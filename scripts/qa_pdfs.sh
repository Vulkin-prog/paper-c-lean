#!/usr/bin/env bash
set -Eeuo pipefail

ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
OUT=${1:-"$ROOT/ci-logs/pdf-qa"}
mkdir -p "$OUT"

pdfs=(paper_C_complete_v09_en.pdf paper_C_complete_v09.pdf)
report="$OUT/report.md"
printf '# PDF QA report\n\n' > "$report"
printf '| PDF | Pages | Bytes | SHA-256 |\n|---|---:|---:|---|\n' >> "$report"

for name in "${pdfs[@]}"; do
  pdf="$ROOT/$name"
  test -f "$pdf"
  qpdf --check "$pdf" > "$OUT/$name.qpdf.txt" 2>&1
  pdfinfo "$pdf" > "$OUT/$name.pdfinfo.txt"
  pdffonts "$pdf" > "$OUT/$name.fonts.txt"
  pdftotext "$pdf" "$OUT/$name.txt"
  if pdfinfo -url "$pdf" > "$OUT/$name.urls.txt" 2>&1; then :; else
    printf 'pdfinfo -url unsupported or returned no URL inventory\n' > "$OUT/$name.urls.txt"
  fi

  awk 'NR > 2 && $(NF-4) != "yes" { print; bad=1 } END { exit bad }' \
    "$OUT/$name.fonts.txt"
  if grep -F 'Type 3' "$OUT/$name.fonts.txt"; then
    echo "Type 3 font detected in $name" >&2
    exit 1
  fi
  if grep -Eaiq '(/home/|/Users/|[A-Z]:\\\\|localhost|127\\.0\\.0\\.1|private-user-images|githubusercontent\.com/user-attachments)' \
      "$OUT/$name.txt" "$OUT/$name.pdfinfo.txt" "$OUT/$name.urls.txt"; then
    echo "Private or local path/URI detected in $name" >&2
    exit 1
  fi

  pages=$(awk -F: '/^Pages:/ {gsub(/^[[:space:]]+/, "", $2); print $2}' "$OUT/$name.pdfinfo.txt")
  bytes=$(stat -c '%s' "$pdf")
  sha=$(sha256sum "$pdf" | awk '{print $1}')
  printf '| `%s` | %s | %s | `%s` |\n' "$name" "$pages" "$bytes" "$sha" >> "$report"
done

cat >> "$report" <<'EOF'

Checks performed:

- `qpdf --check`;
- complete font inventory, all fonts embedded, no Type 3 fonts;
- PDF metadata and URL extraction when supported by Poppler;
- text extraction and scan for local/private paths and attachment URLs.
EOF
