#!/usr/bin/env bash
set -Eeuo pipefail

ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
OUT=${1:-"$ROOT/ci-logs/pdf-qa"}
mkdir -p "$OUT"

for command in pdfinfo pdffonts pdftotext awk grep stat sha256sum mktemp rm; do
  command -v "$command" >/dev/null 2>&1 || {
    echo "Required PDF QA command is unavailable: $command" >&2
    exit 1
  }
done

if command -v qpdf >/dev/null 2>&1; then
  structure_checker=qpdf
  structure_description='qpdf --check'
elif command -v mutool >/dev/null 2>&1; then
  structure_checker=mutool
  structure_description='mutool info + mutool clean -gggg'
else
  echo "PDF structural QA requires qpdf or the mutool fallback" >&2
  exit 1
fi

scratch=$(mktemp -d "${TMPDIR:-/tmp}/paper-c-lean-pdf-qa.XXXXXX")
trap 'rm -rf -- "$scratch"' EXIT

pdfs=(paper_C_complete_v09_en.pdf paper_C_complete_v09.pdf)
report="$OUT/report.md"
printf '# PDF QA report\n\n' > "$report"
printf '| PDF | Pages | Bytes | SHA-256 |\n|---|---:|---:|---|\n' >> "$report"

private_pattern='(/home/|/Users/|/tmp/|/private/var/|[A-Za-z]:\\|file:(//)?|localhost|127\.0\.0\.1|private-user-images|githubusercontent\.com/user-attachments)'

for name in "${pdfs[@]}"; do
  pdf="$ROOT/$name"
  test -s "$pdf" || {
    echo "Missing or empty PDF: $name" >&2
    exit 1
  }

  structure_log="$OUT/$name.$structure_checker.txt"
  if [[ "$structure_checker" == qpdf ]]; then
    qpdf --check "$pdf" > "$structure_log" 2>&1 || {
      echo "qpdf structural check failed for $name" >&2
      exit 1
    }
  else
    checked_pdf="$scratch/$name"
    mutool info "$pdf" > "$structure_log" 2>&1 || {
      echo "mutool info structural check failed for $name" >&2
      exit 1
    }
    mutool clean -gggg "$pdf" "$checked_pdf" >> "$structure_log" 2>&1 || {
      echo "mutool clean structural check failed for $name" >&2
      exit 1
    }
    test -s "$checked_pdf" || {
      echo "mutool clean produced no checked PDF for $name" >&2
      exit 1
    }
  fi

  pdfinfo "$pdf" > "$OUT/$name.pdfinfo.txt"
  pdffonts "$pdf" > "$OUT/$name.fonts.txt"
  pdftotext "$pdf" "$OUT/$name.txt"
  for inventory in url meta custom dests; do
    pdfinfo "-$inventory" "$pdf" > "$OUT/$name.$inventory.txt" 2>&1 || {
      echo "pdfinfo -$inventory failed for $name" >&2
      exit 1
    }
  done

  awk '
    NR > 2 && NF > 0 {
      fonts++
      if ($(NF-4) != "yes") {
        print "Font is not embedded: " $0 > "/dev/stderr"
        bad = 1
      }
      if ($(NF-3) != "yes") {
        print "Font is not subset: " $0 > "/dev/stderr"
        bad = 1
      }
      if ($2 == "Type" && $3 == "3") {
        print "Type 3 font detected: " $0 > "/dev/stderr"
        bad = 1
      }
    }
    END {
      if (fonts == 0) {
        print "No font inventory rows found" > "/dev/stderr"
        bad = 1
      }
      exit bad
    }
  ' "$OUT/$name.fonts.txt" || {
    echo "Font QA failed for $name" >&2
    exit 1
  }

  if grep -Eaiq -- "$private_pattern" \
      "$OUT/$name.txt" \
      "$OUT/$name.pdfinfo.txt" \
      "$OUT/$name.url.txt" \
      "$OUT/$name.meta.txt" \
      "$OUT/$name.custom.txt" \
      "$OUT/$name.dests.txt"; then
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

EOF
printf -- '- structural integrity with `%s` (fail-closed selection: `qpdf` then `mutool`);\n' \
  "$structure_description" >> "$report"
cat >> "$report" <<'EOF'

- complete font inventory, every font embedded and subset, no Type 3 fonts;
- mandatory PDF URL, metadata, custom-metadata and named-destination inventories;
- text extraction and scan of text plus all PDF inventories for local/private
  paths and attachment URLs.
EOF
