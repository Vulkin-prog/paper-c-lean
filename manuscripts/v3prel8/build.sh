#!/usr/bin/env bash
# Rebuild the article and companion, with independent local bibliographies.
set -euo pipefail
cd "$(dirname "$0")"
export TZ=UTC LC_ALL=C.UTF-8 SOURCE_DATE_EPOCH=1789516800 FORCE_SOURCE_DATE=1
for tool in pdflatex biber python3; do
  command -v "$tool" >/dev/null || { echo "Missing dependency: $tool" >&2; exit 1; }
done
mkdir -p build_reports
main=paper_c_version_3PREL8_en
comp=paper_c_version_3PREL8_technical_companion_en
for doc in "$main" "$comp"; do
  rm -f "$doc".{aux,toc,out,log,pdf,fls,fdb_latexmk,bcf,bbl,blg,run.xml}
done
previous=''
for pass in 1 2 3 4 5 6 7; do
  for doc in "$main" "$comp"; do
    if ! pdflatex -interaction=nonstopmode -halt-on-error "$doc.tex" >"build_reports/${doc}_pass${pass}.txt" 2>&1; then
      tail -80 "build_reports/${doc}_pass${pass}.txt" >&2; exit 1
    fi
    if [[ "$pass" == 1 ]]; then
      if ! biber --validate-datamodel "$doc" >"build_reports/${doc}_biber.txt" 2>&1; then
        tail -80 "build_reports/${doc}_biber.txt" >&2; exit 1
      fi
    fi
  done
  current=$(python3 - "$main.aux" "$comp.aux" "$main.toc" "$comp.toc" <<'PY'
import hashlib,sys
from pathlib import Path
h=hashlib.sha256()
for name in sys.argv[1:]:h.update(Path(name).read_bytes())
print(h.hexdigest())
PY
)
  if [[ "$current" == "$previous" ]]; then break; fi
  previous=$current
  if [[ "$pass" == 7 ]]; then echo 'Cross-references did not stabilize.' >&2; exit 1; fi
done
for doc in "$main" "$comp"; do
  if grep -E 'undefined references|multiply-defined labels|Overfull|Missing character|LaTeX Error|LaTeX Warning|Package .* Warning|WARN -|ERROR -' "$doc.log" "$doc.blg"; then
    echo "Resolve the reported warning(s) before release." >&2; exit 1
  fi
  cp "$doc.log" "build_reports/$doc.log"
  cp "$doc.blg" "build_reports/$doc.blg"
done
printf 'Build complete: %s.pdf and %s.pdf (stable after %s passes)\n' "$main" "$comp" "$pass"
