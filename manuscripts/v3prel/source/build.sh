#!/usr/bin/env bash
# Rebuild both cross-referencing documents from a clean source checkout.
set -euo pipefail
cd "$(dirname "$0")"
export TZ=UTC LC_ALL=C.UTF-8
# Fixed release date; makes PDF dates independent of the local build clock.
export SOURCE_DATE_EPOCH=1788739200 FORCE_SOURCE_DATE=1
for tool in pdflatex python3; do
  command -v "$tool" >/dev/null || { echo "Missing dependency: $tool" >&2; exit 1; }
done
mkdir -p build_reports
python3 tools/bibliography.py --output build_reports/BIBLIOGRAPHY_CHECK.json > build_reports/bibliography_check.txt
main=paper_C_version_3PREL_en
comp=paper_C_version_3PREL_technical_companion_en
# Remove only generated files for this pair. Never reuse a stale cross-document .aux.
for doc in "$main" "$comp"; do
  rm -f "$doc.aux" "$doc.toc" "$doc.out" "$doc.log" "$doc.pdf" "$doc.fls" "$doc.fdb_latexmk"
done
previous=''
for pass in 1 2 3 4 5 6; do
  for doc in "$main" "$comp"; do
    if ! pdflatex -interaction=nonstopmode -halt-on-error "$doc.tex" >"build_reports/${doc}_pass${pass}.txt" 2>&1; then
      tail -70 "build_reports/${doc}_pass${pass}.txt" >&2
      exit 1
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
  if [[ "$pass" == 6 ]]; then echo 'Cross-references did not stabilize.' >&2; exit 1; fi
done
for doc in "$main" "$comp"; do
  if grep -E 'undefined references|multiply-defined labels|Overfull|Missing character|LaTeX Error|LaTeX Warning|Package .* Warning' "$doc.log"; then
    echo "Resolve the reported warning(s) in $doc.log before release." >&2
    exit 1
  fi
  cp "$doc.log" "build_reports/$doc.log"
done
python3 tools/finite_diagnostics.py --output build_reports/FINITE_DIAGNOSTICS.json > build_reports/finite_diagnostics.txt
python3 tools/profile_diagnostics.py --output build_reports/PROFILE_DIAGNOSTICS.json > build_reports/profile_diagnostics.txt
python3 tools/boundary_filling_diagnostics.py --output build_reports/BOUNDARY_FILLING_DIAGNOSTICS.json > build_reports/boundary_filling_diagnostics.txt
python3 tools/probability_diagnostics.py --output build_reports/PROBABILITY_DIAGNOSTICS.json > build_reports/probability_diagnostics.txt
python3 tools/source_audit.py --output build_reports/SOURCE_AUDIT.json
python3 tools/stein_diagnostics.py --output build_reports/STEIN_DIAGNOSTICS.json > build_reports/stein_diagnostics.txt
if python3 -c 'import fitz' >/dev/null 2>&1; then
  python3 tools/pdf_audit.py --output build_reports/PDF_QA.json > build_reports/pdf_audit.txt
else
  echo 'Optional PDF preflight skipped: PyMuPDF is not installed.'
fi
printf 'Build complete: %s.pdf and %s.pdf\n' "$main" "$comp"
