#!/usr/bin/env python3
"""Generate or check the two local bibliographies from one shared source.

This is an internal consistency check, not an external bibliographic audit.
"""
from __future__ import annotations
import argparse,json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def main()->None:
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--write',action='store_true',help='regenerate bibliography .tex files')
 p.add_argument('--output',type=Path,default=ROOT/'build_reports/BIBLIOGRAPHY_CHECK.json')
 a=p.parse_args();db=json.loads((ROOT/'bibliography/entries.json').read_text())
 errors=[];counts={};used=set()
 for doc,keys in db['document_order'].items():
  if len(keys)!=len(set(keys)):errors.append(f'{doc}: duplicate key')
  missing=set(keys)-set(db['entries'])
  if missing:raise ValueError(f'{doc}: missing entries {missing}')
  tex='\\begin{thebibliography}{99}\n\n'+'\n\n'.join('\\bibitem{'+k+'}\n'+db['entries'][k]['tex'] for k in keys)+'\n\n\\end{thebibliography}\n'
  f=ROOT/f'bibliography_{doc}.tex'
  if a.write:f.write_text(tex)
  elif not f.exists() or f.read_text()!=tex:errors.append(f'{f.name}: does not match entries.json')
  counts[doc]=len(keys);used.update(keys)
 if used!=set(db['entries']):errors.append('Unused master entries')
 report={'status':'FAIL' if errors else 'PASS','document_entries':counts,'distinct_entries':len(used), 'external_source_verification':False,'errors':errors}
 a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
 if errors:raise SystemExit(1)
if __name__=='__main__':main()
