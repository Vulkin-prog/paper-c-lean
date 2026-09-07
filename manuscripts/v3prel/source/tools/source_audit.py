#!/usr/bin/env python3
"""Audit local source references, statement inventory and final TeX logs.

This is a structural QA tool, not a mathematical proof checker.
"""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

ROOT=Path(__file__).resolve().parents[1]
STATEMENTS='theorem|lemma|proposition|corollary|definition|remark|convention|claim|hypothesis'

def walk(name: str, seen: set[str] | None = None) -> list[Path]:
    seen=set() if seen is None else seen
    f=ROOT/name
    if not f.suffix:f=f.with_suffix('.tex')
    rel=str(f.relative_to(ROOT))
    if rel in seen:return []
    seen.add(rel)
    if not f.exists():raise FileNotFoundError(f)
    out=[f]
    for child in re.findall(r'\\input\{([^}]+)\}',f.read_text()):out.extend(walk(child,seen))
    return out


def main() -> None:
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,default=ROOT/'SOURCE_AUDIT.json');a=p.parse_args()
    docs={'main':'paper_C_version_3PREL_en','companion':'paper_C_version_3PREL_technical_companion_en'}
    texfiles=sorted(set(f for base in docs.values() for f in walk(base+'.tex')))
    alltext='\n'.join(f.read_text() for f in texfiles)
    labels=re.findall(r'\\label\{([^}]+)\}',alltext)
    duplicates={k:v for k,v in Counter(labels).items() if v>1}
    refs={k.strip() for m in re.finditer(r'\\(?:[cC]?ref|eqref|pageref|suppref)\*?\{([^}]+)\}',alltext) for k in m[1].split(',') if not k.startswith('#')}
    undefined=sorted(refs-set(labels))
    mismatches=[]
    for f in texfiles:
        stack=[]
        for m in re.finditer(r'\\(begin|end)\{([^}]+)\}',f.read_text()):
            kind,env=m.groups()
            if kind=='begin':stack.append(env)
            elif stack and stack[-1]==env:stack.pop()
            else:mismatches.append([str(f.relative_to(ROOT)),env,'closing mismatch'])
        if stack:mismatches.append([str(f.relative_to(ROOT)),stack,'unclosed'])
    inventories={};citeissues={};logissues={}
    for doc,base in docs.items():
        files=walk(base+'.tex')
        text='\n'.join(f.read_text() for f in files)
        bibs=set(re.findall(r'\\bibitem\{([^}]+)\}',text))
        cites={k.strip() for m in re.finditer(r'\\cite(?:\[[^\]]*\]){0,2}\{([^}]+)\}',text) for k in m[1].split(',')}
        citeissues[doc]=dict(undefined=sorted(cites-bibs),uncited=sorted(bibs-cites))
        aux=(ROOT/(base+'.aux')).read_text() if (ROOT/(base+'.aux')).exists() else ''
        nums={m[1]:(m[2],m[3]) for m in re.finditer(r'\\newlabel\{([^}]+)\}\{\{([^{}]*)\}\{([^{}]*)\}',aux)}
        inv=[]
        for f in files:
            s=f.read_text()
            for m in re.finditer(r'\\begin\{('+STATEMENTS+r')\}(?:\[([^\]]*)\])?(.*?)\\end\{\1\}',s,re.S):
                labs=re.findall(r'\\label\{([^}]+)\}',m[3])
                label=labs[0] if labs else None
                number,page=nums.get(label,('', ''))
                inv.append(dict(environment=m[1],title=m[2] or '',label=label,number=number,page=page,
                                source=str(f.relative_to(ROOT)),line=s[:m.start()].count('\n')+1,
                                statement_sha256=hashlib.sha256(m[0].encode()).hexdigest()))
        try:
            import fitz
        except ImportError:
            for item in inv:
                item['page_source'] = 'LaTeX auxiliary only; printed heading not inspected'
        else:
            with fitz.open(ROOT/(base+'.pdf')) as pdf:
                page_texts = [page.get_text() for page in pdf]
            for item in inv:
                pattern = (r'(?m)^' + item['environment'].capitalize() + r'\s+'
                           + re.escape(item['number']) + r'\s*\(')
                hits = [i+1 for i,t in enumerate(page_texts) if re.search(pattern,t)]
                if len(hits) != 1:
                    raise ValueError(f"Nonunique PDF statement heading: {item['label']}: {hits}")
                item['auxiliary_page'] = item['page']
                item['page'] = str(hits[0])
                item['page_source'] = 'printed PDF heading (PyMuPDF text, no OCR)'
        inventories[doc]=inv
        (ROOT/f'STATEMENT_INVENTORY_{doc.upper()}.json').write_text(json.dumps(dict(document=doc,revision='3PREL',statements=inv),indent=2)+'\n')
        log=(ROOT/(base+'.log')).read_text(errors='replace') if (ROOT/(base+'.log')).exists() else 'LOG MISSING'
        logissues[doc]=[line for line in log.splitlines() if any(k in line for k in ['Warning','Overfull','Underfull','Missing character','LaTeX Error','LOG MISSING'])]
    wrong_names=bool(re.search(r'GPT 5\.6|GPT-5\.6(?! Sol)|GPT-6 Pro',alltext))
    required_names=all(x in (ROOT/'declarations.tex').read_text() for x in ['GPT-5.6 Sol','GPT-6 Astra'])
    malformed_notation='m odd}' in alltext or 'm squarefree}' in alltext or '\r' in alltext
    public_history_clean=not any(t in alltext for t in ['migration note','detached verification','working version','working draft','revision log','recorded valuation correction','Version 2.8','Version 2.9 incorporates'])
    passed=(public_history_clean and not duplicates and not undefined and not mismatches and
            not any(x['undefined'] or x['uncited'] for x in citeissues.values()) and
            not any(logissues.values()) and not wrong_names and required_names and not malformed_notation)
    report=dict(revision='3PREL',status='PASS' if passed else 'FAIL',scope='Structural checks only; no mathematical certification.',
                tex_files=len(texfiles),labels=len(labels),duplicate_labels=duplicates,undefined_references=undefined,
                environment_issues=mismatches,citation_issues=citeissues,log_issues=logissues,
                ai_names_exact=required_names and not wrong_names,malformed_notation=malformed_notation,
                public_manuscript_scope_clean=public_history_clean,
                statement_counts={k:len(v) for k,v in inventories.items()})
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
    if not passed:raise SystemExit(1)

if __name__=='__main__':main()
