#!/usr/bin/env python3
"""Exact finite regression tests for the capped profiles and relative normalization.

These tests exercise identities/inequalities on explicit finite domains.
They do not prove an asymptotic estimate or validate an external theorem.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]

def main() -> None:
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,default=ROOT/'PROFILE_DIAGNOSTICS.json')
    a=ap.parse_args(); counts={}
    total=0;endpoint=0
    for B in range(3,513):
        js=range((B-2)//3+1)
        ks=[B-3*j-1 for j in js]
        assert len(set(ks))==len(ks)
        weight=sum((F(B*B,k*(k-1)) for k in ks if k>=2),F(0))
        assert weight<=B*B
        exceptional=[k for k in ks if k<=1]
        assert len(exceptional)<=1
        assert bool(exceptional)==(B%3==2)
        endpoint+=bool(exceptional);total+=len(ks)
    counts['terminal_strata']={'window_lengths':510,'strata':total,'endpoint_cases':endpoint,'largest_B':512}
    c=0
    for T in [F(1),F(3,2),F(2),F(9),F(100),F(100000)]:
        for E in [F(1),F(5,4),F(2),F(9)]:
            for Q in [F(2),F(8),F(1024),F(99999)]:
                assert min(T,E*Q)<=E*min(T,Q);c+=1
        for rho in range(18):
            for extra in range(3):
                full=rho+extra
                assert min(T,2**full-1)<=4*min(T,2**rho-1)+3*(full>0);c+=1
    counts['cap_inequalities']={'cases':c}
    # Vectors of exponents in N, Lambda, m. Q=N*m/Lambda, a=Lambda/N.
    def add(*vs):return tuple(sum(v[i] for v in vs) for i in range(3))
    def scale(c,v):return tuple(c*x for x in v)
    av=(F(-1),F(1),F(0));qv=(F(1),F(-1),F(1));tv=(F(1),F(-1),F(0))
    identities=[
      (add(scale(2,av),(F(3,2),F(0),F(0)),scale(F(1,6),qv)),(F(-1,3),F(11,6),F(1,6))),
      (add(scale(2,av),(F(1),F(0),F(0)),scale(F(2,3),qv)),(F(-1,3),F(4,3),F(2,3))),
      (add(scale(2,av),(F(2,3),F(0),F(0)),tv),(F(-1,3),F(1),F(0))),
    ]
    assert all(lhs==rhs for lhs,rhs in identities)
    critical=0
    for den in range(3,80):
        for num in range(1,(den-1)//2+1):
            eta=F(num,den);eps=eta/6
            assert F(-1,3)+eps+(F(1,2)-eta)/6==F(-1,4)
            assert F(-1,3)+eps+(F(1,2)-eta)*F(2,3)==-eta/2
            assert F(-1,3)+eps<=-eta/2
            critical+=1
    admissible=0
    for N in [1,2,10,101,10000]:
        for B in range(1,17):
            for m in sorted({1,2**B,max(1,2**B//3),max(1,2**B//2)}):
                rate=F(m,2**B);Lambda=N*rate;T=1/rate;Q=F(2**B)
                assert 0<rate<=1 and 1<=T<=Q and Q==N*m/Lambda
                # Cube of the secondary-edge absorption avoids fractional powers.
                assert (Lambda**2/N)**3 <= Lambda**4*m*m/N
                admissible+=1
    counts['dictionary_normalization']={'monomial_identities':3,'critical_margin_cases':critical,'admissible_parameter_cases':admissible}
    shiftcases=0
    for k in range(3,90):
        for m in [k*k+1,k*k+2,10*k*k]:
            z=m+1
            for ds in [(1,k),(1,(k+1)//2,k),tuple(range(1,k+1))]:
                ds=tuple(sorted(set(ds)));dp=tuple(d-1 for d in ds)
                assert all(0<=d<k for d in dp)
                assert tuple(m+d for d in ds)==tuple(z+d for d in dp)
                shiftcases+=1
    counts['postquadratic_translation']={'cases':shiftcases,'scope':'Offset and integer-height substitution only; does not check the literature exclusion.'}
    # Exact geometric truncation and right-censoring tails of the target.
    censor=0
    for n in range(1,200):
        t=sum((F(1,2**j) for j in range(1,n+1)),F(0))/n
        assert t==F(1, n)*(1-F(1,2**n)) and t<=F(1,n);censor+=1
    counts['target_censoring']={'grid_sizes':censor}
    result={'revision':'3PREL','status':'PASS','arithmetic':'exact integers and fractions','scope':'Finite algebraic regressions only. No asymptotic proof, independent peer review or Lean certification.','checks':counts}
    a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
