#!/usr/bin/env python3
"""Exact regressions for the Poisson filling and K=11 boundary argument.

No simulation or floating-point acceptance criteria. Finite checks do not prove
asymptotic estimates. The monotonicity proof itself is in Appendix E.4.
"""
from __future__ import annotations
import argparse, json
from fractions import Fraction as F
from itertools import product
from math import factorial
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]

def boundary()->dict:
 H={};v=F(0)
 for k in range(1,501):v+=F(1,k);H[k]=v
 ds={k:(H[k]-2)/(k+1) for k in range(2,501)}
 for k in range(2,500):assert ds[k+1]-ds[k]==(3-H[k])/((k+1)*(k+2))
 assert H[10]<3<H[11]
 assert max(ds,key=ds.get)==11
 assert H[11]==F(83711,27720) and ds[11]==F(28271,332640)
 assert ds[11]-F(1,12)==F(551,332640)
 B=1332;K=11
 assert B**3-K**3*B**2-K**3*B==B
 assert F(B,K)**3>B*B+B and F(B**3,K*K)>B*B+B and F(B,K)**2>B
 assert F(K*K*(B*B+B),B*B)<122
 assert 1+F(K,2)<7
 for k in range(2,101):
  b=k**3+1
  assert b**3-k**3*b*b-k**3*b==b
  assert F(b,k)**3>b*b+b and F(b**3,k*k)>b*b+b and F(b,k)**2>b
 return {'harmonic_difference_cases':498,'unique_maximizer_in_displayed_family':11,
 'H11':str(H[11]),'delta11':str(ds[11]),'strict_margin_over_1_12':str(ds[11]-F(1,12)),
 'local_product_threshold':1332,'generic_product_threshold_cases':99,
 'complete_theorem_threshold_claimed':False,'optimality_beyond_this_family_claimed':False}

def pmass(z:tuple[int,...],rates:tuple[F,...])->F:
 r=F(1)
 for k,a in zip(z,rates):r*=a**k/factorial(k)
 return r # common exp(-sum rates) cancels in the tested identity.

def filling()->dict:
 # Compactly supported delta tests ensure summation is exact, not a truncated
 # approximation to an unbounded function under a Poisson law.
 checks=0
 for dim in (1,2,3):
  rateset=[tuple(F(i+j,3) for j in range(dim)) for i in (0,1,3)]
  goodset=[tuple(0 for _ in range(dim)),tuple(1 for _ in range(dim))]
  for rates in rateset:
   for good in goodset:
    for target in product(range(3),repeat=dim):
     for i in range(dim):
      left=right=F(0)
      def g(w):return int(tuple(w)==target)
      def diff(w):
       wp=list(w);wp[i]+=1
       return g(wp)-g(w)
      for z in product(*(range(t+3) for t in target)):
       w=tuple(a+b for a,b in zip(good,z));mass=pmass(z,rates)
       right+=rates[i]*diff(w)*mass
       if z[i]:
        wm=list(w);wm[i]-=1
        left+=z[i]*diff(wm)*mass
      assert left==right
      checks+=1
 normcases=0
 for E in range(12):
  q=[F(1,2**(e+1)) for e in range(E+1)];S=sum(q)
  assert S==1-F(1,2**(E+1)) and F(1,2)<=S<1
  for N in (1,2,7,29):
   for removed in sorted({0,N//2,N}):
    p=F(1,8);lam=N*p
    for qe,qf in product(q,repeat=2):
     # Square both sides to avoid square roots of fractions.
     assert (lam*S)**2*(qe/S)*(qf/S)==lam*lam*qe*qf
     assert (N-removed)*p*qe+removed*p*qe==lam*qe
     normcases+=1
 return {'exact_compact_test_identities':checks,'truncated_target_normalization_cases':normcases,
 'includes_zero_filling':True,'includes_all_sites_deleted':True,
 'poisson_sums_truncated_with_zero_tail_not_approximately':True,
 'scope':'Finite algebraic tests of cancellation and target normalization; not a proof of the approximation bound.'}

def main()->None:
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,default=ROOT/'BOUNDARY_FILLING_DIAGNOSTICS.json');a=p.parse_args()
 r={'revision':'3PREL','status':'PASS','arithmetic':'exact integers and rational fractions','checks':{'boundary_parameter':boundary(),'poisson_filling':filling()},'limits':'Finite regression tests; no asymptotic, interval-numerical or formal certification.'}
 a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
if __name__=='__main__':main()
