#!/usr/bin/env python3
"""Exact algebraic tests for multivariate Stein differences.

These check finite identities, not the existence of a Stein solution or an
asymptotic limit theorem. The analytic estimates are cited in companion C.3.
"""
from __future__ import annotations
import argparse,json
from fractions import Fraction as F
from itertools import product
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def main()->None:
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,default=ROOT/'build_reports/STEIN_DIAGNOSTICS.json');a=p.parse_args()
 # The mixed difference of any indicator has absolute value at most two.
 patterns=0
 for h00,h10,h01,h11 in product((0,1),repeat=4):
  assert abs(h11-h10-h01+h00)<=2;patterns+=1
 # Polarization isolates an entry of a symmetric Hessian. Rational weights
 # suffice to verify the identity without using numerical square roots.
 polar=0
 for A,B,C,x,y in product(range(-2,3),repeat=5):
  qplus=A*x*x+2*B*x*y+C*y*y
  qminus=A*x*x-2*B*x*y+C*y*y
  assert qplus-qminus==4*B*x*y;polar+=1
 # The generator/Hessian identity for two rates 1/2 is a polynomial
 # identity in the six required evaluations. Test every basis vector,
 # which proves this finite linear identity exactly.
 basis=0
 for k in range(6):
  g=[F(int(j==k)) for j in range(6)]
  g00,g10,g01,g20,g11,g02=g
  Ae1=(g20-g10+g11-g10)/2+g00-g10
  Ae2=(g11-g01+g02-g01)/2+g00-g01
  mixed=g20+2*g11+g02-4*g10-4*g01+4*g00
  assert mixed==2*(Ae1+Ae2);basis+=1
 # Geometric type renormalization preserves every weighted denominator.
 norms=0
 for E in range(8):
  q=[F(1,2**(e+1)) for e in range(E+1)];S=sum(q)
  for lam in (F(1,8),F(1,2),F(1),F(3),F(20)):
   for qi,qj in product(q,repeat=2):
    assert (lam*S)**2*(qi/S)*(qj/S)==lam**2*qi*qj;norms+=1
 report={'status':'PASS','arithmetic':'integers and exact rational fractions','indicator_patterns':patterns,'polarization_cases':polar,'linear_generator_identity_basis_checks':basis,'geometric_denominator_checks':norms,'scope':'Finite algebraic checks only; no Lean execution and no certification of external premises.'}
 a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
