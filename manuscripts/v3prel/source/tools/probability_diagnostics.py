#!/usr/bin/env python3
"""Exact finite tests of valuations, dictionary overlaps, and Poisson probabilities.

Uses Python's integers and rational numbers, without simulation. These tests
check identities and failure modes, not uniform asymptotics or Lean proofs.
"""
from __future__ import annotations
import argparse, json
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
from math import comb
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]

def valuation_counterexample() -> dict:
    rows=[]; assignments=0
    for s2,s3 in product((-1,1),repeat=2):
        counts=Counter()
        for s5,s13 in product((-1,1),repeat=2):
            counts[(s5*s5,s2*s13)]+=1;assignments+=1
        for w in product((-1,1),repeat=2):
            prob=F(counts[w],4)
            assert prob==(F(1,2) if w[0]==1 else 0)
        rows.append({'f2':s2,'f3':s3,'negative_first_probability':'0','positive_word_probability':'1/2'})
    assert 25==5**2 and 26==2*13 and 5>3 and 13>3
    return {'B':2,'Y':3,'x':26,'vertices':[25,26],'assignments':assignments,'small_prime_atoms':rows,
            'conclusion':'The literal odd-prime-divisor condition fails; valuation parity is essential.'}

def dictionary_overlap() -> dict:
    pair_tests=0; shift_counts=[]; mean_checks=0; exhaustive=0
    for B in range(1,9):
        words=list(product((0,1),repeat=B));Q=len(words)
        weights=[[F(0) for _ in words] for _ in words] if B<=4 else None
        for d in range(1,B):
            total=diagonal=0
            for i,w in enumerate(words):
                for j,v in enumerate(words):
                    ok=w[d:]==v[:B-d]; pair_tests+=1
                    if ok:
                        total+=1;diagonal+=i==j
                        if weights is not None:weights[i][j]+=F(1,2**d)
            assert diagonal==2**d and total==2**(B+d)
            distinct=total-diagonal
            assert distinct==2**d*(Q-1)
            for m in range(1,Q+1):
                expectation=(diagonal*F(m,Q)+distinct*F(m*(m-1),Q*(Q-1)))/ (m*2**d)
                assert expectation==F(m,Q);mean_checks+=1
            shift_counts.append({'B':B,'d':d,'total':total,'diagonal':diagonal,'distinct':distinct})
        if weights is not None:
            for m in range(1,(Q if B<=3 else 4)+1):
                total=F(0);count=0
                for W in combinations(range(Q),m):
                    total+=sum((weights[i][j] for i in W for j in W),F(0))/m
                    count+=1;exhaustive+=1
                assert count==comb(Q,m)
                assert total/count==F(m*(B-1),Q)
    return {'directed_pair_tests':pair_tests,'shift_inclusion_mean_checks':mean_checks,
            'exhaustive_without_replacement_dictionaries':exhaustive,
            'formula':'E Omega = m(B-1)/2^B','shift_counts':shift_counts}

def masked_deletion() -> dict:
    tested=0;p=F(1,16)
    for defects in product(range(4),repeat=4):
        for membership in product(range(3),repeat=4): # outside, retained, deleted
            A=[i for i in range(4) if membership[i]];D=[i for i in A if membership[i]==2]
            mb=sum(2**defects[i]-1 for i in A)
            actual_upper=sum((min(F(1),p*2**defects[i]) for i in D),F(0))
            target=p*len(D)
            assert actual_upper+target<=p*(mb+2*len(D))
            assert p*len(A)-p*(len(A)-len(D))==target
            tested+=1
    return {'arbitrary_mask_and_defect_cases':tested,'empty_masks_included':True,
            'scope':'Algebraic deletion and own-mask intensity identities under the pointwise probability bound.'}

def terminal_caps() -> dict:
    weights=0;caps=0;complement=0
    for B in range(3,257):
        QB=2**B;TB=(B-2)//3
        for j in range(TB+1):
            m=B-3*j-1;assert m>=1
            for D in range(3):
                tau=B+D-j;w=2**tau-1;weights+=1
                if m>=2:
                    assert w<=4*QB
                    for T in (F(0),F(1,3),F(QB,100),F(QB),F(3*QB),F(10*QB)):
                        assert min(T,w)<=4*min(T,QB);caps+=1
                else:
                    assert 3*tau<=2*B+8
                    assert (2**tau)**3<=512*QB**2
                    complement+=1
    return {'terminal_index_weight_cases':weights,'common_nonnegative_cap_cases':caps,
            'one_kernel_complement_cases':complement,
            'scope':'Two-population pointwise inequalities only; energy and partner asymptotics are not tested.'}

def soft_factors() -> dict:
    factor_cases=0;exponential_cases=0
    for k in range(-20,21):
        lam=F(4)**k;sqrtlam=F(2)**k;K=max(F(1),lam)
        a=min(F(1),1/lam);b=min(F(1),1/sqrtlam)
        assert a*lam**2<=K and a*(lam**2+lam)<=2*K
        assert b*lam<=max(F(1),sqrtlam)
        factor_cases+=1
    # Set w-ell=2a log 2 and the nonnegative remainder=b log 2.
    for a in range(41):
        for b in range(a+1):
            q=F(2)**(-a+b);r=F(2)**(-2*a+b)
            assert q<=1 and r<=q and q+r<=2*q
            exponential_cases+=1
    return {'intensities_on_both_sides_of_one':factor_cases,'common_remainder_exponential_cases':exponential_cases,
            'scope':'Exact Stein-factor algebra, not an asymptotic cutoff calculation.'}

def stirling_steps() -> dict:
    tested=0
    for n in range(1,501):
        t=F(1,2*n+1);upper=t*t/(3*(1-t*t))
        assert upper==F(1,12*n*(n+1))
        for jmax in (1,2,5,10):
            partial=sum((t**(2*j)/(2*j+1) for j in range(1,jmax+1)),F(0))
            tail_upper=t**(2*jmax+2)/((2*jmax+3)*(1-t*t))
            assert 0<=partial<=partial+tail_upper<=upper
            tested+=1
        for end in (n,n+1,n+5):
            assert sum((F(1,12*k*(k+1)) for k in range(n,end+1)),F(0))==F(1,12*n)-F(1,12*(end+1))
    return {'rational_log_series_step_bounds':tested,'telescoping_identities':1500,
            'scope':'Exact finite bounds for the elementary proof; Stirling limit and infinite telescoping are in the written argument.'}

def sparse_weights() -> dict:
    tested=0
    alphas=[F(a,2**k) for k in range(1,8) for a in (0,1,2**(k-1),2**k)]
    bs=[F(b,2**k) for k in range(0,9) for b in (0,1,3,7)]
    for alpha in alphas:
        for b in bs:
            denom=alpha+(1-alpha)*b
            if denom==0 or alpha+b==0:continue
            exact=alpha/denom;candidate=alpha/(alpha+b)
            difference=alpha**2*b/((alpha+b)*denom)
            assert exact-candidate==difference and 0<=difference<=b
            assert exact+(1-alpha)*b/denom==1
            tested+=1
    # Geometric marked clock: exact tails via finite partial sum plus remainder.
    for K in range(21):
        partial=sum((F(1,2**(j+1)) for j in range(K+1)),F(0))
        assert 1-partial==F(1,2**(K+1))
    return {'moving_source_weight_cases':tested,'geometric_tail_cases':21,
            'scope':'The common exp(-b) cancels in the exact one-hit weights. No lower bound on either weight.'}

def overflow_masks() -> dict:
    tested=0
    for M in range(5,301):
        for L in range(2,M+1):
            excluded=list(range(M-L+2,M))
            assert len(excluded)<=L
            if M-L+2>=2*L*L:
                assert all(x>=2*L*L for x in excluded)
                tested+=1
    return {'deep_rightmost_mask_cases':tested,
            'scope':'Index and cardinality check; the probability bound uses the global deep-start theorem.'}

def main() -> None:
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,default=ROOT/'PROBABILITY_DIAGNOSTICS.json');args=ap.parse_args()
    report={'revision':'3PREL','status':'PASS','arithmetic':'exact Python integers and fractions; no sampling',
            'scope':'Finite regressions only, not proof of asymptotic estimates or local Lean compilation.',
            'valuation_pivots':valuation_counterexample(),'dictionary_overlap':dictionary_overlap(),'masked_deletion':masked_deletion(),
            'terminal_caps':terminal_caps(),'soft_factors':soft_factors(),'stirling_steps':stirling_steps(),
            'sparse_weights':sparse_weights(),'overflow_masks':overflow_masks()}
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v if not isinstance(v,dict) else {a:b for a,b in v.items() if not isinstance(b,list)} for k,v in report.items()},indent=2))
if __name__=='__main__':main()
