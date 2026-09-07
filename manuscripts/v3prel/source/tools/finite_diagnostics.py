#!/usr/bin/env python3
"""Exact finite regression checks for Paper C.

These computations are diagnostics, not proofs of the asymptotic theorems.
All equalities and inequalities below use integers or fractions. No external
Python packages are required. Run from any directory; pass --output for JSON.
"""
from __future__ import annotations
import argparse
from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path
import json
import platform
import random
import time


def rank(rows: list[int]) -> int:
    """Rank over F_2, with binary row vectors packed into integers."""
    basis: dict[int, int] = {}
    for row in rows:
        while row:
            pivot = row.bit_length() - 1
            if pivot in basis:
                row ^= basis[pivot]
            else:
                basis[pivot] = row
                break
    return len(basis)


def parity(x: int) -> int:
    return x.bit_count() & 1


def linear_combination(rows: list[int], coeff: int) -> int:
    out = 0
    for i, row in enumerate(rows):
        if (coeff >> i) & 1:
            out ^= row
    return out


def tv(mu: dict, nu: dict) -> F:
    return sum((abs(mu.get(k, F(0)) - nu.get(k, F(0)))
                for k in mu.keys() | nu.keys()), F(0)) / 2


def valuation_parities(n: int) -> set[int]:
    if n < 1:
        raise ValueError("valuation vector requires a positive integer")
    out: set[int] = set()
    p = 2
    while p * p <= n:
        v = 0
        while n % p == 0:
            n //= p
            v ^= 1
        if v:
            out.add(p)
        p += 1
    if n > 1:
        out.add(n)
    return out


def rational_example() -> dict:
    x, y, L = 100, 67, 3
    vals = {n: valuation_parities(n)
            for z in [x, y] for n in range(z-1, z+L)}
    primes = sorted(set().union(*vals.values()))
    index = {p: i for i, p in enumerate(primes)}
    encoded = {n: sum(1 << index[p] for p in v) for n, v in vals.items()}
    def rows(z):
        return [encoded[z-1] ^ encoded[z]] + [encoded[z] ^ encoded[z+i] for i in range(1,L)]
    A, B = rows(x), rows(y)
    count = 0
    for X in range(1 << len(primes)):
        if [parity(a & X) for a in A+B] == [1,0,0,1,0,0]:
            count += 1
    joint = F(count, 1 << len(primes))
    assert rank(A) == rank(B) == 3 and rank(A+B) == 5
    assert joint == F(1, 32)
    assert 99*102*66*68 == 6732**2
    return dict(primes=primes, rows=A+B, ranks=[3,3,5], joint=str(joint),
                square_product=99*102*66*68)


def conditioning(seed: int) -> dict:
    rng=random.Random(seed)
    cases=0
    states=list(product(range(3),range(3)))
    for _ in range(600):
        a=[rng.randint(0,20) for _ in states];b=[rng.randint(0,20) for _ in states]
        if not sum(a) or not sum(b):continue
        mu={z:F(x,sum(a)) for z,x in zip(states,a)}
        nu={z:F(x,sum(b)) for z,x in zip(states,b)}
        for chosen in [(0,),(1,),(0,2)]:
            q=sum((v for (x,y),v in mu.items() if x in chosen),F(0))
            p=sum((v for (x,y),v in nu.items() if x in chosen),F(0))
            if not p or not q:continue
            muc={y:sum((v for (x,z),v in mu.items() if x in chosen and z==y),F(0))/q for y in range(3)}
            nuc={y:sum((v for (x,z),v in nu.items() if x in chosen and z==y),F(0))/p for y in range(3)}
            assert tv(muc,nuc)<=tv(mu,nu)/max(p,q)
            cases+=1
    return dict(cases=cases, sharp_denominator=True, seed=seed)


def pattern_overlaps() -> dict:
    cases=0
    # Fix the first sign to +1 to enumerate global-sign classes once.
    for L in range(1,6):
        for tail in product([0,1],repeat=L):
            a=(0,)+tail
            for d in range(1,L+1):
                eta=a[d]^a[0]
                compatible=all(a[d+j]==(a[j]^eta) for j in range(L-d+1))
                count=0
                for z in product([0,1],repeat=L+d+1):
                    first=all(z[j]==(a[j]^z[0]) for j in range(L+1))
                    second=all(z[d+j]==(a[j]^z[d]) for j in range(L+1))
                    count+=bool(first and second)
                prob=F(count,1<<(L+d+1))
                assert prob==(F(1,1<<(L+d)) if compatible else F(0))
                cases+=1
    return dict(cases=cases, maximum_word_length=6, exact_union_probabilities=True)


def simple_incidence() -> dict:
    cases=0
    for n in range(1,6):
        edges=list(combinations(range(n),2))
        for mask in range(1<<len(edges)):
            edgerows=[(1<<i)|(1<<j) for k,(i,j) in enumerate(edges) if (mask>>k)&1]
            for pins in range(1<<n):
                rows=edgerows+[1<<i for i in range(n) if (pins>>i)&1]
                E=sum(r.bit_count() for r in rows)
                K=max((sum((r>>i)&1 for r in rows) for i in range(n)),default=0)
                assert rank(rows)*(K+1)>=E
                cases+=1
    H11=sum((F(1,j) for j in range(1,12)),F(0))
    delta=(H11-2)/12
    assert delta==F(28271,332640) and delta>F(1,12)
    B=1332
    assert F(B,11)**3>B*B+B and F(B**3,121)>B*B+B and F(B,11)**2>B
    return dict(cases=cases, max_vertices=5, delta=str(delta), displayed_exponent='1/12',
                local_product_threshold=1332, complete_asymptotic_threshold_asserted=False)


def value_relation_profile(seed: int) -> dict:
    rng = random.Random(seed)
    abstract_cases = 0
    arithmetic_cases = 0
    def check(a: list[int], b: list[int]) -> None:
        B = len(a)
        def tree(v: list[int]) -> list[int]:
            return [v[0] ^ v[1]] + [v[1] ^ v[j] for j in range(2, B)]
        rv = 2 * B - rank(a + b)
        rr = 2 * (B - 1) - rank(tree(a) + tree(b))
        assert rr <= rv <= rr + 2
        assert (1 << rv) - 1 <= 4 * ((1 << rr) - 1) + 3 * int(rv > 0)
    for B in range(2, 9):
        for width in range(1, 10):
            for _ in range(24):
                a = [rng.randrange(1 << width) for _ in range(B)]
                b = [rng.randrange(1 << width) for _ in range(B)]
                check(a, b)
                abstract_cases += 1
    for B in range(2, 8):
        for x in range(2, 52):
            y = x + B + rng.randrange(1, 100)
            va = [valuation_parities(n) for n in range(x - 1, x + B - 1)]
            vb = [valuation_parities(n) for n in range(y - 1, y + B - 1)]
            primes = sorted(set().union(*(va + vb)))
            index = {q: j for j, q in enumerate(primes)}
            rows = [sum(1 << index[q] for q in v) for v in va + vb]
            check(rows[:B], rows[B:])
            arithmetic_cases += 1
    return dict(abstract_cases=abstract_cases, arithmetic_cases=arithmetic_cases,
                codimension_at_most_two=True, weighted_host_inequality=True, seed=seed)


def absolute_word_overlaps() -> dict:
    cases = 0
    for B in range(2, 8):
        words = list(product([0, 1], repeat=B))
        for d in range(1, B):
            observed = Counter((z[:B], z[d:]) for z in product([0, 1], repeat=B+d))
            for w in words:
                for v in words:
                    compatible = w[d:] == v[:B-d]
                    assert observed[(w, v)] == int(compatible)
                    cases += 1
    return dict(cases=cases, maximum_word_length=7,
                exact_joint_probability='2^(-(B+d)) for compatible words, zero otherwise')


def generic_dictionaries() -> dict:
    ensembles = 0
    dictionaries = 0
    def overlap(W: tuple[tuple[int, ...], ...], B: int) -> F:
        return sum((F(int(w[d:] == v[:B-d]), 1 << d)
                    for w in W for v in W for d in range(1, B)), F(0)) / len(W)
    for B in range(2, 5):
        words = list(product([0, 1], repeat=B))
        for m in range(1, min(4, len(words))):
            total = F(0)
            count = 0
            for W in combinations(words, m):
                total += overlap(W, B)
                count += 1
            expectation = total / count
            assert expectation <= F(m * (B-1), (1 << B)-1)
            dictionaries += count
            ensembles += 1
        for w in words:
            neg = tuple(1 - z for z in w)
            theta = F(0)
            for d in range(1, B):
                eta = w[d] ^ w[0]
                if all(w[d+j] == (w[j] ^ eta) for j in range(B-d)):
                    theta += F(1, 1 << d)
            assert overlap((w, neg), B) == theta
    return dict(ensembles=ensembles, dictionaries=dictionaries,
                expectation_bound=True, sign_class_overlap_identity=True)


def signed_local_runs() -> dict:
    cases = 0
    exhaustive_cases = 0
    for a in range(1, 6):
        for b in range(1, 6):
            for d in range(1, a+4):
                for s, t in product([0, 1], repeat=2):
                    wa = (1-s,) + (s,)*a + (1-s,)
                    wb = (1-t,) + (t,)*b + (1-t,)
                    prescribed = dict(enumerate(wa))
                    compatible = True
                    for j, z in enumerate(wb, d):
                        if j in prescribed and prescribed[j] != z:
                            compatible = False
                        prescribed[j] = z
                    actual = F(1, 1 << len(prescribed)) if compatible else F(0)
                    prodp = F(1, 1 << (a+b+4))
                    if d < a:
                        expected = F(0)
                    elif d == a:
                        expected = 4*prodp if t != s else F(0)
                    elif d == a+1:
                        expected = 2*prodp if t == s else F(0)
                    else:
                        expected = prodp
                    assert actual == expected
                    assert actual <= 4*prodp
                    if a <= 3 and b <= 3:
                        length = max(a+2, d+b+2)
                        hit = sum(z[:a+2] == wa and z[d:d+b+2] == wb
                                  for z in product([0, 1], repeat=length))
                        assert actual == F(hit, 1 << length)
                        exhaustive_cases += 1
                    cases += 1
    # The right-censoring probability for a uniform site is at most 1/H.
    for H in range(1, 50):
        assert sum((F(1, 1 << j) for j in range(1, H+1)), F(0)) / H <= F(1, H)
    return dict(cases=cases, exhaustive_cases=exhaustive_cases,
                compatible_overlap_factors=[4, 2, 1], censoring_geometric_sum=True)



def capped_relations(seed: int) -> dict:
    scalar_cases = 0
    for rr in range(24):
        for gap in range(3):
            rv = rr + gap
            for T in [F(1),F(3,2),F(2),F(7),F(31),F(1024),F(2**28)]:
                assert min(T, 2**rv-1) <= 4*min(T, 2**rr-1)+3*int(rv>0)
                scalar_cases += 1
    rng = random.Random(seed)
    dictionary_cases = 0
    for B in range(1,6):
        for width in range(B,B+4):
            for _ in range(12):
                def full_rank_rows() -> list[int]:
                    for trial in range(10000):
                        A = [rng.randrange(1<<width) for _ in range(B)]
                        if rank(A)==B:return A
                    raise RuntimeError('full-rank sampling failed')
                A,C=full_rank_rows(),full_rank_rows()
                rv=2*B-rank(A+C)
                values=[]
                for x in range(1<<width):
                    values.append((sum(parity(r&x)<<j for j,r in enumerate(A)),
                                   sum(parity(r&x)<<j for j,r in enumerate(C))))
                for m in sorted({1, min(2,1<<B), max(1,(1<<B)//2), 1<<B}):
                    W=set(rng.sample(range(1<<B),m)); a=F(m,1<<B)
                    joint=F(sum(u in W and v in W for u,v in values),1<<width)
                    assert joint<=min(a,a*a*(1<<rv))
                    assert joint<=a*a*(1+min(1/a,(1<<rv)-1))
                    dictionary_cases+=1
    # Each exponent vector is (N, Lambda, m), before/after substitution Q=Nm/Lambda.
    raw = [(F(3,2),F(1,6)),(F(1),F(2,3)),(F(2,3),None)]
    expected=[(F(-1,3),F(11,6),F(1,6)),
              (F(-1,3),F(4,3),F(2,3)),(F(-1,3),F(1),F(0))]
    for (n,q),want in zip(raw,expected):
        got=(n-2+q,2-q,q) if q is not None else (n-1,F(1),F(0))
        assert got==want
    return dict(pointwise_cases=scalar_cases, dictionary_cases=dictionary_cases,
                exact_exponent_identities=3,seed=seed)


def marker_dictionaries() -> dict:
    families=[]
    total_words=0
    for B in range(8,19):
        k=(2*B-1).bit_length()
        words=[]
        for u in product([0,1],repeat=B-k-2):
            if not any(all(z==0 for z in u[i:i+k]) for i in range(len(u)-k+1)):
                words.append((0,)*k+(1,)+u+(1,))
        assert len(words)>=F(1<<B,32*B)
        for length in range(1,B):
            prefixes={w[:length] for w in words}
            suffixes={w[-length:] for w in words}
            assert prefixes.isdisjoint(suffixes)
        total_words+=len(words)
        families.append(dict(B=B,k=k,words=len(words)))
    return dict(families=families,words=total_words,all_cross_overlaps_absent=True)


def split_square_localization() -> dict:
    cases=0
    equal_class_cases=0
    distinct_class_cases=0
    for degree in range(2,5):
        for offsets in combinations(range(7),degree):
            delta=1
            for h,k in combinations(offsets,2):delta*=abs(h-k)
            delta_primes=set()
            n=delta; p=2
            while p*p<=n:
                if n%p==0:
                    delta_primes.add(p)
                    while n%p==0:n//=p
                p+=1
            if n>1:delta_primes.add(n)
            for x in range(1,201):
                parts=[valuation_parities(x+h) for h in offsets]
                ecoords=set()
                for coords in parts:ecoords.symmetric_difference_update(coords)
                S=delta_primes|ecoords
                assert all(coords<=S for coords in parts)
                def number(coords:set[int]) -> int:
                    n=1
                    for p in coords:n*=p
                    return n
                s,t=number(parts[0]),number(parts[1])
                from math import isqrt
                u=isqrt((x+offsets[0])//s);v=isqrt((x+offsets[1])//t)
                assert s*u*u-t*v*v==offsets[0]-offsets[1]
                if s==t:
                    assert (offsets[0]-offsets[1])%s==0
                    assert (u-v)*(u+v)==(offsets[0]-offsets[1])//s
                    equal_class_cases+=1
                else:
                    assert parts[0]!=parts[1]
                    distinct_class_cases+=1
                cases+=1
    return dict(cases=cases,equal_class_cases=equal_class_cases,
                distinct_class_cases=distinct_class_cases,
                scope='Checks square-class localization and both algebraic branches; not the asymptotic counting bound.')

def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path('FINITE_DIAGNOSTICS.json'))
    args=parser.parse_args()
    start=time.perf_counter()
    results=dict(rational_example=rational_example(),
                 sharp_conditioning=conditioning(260905),
                 pattern_overlaps=pattern_overlaps(), simple_incidence=simple_incidence(),
                 value_relation_profile=value_relation_profile(260906),
                 absolute_word_overlaps=absolute_word_overlaps(),
                 generic_dictionaries=generic_dictionaries(),
                 signed_local_runs=signed_local_runs(),
                 capped_relations=capped_relations(260907),
                 marker_dictionaries=marker_dictionaries(),
                 split_square_localization=split_square_localization())
    report=dict(revision='3PREL',status='PASS',arithmetic='exact integers and fractions',
                python=platform.python_version(),elapsed_seconds=round(time.perf_counter()-start,3),
                scope='Finite diagnostics only; not a formal or asymptotic proof certificate.',checks=results)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':
    main()
