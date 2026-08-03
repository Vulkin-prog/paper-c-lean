# Nicolas--Robin divisor-log specialization

- Bridge ID: `NR83-T1-divisor-log-bound`
- Lean proposition: `PaperC.PellInput.NicolasRobinDivisorLogBoundStatement`
- Current rc2 implication status: `agent_checked_supports`
- Current source locator: `Theorem 1, printed p. 485.`
- Primary-source access: `full_text`
- Review level: agent counter-audit; independent human review required

This document audits the implication from the cited theorem to the ordinary
Lean proposition.  It is neither a formalization of Nicolas--Robin nor an
independent human review, and the registered Lean bridge remains `open`.

## Primary result and normalization

J.-L. Nicolas and G. Robin, *Majorations explicites pour le nombre de
diviseurs de N*, Canadian Mathematical Bulletin 26 (1983), 485--492, DOI
[10.4153/CMB-1983-078-5](https://doi.org/10.4153/CMB-1983-078-5).  The
[publisher PDF](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/D424A2915C0A748C93CF4962D0120B94/S0008439500065188a.pdf/majorations_explicites_pour_le_nombre_de_diviseurs_de_n.pdf)
was inspected.

On printed page 485 the paper defines, for `n > 2`,

```text
F(n) = log(d(n)) * log(log(n)) / (log(2) * log(n)),
```

where `d(n)` is the number of positive divisors.  Theorem 1 says that the
maximum is attained at

```text
n0 = 6,983,776,800
```

and prints its numerical value as `1.5379`.  The displayed decimal must not be
treated as an exact rational number.  The Lean coefficient is obtained by
bounding the normalized quantity `F(n)` by `2`; it is not obtained by
comparing `1.5379` directly with `2*log(2)`.

## Exact safe majorant at the maximizer

The maximizer has the exact factorization

```text
n0 = 2^5 * 3^3 * 5^2 * 7 * 11 * 13 * 17 * 19,
d(n0) = 6 * 4 * 3 * 2^5 = 2304.
```

The following integer comparisons give a wide exact margin:

```text
2304^5 = 64,925,062,108,545,024
        < 48,773,138,392,218,240,000 = n0^2,

n0 * 2^32 = 29,995,092,958,563,328,000
            < 23,283,064,365,386,962,890,625 = 5^32.
```

The first comparison and monotonicity of `log` give
`log(2304) < (2/5) log(n0)`.  The elementary series estimate
`e > 1 + 1 + 1/2 + 1/6 > 5/2`, together with the second comparison, gives
`n0 < e^32`, hence `log(log(n0)) < log(32) = 5 log(2)`.  Multiplication yields

```text
log(d(n0)) * log(log(n0)) < 2 * log(2) * log(n0),
```

so `F(n0) < 2` without assigning an exact meaning to the printed four-digit
decimal.

## Passage to the Lean statement

By the source maximum theorem, `F(n) <= F(n0) < 2` for every `n > 2`.  For
the Lean range `n >= 64`, `log(2)`, `log(n)`, and `log(log(n))` are positive.
Multiplying the normalized inequality by the positive denominator gives

```text
log(d(n)) * log(log(n)) <= 2 * log(2) * log(n).
```

Mathlib's `n.divisors.card` is the same positive-divisor count `d(n)` on this
range.  The Challenge definition `nicolasRobinConstant = 2 * log 2` therefore
matches the right-hand coefficient exactly.  Restricting from `n > 2` to
`n >= 64` is harmless.

## Conclusion and remaining review

The source normalization, the maximizer statement, and the exact elementary
majorant above support the registered Lean proposition.  The derivation is
documentary rather than kernel-checked and has not received independent human
review.  Its rc2 status is `agent_checked_supports`; the ordinary Lean bridge
remains `open`.
