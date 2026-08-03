# Evertse--Silverman split quadratic specialization

- Bridge ID: `ES86-T1b-Q-split-n2`
- Lean proposition: `PaperC.EvertseSilvermanInput.EvertseSilvermanAbscissaStatement`
- Current rc2 implication status: `agent_checked_supports`
- Current source locator: `Theorem 1(b), printed p. 238.`
- Primary-source access: `full_text`
- Review level: agent counter-audit; independent human review required

This document audits a source-to-Lean implication.  It is not a kernel proof
or independent human peer review, and the registered Lean bridge remains
`open`.

## Primary result

J.-H. Evertse and J. H. Silverman, *Uniform bounds for the number of
solutions to Y^n = f(X)*, Mathematical Proceedings of the Cambridge
Philosophical Society 100 (1986), 237--248, DOI
[10.1017/S0305004100066068](https://doi.org/10.1017/S0305004100066068).
The authors' final PDF is also available from the
[CWI repository](https://ir.cwi.nl/pub/1788/1788D.pdf).

On printed page 238, Theorem 1 defines

```text
V(R_S, f, n) = { x in R_S : f(x) is in K*^n }.
```

Part (b) states that, when `d >= 3` and an extension `L/K` contains at
least three zeros of `f`,

```text
#V(R_S, f, 2) <= 7^(M(4m + 9s)) * 4^(kappa_2(L)).
```

Here `m = [K:Q]`, `M = [L:K]`, `s` is the number of places in `S`, and
`kappa_2(L)` is the 2-rank of the ideal class group of `L`.  The theorem counts
abscissas `x`, not pairs `(x,y)`.

## Specialization

Fix the Challenge data `d`, `shift : Fin d -> Z`, and `e`, and put

```text
K = L = Q,
n = 2,
f(T) = e * product_r (T + shift r).
```

Then `m = M = 1`, the class group of `Q` is trivial, and hence
`kappa_2(Q) = 0`.  Injectivity of `shift`, together with `d >= 3`, supplies at
least three distinct rational roots `-shift r`.

Let `S` contain the infinite place and every finite prime dividing

```text
2 * |e| * product_{r<s} |shift r - shift s|.
```

This is the set counted by `badPlaceCount`; including the prime `2` can only
enlarge a minimal admissible set of bad places.  The coefficients of `f` are
`S`-integral.  Its discriminant is, up to sign,

```text
e^(2d-2) * product_{r<s} (shift r - shift s)^2,
```

so it is an `S`-unit.  The source hypotheses are therefore satisfied and its
bound becomes exactly

```text
7^(4 + 9 * badPlaceCount shift e).
```

If an integer `X` satisfies the Challenge predicate, there is a nonzero
integer `Z` with `Z^2 = f(X)`.  Thus `X` is an `S`-integer and belongs to
`V(R_S,f,2)`.  The inclusion is on abscissas, so no factor for the two possible
signs of `Z` is needed here.  The Challenge's squarefreeness condition on `e`
is an additional restriction and does not weaken the implication.

## Edge conditions

- `e != 0` and injectivity of `shift` ensure that the discriminant-support
  product is nonzero.
- Requiring `Z != 0` merely restricts the set counted by the source theorem.
- An integer solution is a special case of an `S`-integer solution.
- The prime-factor set is distinct-prime support, matching the cardinal `s`.

## Conclusion and remaining review

The agent counter-audit found that Theorem 1(b) specializes to the Challenge
abscissa bound with the parameter substitutions above.  This derivation has
not been formalized from a formal statement of Evertse--Silverman and has not
received independent human review.  The rc2 status is
`agent_checked_supports`; the ordinary Lean bridge remains `open`.
