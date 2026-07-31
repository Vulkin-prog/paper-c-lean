import PaperC.Arithmetic.PrimeCountBridge
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Laishram--Shorey input for a product of consecutive integers

This module records, without strengthening it, Corollary 1 of Laishram and
Shorey [20].  All subsequent manipulations of the bound (discarding the
nonnegative correction term and extracting primes above the window length)
are carried out in Lean.
-/

namespace PaperC
namespace LaishramShoreyInput

open scoped BigOperators

/-- The product `Δ(n,k) = n(n+1)⋯(n+k-1)` used in [20]. -/
def consecutiveProduct (n k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, (n + i)

/--
The correction term `δ(k)` appearing in Corollary 1 of [20].

It is `3` for `k=2`, `2` for `3≤k≤6`, `1` for `7≤k≤16`, and `0`
thereafter.
-/
def exceptionCorrection (k : ℕ) : ℕ :=
  if k = 2 then 3
  else if k ≤ 6 then 2
  else if k ≤ 16 then 1
  else 0

/--
**External bridge (Laishram--Shorey, Corollary 1).**

For `n > k ≥ 2`, this is the published lower bound for the number `ω(Δ)`
of distinct prime divisors of `Δ(n,k)`.  Natural-number division by `4`
is exactly the floor in the printed statement.
-/
/- AUDIT_BRIDGE
{
  "id": "LS04-Corollary-1",
  "kind": "external",
  "status": "open",
  "lean_name": "PaperC.LaishramShoreyInput.LaishramShoreyStatement",
  "citation": {
    "authors": ["Shanta Laishram", "T. N. Shorey"],
    "title": "Number of prime divisors in a product of consecutive integers",
    "journal": "Acta Arithmetica 113 (2004), 327–341",
    "doi": "10.4064/aa113-4-3",
    "locator": "Corollary 1, equation (10), p. 330; definition of δ(k), p. 328"
  },
  "source_statement": {
    "verbatim": "Let n > k. Then ω(Δ) ≥ min(π(k) + ⌊3/4 π(k)⌋ − 1 + δ(k), π(2k) − 1).",
    "source_url": "https://www.impan.pl/shop/en/publication/transaction/download/product/83314",
    "verification": "verified_transcription_against_primary_source_pdf",
    "verification_note": "The surrounding source fixes k ≥ 2 and defines Δ(n,k)=n(n+1)⋯(n+k−1). The four cases of δ(k) are transcribed in exceptionCorrection."
  },
  "manuscript_locator": {
    "result": "Lemma 15.2",
    "pages": "49–50",
    "reference": "[20]"
  },
  "formalization_relation": "exact natural-number transcription; primeFactors.card is ω, PrimesUpTo.count is π, and Nat division by 4 is the printed floor"
}
AUDIT_BRIDGE -/
def LaishramShoreyStatement : Prop :=
  ∀ n k : ℕ, 2 ≤ k → k < n →
    min
        (PrimesUpTo.count k + (3 * PrimesUpTo.count k) / 4 - 1 +
          exceptionCorrection k)
        (PrimesUpTo.count (2 * k) - 1) ≤
      (consecutiveProduct n k).primeFactors.card

/--
The slightly weaker form quoted in Paper C follows by discarding the
nonnegative correction `δ(k)`.
-/
theorem manuscript_bound_of_laishramShorey
    (hLS : LaishramShoreyStatement)
    {n k : ℕ} (hk : 2 ≤ k) (hnk : k < n) :
    min
        (PrimesUpTo.count k + (3 * PrimesUpTo.count k) / 4 - 1)
        (PrimesUpTo.count (2 * k) - 1) ≤
      (consecutiveProduct n k).primeFactors.card := by
  refine (min_le_min ?_ le_rfl).trans (hLS n k hk hnk)
  exact Nat.le_add_right
    (PrimesUpTo.count k + (3 * PrimesUpTo.count k) / 4 - 1)
    (exceptionCorrection k)

end LaishramShoreyInput
end PaperC
