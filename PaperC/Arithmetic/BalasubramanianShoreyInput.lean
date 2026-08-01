import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Order.Interval.Finset.Nat

/-!
# Balasubramanian--Shorey input

Lemma 15.4 of Paper C invokes Theorem 1 of Balasubramanian and Shorey
(1993).  This file records that published theorem as a named proposition.
All conversion of a family of defective vertices into the product appearing
here is kept outside the bridge.
-/

namespace PaperC
namespace BalasubramanianShoreyInput

open scoped BigOperators

/-- The threshold `μₖ(θ)` printed in Balasubramanian--Shorey. -/
noncomputable def mu (k : ℕ) (θ : ℝ) : ℝ :=
  (k : ℝ) *
    (1 -
      Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ) +
      Real.log (Real.log (Real.log (k : ℝ))) /
        Real.log (k : ℝ) +
      θ / Real.log (k : ℝ))

/-- The pointwise gap `g = k - μₖ(θ)` used in Lemma 15.4. -/
noncomputable def gap (k : ℕ) (θ : ℝ) : ℝ :=
  (k : ℝ) - mu k θ

/--
Exact algebraic form of the displayed gap.  The manuscript only needs its
asymptotic consequence, while the identity itself has no error term.
-/
theorem gap_eq
    {k : ℕ} {θ : ℝ}
    (hlog : Real.log (k : ℝ) ≠ 0) :
    gap k θ =
      ((k : ℝ) / Real.log (k : ℝ)) *
        (Real.log (Real.log (k : ℝ)) -
          Real.log (Real.log (Real.log (k : ℝ))) - θ) := by
  unfold gap mu
  field_simp
  ring

/-- Every prime divisor of `b` is at most `k`. -/
def IsSmoothAt (k b : ℕ) : Prop :=
  ∀ p ∈ b.primeFactors, p ≤ k

/--
The hypotheses of equation (1), (4), and (5) in Theorem 1, represented by a
finset of distinct offsets.  A finset is equivalent to the source's strictly
increasing list `1 ≤ d₁ < ⋯ < dₜ ≤ k`, since the product is symmetric.
-/
def DenseSquareSubproduct
    (k m : ℕ) (offsets : Finset ℕ) (b y : ℕ) : Prop :=
  2 ≤ offsets.card ∧
  offsets.card ≤ k ∧
  offsets ⊆ Finset.Icc 1 k ∧
  0 < b ∧
  0 < y ∧
  (∏ d ∈ offsets, (m + d)) = b * y ^ 2 ∧
  IsSmoothAt k b

/--
**External bridge (Balasubramanian--Shorey, Theorem 1).**

For `k ≥ 27`, a sufficiently dense square subproduct of a block, with
`m > k²`, forces an absolute upper bound on `k`.

The published real constant `C₂` is replaced by its natural ceiling.  This
is an equivalent reformulation because `k` is a natural number.
-/
/- AUDIT_BRIDGE
{
  "id": "BS93-Theorem-1",
  "kind": "external",
  "status": "open",
  "lean_name": "PaperC.BalasubramanianShoreyInput.BalasubramanianShoreyStatement",
  "citation": {
    "authors": ["R. Balasubramanian", "T. N. Shorey"],
    "title": "Squares in products from a block of consecutive integers",
    "journal": "Acta Arithmetica 65 (1993), no. 3, 213–220",
    "doi": "10.4064/aa-65-3-213-220",
    "locator": "Theorem 1; equations (1), (4), and (5), pp. 213–214"
  },
  "source_statement": {
    "verbatim": "Theorem 1. Let k ≥ 27. There exist effectively computable absolute constants θ₀ and C₂",
    "verbatim_is_excerpt": true,
    "displayed_formulas": {
      "equation_1": "(m+d₁)⋯(m+dₜ)=b y²",
      "offset_setup": "k≥t≥2, m≥0, y≥1, 1≤d₁<⋯<dₜ≤k, P⁺(b)≤k",
      "condition_4": "m>k²",
      "condition_5": "t≥μₖ(θ₀)",
      "conclusion": "k≤C₂"
    },
    "source_url": "https://matwbn.icm.edu.pl/ksiazki/aa/aa65/aa6532.pdf",
    "verification": "verified_equivalent_reformulation_against_primary_source_pdf",
    "verification_note": "Equation (1) is (m+d₁)⋯(m+dₜ)=by² with distinct 1≤dᵢ≤k, b,y positive and P⁺(b)≤k; (4) is m>k²; (5) is t≥μₖ(θ₀). The source setup has k≥t≥2. The natural C₂ is the ceiling of the published absolute real constant. The published effectivity of θ₀ and C₂ is not encoded as computable data."
  },
  "manuscript_locator": {
    "result": "Lemma 15.4",
    "pages": "50–51",
    "bibliography_key": "BalasubramanianShorey1993"
  },
  "formalization_relation": "equivalent finset reformulation of the distinct offsets and their product; P⁺(b)≤k is expressed as every prime factor of b being at most k; the real absolute bound C₂ is replaced by its natural ceiling; published effectivity is not encoded"
}
AUDIT_BRIDGE -/
def BalasubramanianShoreyStatement : Prop :=
  ∃ θ₀ : ℝ, ∃ C₂ : ℕ,
    ∀ (k m : ℕ) (offsets : Finset ℕ) (b y : ℕ),
      27 ≤ k →
      k ^ 2 < m →
      mu k θ₀ ≤ (offsets.card : ℝ) →
      DenseSquareSubproduct k m offsets b y →
      k ≤ C₂

/-- Direct finite consumer of the registered theorem. -/
theorem windowBound_of_balasubramanianShorey
    (hBS : BalasubramanianShoreyStatement) :
    ∃ θ₀ : ℝ, ∃ C₂ : ℕ,
      ∀ (k m : ℕ) (offsets : Finset ℕ) (b y : ℕ),
        27 ≤ k →
        k ^ 2 < m →
        mu k θ₀ ≤ (offsets.card : ℝ) →
        DenseSquareSubproduct k m offsets b y →
        k ≤ C₂ :=
  hBS

end BalasubramanianShoreyInput
end PaperC
