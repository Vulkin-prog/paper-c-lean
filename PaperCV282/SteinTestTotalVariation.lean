import PaperCV282.SteinFiniteExpectation

/-!
# From scalar test sets to the historical half-L1 total variation

The maximizing test set is exhibited directly. This avoids a hidden
normalization change between Stein's test-set equation and the retained
real-mass representation of total variation.
-/

namespace PaperC.V282.SteinTestTotalVariation

open ArratiaGoldsteinGordonInput IndependentThinning SectionThirteenFiniteBound
open SteinFiniteExpectation
open scoped BigOperators

noncomputable section

local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- Restricting a summable nonnegative mass to an arbitrary set remains summable. -/
theorem summable_restricted_mass {p : ℕ → ℝ} (hp : Summable p)
    (hp0 : ∀ k, 0 ≤ p k) (A : Set ℕ) :
    Summable (fun k => if k ∈ A then p k else 0) := by
  classical
  apply hp.of_nonneg_of_le
  · intro k
    split_ifs <;> simp [hp0]
  · intro k
    split_ifs <;> simp [hp0]

/-- The positive part of the mass difference is an exact maximizing test set. -/
theorem natTotalVariation_eq_positive_set {p q : ℕ → ℝ}
    (hp : HasSum p 1) (hq : HasSum q 1)
    (hp0 : ∀ k, 0 ≤ p k) (hq0 : ∀ k, 0 ≤ q k) :
    natTotalVariation p q =
      (∑' k, if q k ≤ p k then p k else 0) -
        ∑' k, if q k ≤ p k then q k else 0 := by
  classical
  have hpa : Summable (fun k => if q k ≤ p k then p k else 0) := by
    apply hp.summable.of_nonneg_of_le
    · intro k; split_ifs <;> simp [hp0]
    · intro k; split_ifs <;> simp [hp0]
  have hqa : Summable (fun k => if q k ≤ p k then q k else 0) := by
    apply hq.summable.of_nonneg_of_le
    · intro k; split_ifs <;> simp [hq0]
    · intro k; split_ifs <;> simp [hq0]
  have hpoint (k : ℕ) : |p k - q k| =
      2 * ((if q k ≤ p k then p k else 0) - (if q k ≤ p k then q k else 0)) - (p k - q k) := by
    by_cases h : q k ≤ p k
    · rw [if_pos h, if_pos h, abs_of_nonneg (sub_nonneg.mpr h)]
      ring
    · rw [if_neg h, if_neg h, abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge h))]
      ring
  unfold natTotalVariation
  simp_rw [hpoint]
  rw [((hpa.sub hqa).mul_left 2).tsum_sub (hp.summable.sub hq.summable),
    tsum_mul_left, hpa.tsum_sub hqa, hp.summable.tsum_sub hq.summable,
    hp.tsum_eq, hq.tsum_eq]
  ring

/-- A uniform bound for all test-set discrepancies bounds the exact half-L1 distance. -/
theorem natTotalVariation_le_of_test_sets {p q : ℕ → ℝ}
    (hp : HasSum p 1) (hq : HasSum q 1)
    (hp0 : ∀ k, 0 ≤ p k) (hq0 : ∀ k, 0 ≤ q k) {r : ℝ}
    (h : ∀ A : Set ℕ,
      |(∑' k, if k ∈ A then p k else 0) - ∑' k, if k ∈ A then q k else 0| ≤ r) :
    natTotalVariation p q ≤ r := by
  rw [natTotalVariation_eq_positive_set hp hq hp0 hq0]
  exact (le_abs_self _).trans (h {k | q k ≤ p k})

/-- A finite pushforward assigns the same mass as its original event. -/
theorem restricted_finiteNatLaw_eq_eventProbability {Ω : Type*} [Fintype Ω]
    (μ : FinitePMF Ω) (W : Ω → ℕ) (A : Set ℕ) :
    (∑' k, if k ∈ A then finiteNatLaw μ W k else 0) =
      eventProbability μ (fun ω => W ω ∈ A) := by
  classical
  let s : Finset ℕ := Finset.univ.image W
  have hout (k : ℕ) (hk : k ∉ s) : finiteNatLaw μ W k = 0 := by
    unfold finiteNatLaw
    apply Finset.sum_eq_zero
    intro ω _
    have hne : W ω ≠ k := fun h => hk (Finset.mem_image.mpr ⟨ω, Finset.mem_univ _, h⟩)
    simp [hne]
  rw [tsum_eq_sum (s := s) (fun k hk => by simp [hout k hk])]
  unfold finiteNatLaw eventProbability
  calc
    _ = ∑ k ∈ s, ∑ ω, if W ω = k then (if k ∈ A then μ.prob ω else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k ∈ A
      · simp only [hk, if_true]
      · simp [hk]
    _ = ∑ ω, ∑ k ∈ s, if W ω = k then (if k ∈ A then μ.prob ω else 0) else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro ω _
      have hmem : W ω ∈ s := Finset.mem_image.mpr ⟨ω, Finset.mem_univ _, rfl⟩
      simp [hmem]

/-- Test-set representation for any finite random variable against a countable target law. -/
theorem finiteNatLaw_totalVariation_le_of_test_sets {Ω : Type*} [Fintype Ω]
    (μ : FinitePMF Ω) (W : Ω → ℕ) {q : ℕ → ℝ}
    (hq : HasSum q 1) (hq0 : ∀ k, 0 ≤ q k) {r : ℝ}
    (h : ∀ A : Set ℕ,
      |eventProbability μ (fun ω => W ω ∈ A) - ∑' k, if k ∈ A then q k else 0| ≤ r) :
    natTotalVariation (finiteNatLaw μ W) q ≤ r := by
  apply natTotalVariation_le_of_test_sets (hasSum_finiteNatLaw μ W) hq
    (finiteNatLaw_nonneg μ W) hq0
  intro A
  rw [restricted_finiteNatLaw_eq_eventProbability]
  exact h A

end
end PaperC.V282.SteinTestTotalVariation
