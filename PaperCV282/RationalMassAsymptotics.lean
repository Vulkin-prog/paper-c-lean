import PaperCV282.IntervalRationalMass
import PaperCV282.LogarithmicWordPowers
import PaperCV282.MacroscopicGeometry

/-!
# Rational mass with the word-space size explicit

The finite interval estimate gives a profile involving both the square
and cube roots of `Q_B = 2^(L+1)`. Only the polynomial length factor is
absorbed into `M^ε`. The threshold is independent of the interval's lower
endpoint, the length, and the historical coding parameter.
The total profile does not itself prove the two height-filtered bounds.
-/

namespace PaperC.V282.RationalMassAsymptotics

open PropositionSixteenOne LogarithmicWordPowers

noncomputable section

/-- A reversed or empty start interval contributes zero systematic mass. -/
theorem systematicMass_eq_zero_of_upper_le_lower
    {N M A L : ℕ} (hMN : M ≤ N) : systematicMass A N M L = 0 := by
  by_cases hN : 2 ≤ N
  · rw [systematicMass_eq_boundedRationalMass hN]
    simp [BoundedRatioGeometry.boundedRationalMass,
      BoundedRatioGeometry.separatedBoundedRatioPairs,
      BoundedRatioGeometry.boundedRatioPairs, BoundedRatioGeometry.boundedRatioBlock,
      Finset.Ico_eq_empty (not_lt_of_ge hMN)]
  · simp [systematicMass, hN]

/-- Finite profile for every lower endpoint, retaining both roots of `Q_B`. -/
theorem systematicMass_le_word_profile
    {N M A L : ℕ} (hM : 1 ≤ M) (hA : 1 ≤ A) :
    systematicMass A N M L ≤
      6 * (M : ℝ) * (L + 1) ^ 4 *
        (((2 : ℝ) ^ (L + 1)) ^ (1 / (2 : ℝ)) +
          ((2 : ℝ) ^ (L + 1)) ^ (1 / (3 : ℝ))) := by
  by_cases hNM : N ≤ M
  · have hfinite := IntervalRationalMass.systematicMass_le_common_polynomial
      (L := L) hM hNM hA
    exact hfinite.trans (mul_le_mul_of_nonneg_left
      (add_le_add (two_pow_div_le_word_rpow L 2 (by omega))
        (two_pow_div_le_word_rpow L 3 (by omega))) (by positivity))
  · rw [systematicMass_eq_zero_of_upper_le_lower (by omega)]
    positivity

/-- Literal `M^ε` form of the rational total profile, uniformly in every
interval lower endpoint and coding parameter, with no critical balance. -/
theorem systematicMass_uniform_profile
    (C : ℝ) (hC : 0 ≤ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ L : ℕ,
      ((L + 1 : ℕ) : ℝ) ≤ C * Real.log M → ∀ N A : ℕ, 1 ≤ A →
      systematicMass A N M L ≤
        (M : ℝ) ^ ε * ((M : ℝ) *
          (((2 : ℝ) ^ (L + 1)) ^ (1 / (2 : ℝ)) +
            ((2 : ℝ) ^ (L + 1)) ^ (1 / (3 : ℝ)))) := by
  obtain ⟨Mpoly, hpoly⟩ := polynomial_factor_le_rpow_eventually C hC 6 4 ε hε
  refine ⟨max Mpoly 1, ?_⟩
  intro M hM L hL N A hA
  have hMone : 1 ≤ M := (le_max_right _ _).trans hM
  have hfactor : 6 * (L + 1 : ℝ) ^ 4 ≤ (M : ℝ) ^ ε := by
    have h := hpoly M ((le_max_left _ _).trans hM) L hL
    simpa only [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 6 * (L + 1 : ℝ) ^ 4)] using h
  calc
    _ ≤ 6 * (M : ℝ) * (L + 1) ^ 4 *
        (((2 : ℝ) ^ (L + 1)) ^ (1 / (2 : ℝ)) +
          ((2 : ℝ) ^ (L + 1)) ^ (1 / (3 : ℝ))) :=
      systematicMass_le_word_profile hMone hA
    _ = (6 * (L + 1 : ℝ) ^ 4) * ((M : ℝ) *
        (((2 : ℝ) ^ (L + 1)) ^ (1 / (2 : ℝ)) +
          ((2 : ℝ) ^ (L + 1)) ^ (1 / (3 : ℝ)))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hfactor (by positivity)

/-- The preceding total estimate on the exact macroscopic domain with `A=3`.
Its threshold precedes `δ`; identification of a unique canonical channel
has its own additional, `δ`-dependent threshold. -/
theorem macroscopic_systematicMass_uniform_profile
    (C : ℝ) (hC : 0 ≤ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ L : ℕ,
      ((L + 1 : ℕ) : ℝ) ≤ C * Real.log M → ∀ δ : ℝ,
      systematicMass 3 ⌈(M : ℝ) ^ δ⌉₊ M L ≤
        (M : ℝ) ^ ε * ((M : ℝ) *
          (((2 : ℝ) ^ (L + 1)) ^ (1 / (2 : ℝ)) +
            ((2 : ℝ) ^ (L + 1)) ^ (1 / (3 : ℝ)))) := by
  obtain ⟨M₀, hM₀⟩ := systematicMass_uniform_profile C hC ε hε
  exact ⟨M₀, fun M hM L hL δ => hM₀ M hM L hL _ 3 (by omega)⟩

end
end PaperC.V282.RationalMassAsymptotics
