import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Paper C v1.1: the hard-conditioning saddle

The hard-conditioning scheme has two normalized exponential envelopes. With
`a = log Y / S_N`, their leading coefficients are `a` and `(2 * a)⁻¹`.
This file proves the exact max-min calculation used in Proposition 3.11.

The arithmetic estimates producing the two envelopes are formalized
separately. The final declaration below is the algebraic v1.1 endpoint and
introduces no new literature input.
-/

namespace PaperC
namespace V11
namespace HardConditioningSaddle

/-- No positive cutoff can make both `B / u` and `u` exceed `sqrt B`. -/
theorem min_div_self_le_sqrt
    {B u : ℝ} (hB : 0 ≤ B) (hu : 0 < u) :
    min (B / u) u ≤ Real.sqrt B := by
  by_cases hsmall : u ≤ Real.sqrt B
  · exact (min_le_right _ _).trans hsmall
  · have hsqrtLe : Real.sqrt B ≤ u := le_of_not_ge hsmall
    have hdiv : B / u ≤ Real.sqrt B := by
      apply (div_le_iff₀ hu).2
      calc
        B = (Real.sqrt B) ^ 2 := (Real.sq_sqrt hB).symm
        _ = Real.sqrt B * Real.sqrt B := by rw [pow_two]
        _ ≤ Real.sqrt B * u :=
          mul_le_mul_of_nonneg_left hsqrtLe (Real.sqrt_nonneg B)
    exact (min_le_left _ _).trans hdiv

/-- At `u = sqrt B`, the two elementary envelopes agree. -/
theorem div_sqrt_eq_sqrt
    {B : ℝ} (hB : 0 < B) :
    B / Real.sqrt B = Real.sqrt B := by
  have hsqrtNe : Real.sqrt B ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hB)
  calc
    B / Real.sqrt B = (Real.sqrt B) ^ 2 / Real.sqrt B := by
      rw [Real.sq_sqrt hB.le]
    _ = Real.sqrt B := by
      field_simp

/-- The balanced value of the generic pair of envelopes is `sqrt B`. -/
theorem min_at_sqrt
    {B : ℝ} (hB : 0 < B) :
    min (B / Real.sqrt B) (Real.sqrt B) = Real.sqrt B := by
  rw [div_sqrt_eq_sqrt hB, min_self]

/-- The article's two normalizations of the saddle coefficient agree. -/
theorem sqrt_half_eq_inv_sqrt_two :
    Real.sqrt ((1 : ℝ) / 2) = (Real.sqrt 2)⁻¹ := by
  rw [Real.sqrt_div (by positivity)]
  simp [one_div]

/-- Algebraic normalization of the removed-start coefficient. -/
theorem half_div_eq_inv_two_mul (a : ℝ) :
    ((1 : ℝ) / 2) / a = (2 * a)⁻¹ := by
  rw [div_div, one_div]

/-- The common hard-conditioning coefficient is at most `1 / sqrt 2`. -/
theorem hard_saddle_upper
    {a : ℝ} (ha : 0 < a) :
    min a ((2 * a)⁻¹) ≤ (Real.sqrt 2)⁻¹ := by
  have h := min_div_self_le_sqrt
    (B := (1 : ℝ) / 2) (u := a) (by norm_num) ha
  rw [half_div_eq_inv_two_mul, min_comm, sqrt_half_eq_inv_sqrt_two] at h
  exact h

/-- Twice the reciprocal square root of two is the square root of two. -/
theorem two_mul_inv_sqrt_two :
    2 * (Real.sqrt 2)⁻¹ = Real.sqrt 2 := by
  simpa [div_eq_mul_inv] using
    (div_sqrt_eq_sqrt (B := (2 : ℝ)) (by norm_num))

/-- The upper bound is attained at `a = 1 / sqrt 2`. -/
theorem hard_saddle_attained :
    min ((Real.sqrt 2)⁻¹) ((2 * (Real.sqrt 2)⁻¹)⁻¹) =
      (Real.sqrt 2)⁻¹ := by
  rw [two_mul_inv_sqrt_two, min_self]

end HardConditioningSaddle
end V11

/--
Palomar-facing algebraic endpoint for Paper C v1.1, Proposition 3.11.
It records both the universal max-min bound and attainment at the unique
crossing used by the hard-conditioning proof.
-/
theorem paper_c_v1_1_hard_conditioning_saddle :
    (∀ a : ℝ, 0 < a →
      min a ((2 * a)⁻¹) ≤ (Real.sqrt 2)⁻¹) ∧
    min ((Real.sqrt 2)⁻¹) ((2 * (Real.sqrt 2)⁻¹)⁻¹) =
      (Real.sqrt 2)⁻¹ := by
  constructor
  · intro a ha
    exact V11.HardConditioningSaddle.hard_saddle_upper ha
  · exact V11.HardConditioningSaddle.hard_saddle_attained

end PaperC
