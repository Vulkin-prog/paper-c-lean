import PaperCV282.PoissonStirlingBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Explicit cubic remainder for the Poisson entropy

The bound follows from the logarithmic remainder and the mean value inequality,
with a fixed constant on the whole interval |x| ≤ 1/2.
-/
namespace PaperC.V282.PoissonEntropyTaylor

open Real Set PoissonStirlingBounds

noncomputable section

/-- A uniform quadratic error for the derivative of the entropy remainder. -/
theorem log_one_add_remainder_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |log (1 + x) - x| ≤ 2 * |x| ^ 2 := by
  have h := abs_log_sub_add_sum_range_le (x := -x)
    (by rw [abs_neg]; linarith) 1
  have hlog : |log (1 + x) - x| ≤ |x| ^ 2 / (1 - |x|) := by
    simpa [Finset.sum_range_one, sub_eq_add_neg, add_comm] using h
  apply hlog.trans
  apply (div_le_iff₀ (by linarith : 0 < 1 - |x|)).mpr
  have hp := mul_nonneg (sq_nonneg |x|) (show 0 ≤ 1 / 2 - |x| by linarith)
  nlinarith

/-- The entropy has quadratic term x²/2 and an explicit cubic remainder. -/
theorem entropy_taylor_remainder_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |poissonEntropy (1 + x) - x ^ 2 / 2| ≤ 2 * |x| ^ 3 := by
  let f : ℝ → ℝ := fun y => poissonEntropy (1 + y) - y ^ 2 / 2
  have hd (y : ℝ) (hy : y ∈ Icc (-|x|) |x|) :
      HasDerivAt f (log (1 + y) - y) y := by
    have hpos : 0 < 1 + y := by have h := hy.1; linarith
    have hid := (hasDerivAt_id y).const_add 1
    have h := (((hid.mul (hid.log hpos.ne')).sub hid).add_const 1).sub
      ((hasDerivAt_pow 2 y).div_const 2)
    convert h using 1 <;> first | rfl | simp [hpos.ne', one_div]
  have hb (y : ℝ) (hy : y ∈ Icc (-|x|) |x|) :
      ‖log (1 + y) - y‖ ≤ 2 * |x| ^ 2 := by
    have habs : |y| ≤ |x| := abs_le.mpr hy
    rw [Real.norm_eq_abs]
    exact (log_one_add_remainder_le (habs.trans hx)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) habs 2) (by norm_num))
  have hbound : ‖f x - f 0‖ ≤ (2 * |x| ^ 2) * ‖x - 0‖ := by
    refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y hy => (hd y hy).hasDerivWithinAt) hb (convex_Icc _ _) ?_ ?_
    · simp
    · exact ⟨neg_abs_le x, le_abs_self x⟩
  simpa [f, poissonEntropy, pow_succ, mul_assoc] using hbound

/-- The central entropy remainder, uniform in the rate and the real observation. -/
theorem entropy_central_remainder_le {rate n : ℝ} (hr : 0 < rate)
    (hn : |n - rate| ≤ rate / 2) :
    |rate * poissonEntropy (n / rate) - (n - rate) ^ 2 / (2 * rate)| ≤
      2 * |n - rate| ^ 3 / rate ^ 2 := by
  have hx : |(n - rate) / rate| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hr]
    exact (div_le_iff₀ hr).mpr (by linarith)
  have h := mul_le_mul_of_nonneg_left (entropy_taylor_remainder_le hx) hr.le
  have heq : 1 + (n - rate) / rate = n / rate := by field_simp; ring
  rw [heq] at h
  have habs : rate * |poissonEntropy (n / rate) - ((n - rate) / rate) ^ 2 / 2| =
      |rate * (poissonEntropy (n / rate) - ((n - rate) / rate) ^ 2 / 2)| := by
    rw [abs_mul, abs_of_pos hr]
  rw [habs] at h
  have hleft : rate * (poissonEntropy (n / rate) - ((n - rate) / rate) ^ 2 / 2) =
      rate * poissonEntropy (n / rate) - (n - rate) ^ 2 / (2 * rate) := by
    field_simp
  rw [hleft] at h
  have hright : rate * (2 * |(n - rate) / rate| ^ 3) =
      2 * |n - rate| ^ 3 / rate ^ 2 := by
    rw [abs_div, abs_of_pos hr]
    field_simp
  exact h.trans_eq hright

end
end PaperC.V282.PoissonEntropyTaylor
