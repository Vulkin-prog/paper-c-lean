import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Exponential majorant for finite certificate sums

The certificate families in Lemma 7.1 are finite, so their sums stop after
finitely many sizes.  This module records that every such nonnegative finite
sum is bounded by the full exponential series.
-/

namespace PaperC

open scoped BigOperators

/-- Every nonnegative finite exponential series is bounded by `Real.exp`. -/
theorem sum_range_pow_div_factorial_le_exp
    (x : ℝ) (hx : 0 ≤ x) (R : ℕ) :
    (∑ r ∈ Finset.range R, x ^ r / (r.factorial : ℝ)) ≤
      Real.exp x := by
  rw [Real.exp_eq_exp_ℝ]
  exact
    sum_le_hasSum (Finset.range R)
      (fun r hr ↦ div_nonneg (pow_nonneg hx r) (by positivity))
      (NormedSpace.expSeries_div_hasSum_exp x)

/-- Rational finite sums, cast to `ℝ`, obey the same exponential bound. -/
theorem ratCast_sum_range_pow_div_factorial_le_exp
    (x : ℚ) (hx : 0 ≤ x) (R : ℕ) :
    (((∑ r ∈ Finset.range R,
        x ^ r / (r.factorial : ℚ)) : ℚ) : ℝ) ≤
      Real.exp (x : ℝ) := by
  have hx' : (0 : ℝ) ≤ (x : ℝ) := by
    exact_mod_cast hx
  simpa using
    sum_range_pow_div_factorial_le_exp (x : ℝ) hx' R

end PaperC
