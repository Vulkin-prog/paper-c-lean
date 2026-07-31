import PaperC.Analysis.SmoothEulerProduct
import PaperC.Arithmetic.WeightedDefectCounting

/-!
# Global finite bound for square-defect values

This is the quantitative finite counterpart of the global-count line in
Proposition 3.2.  The weighted arithmetic count and the elementary
Euler-product estimate combine without an additive error because zero was
removed before counting.
-/

namespace PaperC

/--
The positive values `n ≤ X` representable as `s * a^2`, with `s` a product
of distinct primes at most `H`, satisfy

`# ≤ √X * exp (2 √H)`.
-/
theorem card_positiveHDefectValues_cast_le_sqrt_mul_exp
    (H X : ℕ) :
    ((WeightedDefectCounting.positiveDefectValues
        (DefectCounting.smallPrimesUpTo H) X).card : ℝ) ≤
      Real.sqrt X * Real.exp (2 * Real.sqrt H) := by
  calc
    ((WeightedDefectCounting.positiveDefectValues
        (DefectCounting.smallPrimesUpTo H) X).card : ℝ)
        ≤ Real.sqrt X *
            ∏ p ∈ DefectCounting.smallPrimesUpTo H,
              (1 + (Real.sqrt p)⁻¹) :=
      WeightedDefectCounting.card_positiveHDefectValues_cast_le_eulerProduct H X
    _ ≤ Real.sqrt X * Real.exp (2 * Real.sqrt H) :=
      mul_le_mul_of_nonneg_left
        (prod_smallPrimesUpTo_one_add_inv_sqrt_le H)
        (Real.sqrt_nonneg X)

end PaperC
