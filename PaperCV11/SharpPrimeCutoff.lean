import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt

/-!
# Paper C v1.1: sharp prime cutoff

The v1.1 conditioning argument uses

`Y* = floor (exp (S_N / sqrt 2))`,

where `S_N = sqrt (log N * log (log N))`. This is intentionally distinct
from the historical cutoff `floor (B^2 * log B)` and is therefore defined in
a separate namespace rather than changing `PaperC.TerminalPrimeCutoff`.
-/

namespace PaperC
namespace V11
namespace SharpPrimeCutoff

noncomputable section

/-- The moderate-deviation scale `S_N` from Paper C v1.1. -/
def saddleScale (N : ℕ) : ℝ :=
  Real.sqrt (Real.log N * Real.log (Real.log N))

/-- The real scale before taking the natural-valued floor. -/
def sharpPrimeScale (N : ℕ) : ℝ :=
  Real.exp (saddleScale N / Real.sqrt 2)

/-- The exact v1.1 prime cutoff `floor (exp (S_N / sqrt 2))`. -/
def sharpPrimeCutoff (N : ℕ) : ℕ :=
  ⌊sharpPrimeScale N⌋₊

/-- `S_N` is nonnegative by construction, including at small inputs. -/
theorem saddleScale_nonneg (N : ℕ) :
    0 ≤ saddleScale N :=
  Real.sqrt_nonneg _

/-- The real quantity defining the cutoff is always strictly positive. -/
theorem sharpPrimeScale_pos (N : ℕ) :
    0 < sharpPrimeScale N :=
  Real.exp_pos _

/-- The natural floor lies below the real scale defining it. -/
theorem cast_sharpPrimeCutoff_le_scale (N : ℕ) :
    (sharpPrimeCutoff N : ℝ) ≤ sharpPrimeScale N := by
  exact Nat.floor_le (sharpPrimeScale_pos N).le

/-- The defining scale is strictly below one plus its natural floor. -/
theorem sharpPrimeScale_lt_cutoff_add_one (N : ℕ) :
    sharpPrimeScale N < (sharpPrimeCutoff N : ℝ) + 1 := by
  exact Nat.lt_floor_add_one (sharpPrimeScale N)

end

end SharpPrimeCutoff
end V11
end PaperC
