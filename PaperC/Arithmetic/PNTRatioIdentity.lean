import PaperC.Arithmetic.PNTEventuallyPositive

namespace PaperC.PrimeNumberTheoremInput

theorem ratio_eq_standard (L : ℕ) :
    (Nat.primeCounting L : ℝ) /
        ((L : ℝ) / Real.log (L : ℝ)) =
      (Nat.primeCounting L : ℝ) *
        Real.log (L : ℝ) / (L : ℝ) := by
  rw [div_div_eq_mul_div]

end PaperC.PrimeNumberTheoremInput
