import PaperC.Arithmetic.PNTEventuallyClosed

namespace PaperC.PrimeNumberTheoremInput

theorem ratio_eq_standard_closed (L : Nat) :
    (Nat.primeCounting L : Real) /
        ((L : Real) / Real.log (L : Real)) =
      (Nat.primeCounting L : Real) *
        Real.log (L : Real) / (L : Real) := by
  rw [div_div_eq_mul_div]

end PaperC.PrimeNumberTheoremInput
