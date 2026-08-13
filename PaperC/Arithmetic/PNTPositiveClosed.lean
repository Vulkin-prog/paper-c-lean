import PaperC.Arithmetic.PNTThresholdClosed

namespace PaperC.PrimeNumberTheoremInput

theorem nat_div_log_pos_closed {L : Nat} (hL : 2 ≤ L) :
    0 < (L : Real) / Real.log (L : Real) := by
  have hLreal : (1 : Real) < (L : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hL)
  exact div_pos (by positivity) (Real.log_pos hLreal)

end PaperC.PrimeNumberTheoremInput
