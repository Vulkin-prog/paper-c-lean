import PaperC.Arithmetic.PNTThreshold

namespace PaperC.PrimeNumberTheoremInput

theorem nat_div_log_pos {L : ℕ} (hL : 2 ≤ L) :
    0 < (L : ℝ) / Real.log (L : ℝ) := by
  have hLreal : (1 : ℝ) < (L : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hL)
  exact div_pos (by positivity) (Real.log_pos hLreal)

end PaperC.PrimeNumberTheoremInput
