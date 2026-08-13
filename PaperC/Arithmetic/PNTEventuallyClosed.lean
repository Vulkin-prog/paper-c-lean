import PaperC.Arithmetic.PNTPositiveClosed

namespace PaperC.PrimeNumberTheoremInput

open Filter

theorem eventual_nat_div_log_ne_closed :
    ∀ᶠ L : Nat in atTop,
      (L : Real) / Real.log (L : Real) ≠ 0 :=
  two_le_eventually_closed.mono fun _ hL =>
    ne_of_gt (nat_div_log_pos_closed hL)

end PaperC.PrimeNumberTheoremInput
