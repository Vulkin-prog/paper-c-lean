import PaperC.Arithmetic.PNTPositive

namespace PaperC.PrimeNumberTheoremInput

open Filter

theorem eventual_nat_div_log_ne :
    ∀ᶠ L : ℕ in atTop,
      Ne ((L : ℝ) / Real.log (L : ℝ)) 0 :=
  two_le_eventually.mono fun _ hL ↦ ne_of_gt (nat_div_log_pos hL)

end PaperC.PrimeNumberTheoremInput
