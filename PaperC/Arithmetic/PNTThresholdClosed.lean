import PaperC.Arithmetic.PNTStep

namespace PaperC.PrimeNumberTheoremInput

open Filter

theorem two_le_eventually_closed :
    ∀ᶠ L : Nat in atTop, 2 ≤ L :=
  eventually_ge_atTop 2

end PaperC.PrimeNumberTheoremInput
