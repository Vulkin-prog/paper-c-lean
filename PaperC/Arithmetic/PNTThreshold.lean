import PaperC.Arithmetic.PrimeCountingBridgePNT

namespace PaperC.PrimeNumberTheoremInput

open Filter

theorem two_le_eventually : ∀ᶠ L : ℕ in atTop, 2 ≤ L :=
  eventually_ge_atTop 2

end PaperC.PrimeNumberTheoremInput
