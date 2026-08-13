import PaperC.Arithmetic.PrimeCountIdentityPNT
import PrimeNumberTheoremAnd.Consequences

namespace PaperC.PrimeNumberTheoremInput

open Filter Asymptotics
open scoped Topology

theorem composed_pnt_equivalence :
    ((fun x : Real => (Nat.primeCounting ⌊x⌋₊ : Real)) ∘
        ((↑) : Nat → Real)) ~[atTop]
      ((fun x : Real => x / Real.log x) ∘
        ((↑) : Nat → Real)) :=
  pi_alt'.comp_tendsto tendsto_natCast_atTop_atTop

end PaperC.PrimeNumberTheoremInput
