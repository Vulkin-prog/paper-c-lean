import PaperC.Arithmetic.PNTSequenceRight

namespace PaperC.PrimeNumberTheoremInput

open Filter Asymptotics
open scoped Topology

theorem primeCounting_isEquivalent_nat_closed :
    IsEquivalent atTop
      (fun L : Nat => (Nat.primeCounting L : Real))
      (fun L : Nat => (L : Real) / Real.log (L : Real)) :=
  (composed_pnt_equivalence.congr_left
    (Filter.Eventually.of_forall composed_primeCounting_apply)).congr_right
      (Filter.Eventually.of_forall composed_scale_apply)

end PaperC.PrimeNumberTheoremInput
