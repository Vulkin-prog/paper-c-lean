import PaperC.Arithmetic.PNTRatioIdentityClosed

namespace PaperC.PrimeNumberTheoremInput

open Filter Asymptotics
open scoped Topology

theorem primeCounting_ratio_tendsto_closed :
    Tendsto
      (fun L : Nat =>
        (Nat.primeCounting L : Real) /
          ((L : Real) / Real.log (L : Real)))
      atTop (nhds 1) :=
  (isEquivalent_iff_tendsto_one
    eventual_nat_div_log_ne_closed).mp
      primeCounting_isEquivalent_nat_closed

end PaperC.PrimeNumberTheoremInput
