import PaperC.Arithmetic.PNTConv2

namespace PaperC.PrimeNumberTheoremInput

open Filter
open scoped Topology

theorem primeCounting_standard_tendsto_closed :
    Tendsto
      (fun L : Nat =>
        (Nat.primeCounting L : Real) *
          Real.log (L : Real) / (L : Real))
      atTop (nhds 1) :=
  primeCounting_ratio_tendsto_closed.congr'
    (Filter.Eventually.of_forall ratio_eq_standard_closed)

end PaperC.PrimeNumberTheoremInput
