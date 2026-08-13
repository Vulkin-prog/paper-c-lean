import PaperC.Arithmetic.PNTStandardLimit

namespace PaperC.PrimeNumberTheoremInput

open Filter
open scoped Topology

theorem project_limit :
    Tendsto
      (fun L : Nat =>
        (PrimesUpTo.count L : Real) *
          Real.log (L : Real) / (L : Real))
      atTop (nhds 1) :=
  primeCounting_standard_tendsto.congr'
    (Filter.Eventually.of_forall fun L => by
      rw [count_eq_primeCounting])

end PaperC.PrimeNumberTheoremInput
