import PaperC.Arithmetic.PNTStandardClosed2

namespace PaperC.PrimeNumberTheoremInput

open Filter
open scoped Topology

theorem project_prime_counting_tendsto_closed :
    Tendsto
      (fun L : Nat =>
        (PrimesUpTo.count L : Real) *
          Real.log (L : Real) / (L : Real))
      atTop (nhds 1) :=
  primeCounting_standard_tendsto_closed.congr'
    (Filter.Eventually.of_forall fun L => by
      rw [count_eq_primeCounting_closed])

end PaperC.PrimeNumberTheoremInput
