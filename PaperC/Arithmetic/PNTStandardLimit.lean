import PaperC.Arithmetic.PNTRatioLimit
import PaperC.Arithmetic.PNTRatioIdentity

namespace PaperC.PrimeNumberTheoremInput

open Filter
open scoped Topology

theorem primeCounting_standard_tendsto :
    Tendsto
      (fun L : ℕ ↦
        (Nat.primeCounting L : ℝ) *
          Real.log (L : ℝ) / (L : ℝ))
      atTop (nhds 1) :=
  primeCounting_ratio_tendsto.congr'
    (Filter.Eventually.of_forall ratio_eq_standard)

end PaperC.PrimeNumberTheoremInput
