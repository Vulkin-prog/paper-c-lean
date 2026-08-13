import PaperC.Arithmetic.PNTEventuallyPositive

namespace PaperC.PrimeNumberTheoremInput

open Filter
open scoped Topology

theorem primeCounting_ratio_tendsto :
    Tendsto
      (fun L : ℕ ↦
        (Nat.primeCounting L : ℝ) /
          ((L : ℝ) / Real.log (L : ℝ)))
      atTop (nhds 1) :=
  (isEquivalent_iff_tendsto_one eventual_nat_div_log_ne).mp
    primeCounting_isEquivalent_nat

end PaperC.PrimeNumberTheoremInput
