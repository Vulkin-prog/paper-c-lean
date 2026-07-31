import PaperC.Asymptotics.SteinChenCritical
import PaperC.Probability.ConditionalAGGAverage

set_option maxHeartbeats 1200000

/-!
# The averaged conditional AGG error in the critical window

This module packages the total variation between the averaged conditional
good-start law and its common Poisson target at the literal terminal prime
cutoff, and proves its pointwise nonnegativity.  Quantitative bounds for this
concrete error are assembled downstream from the Stein--Chen terms and the
canonical homogeneous-mass estimate.
-/

namespace PaperC
namespace ConditionalAGGCritical

open ArratiaGoldsteinGordonInput
open ConditionalAGGAverage
open SectionThirteenFiniteBound
open TerminalPrimeCutoff

noncomputable section

/--
Total variation of the uniformly averaged conditional good-start law at the
literal terminal cutoff.
-/
noncomputable def averagedConditionalGoodTotalVariation
    (N L : ℕ) : ℝ :=
  natTotalVariation
    (averagedConditionalGoodLaw N L
      (terminalPrimeCutoff (L + 1)))
    (commonConditionalGoodPoissonLaw N L
      (terminalPrimeCutoff (L + 1)))

/-- The averaged conditional total variation is pointwise nonnegative. -/
theorem averagedConditionalGoodTotalVariation_nonneg
    (N L : ℕ) :
    0 ≤ averagedConditionalGoodTotalVariation N L :=
  natTotalVariation_nonneg _ _

end

end ConditionalAGGCritical
end PaperC
