import PaperC.Asymptotics.BadStartMassCritical
import PaperC.Asymptotics.ConditionalAGGCritical
import PaperC.Probability.SectionThirteenCouplings

set_option maxHeartbeats 1200000

/-!
# Corollary 13.9 in the critical window

This module assembles the three finite comparisons of Section 13:

1. remove terminal bad starts by the exact full-cylinder coupling;
2. apply the averaged conditional Arratia--Goldstein--Gordon estimate;
3. couple the resulting Poisson law to the manuscript rate `N / 2^L`.

At the literal terminal prime cutoff, the first and third errors are the
already proved `o_C(1)` terms of Lemmas 13.3--13.4, while the middle error is
the conditional conclusion of `ConditionalAGGCritical`.
-/

namespace PaperC
namespace SectionThirteenCritical

open ArratiaGoldsteinGordonInput
open BadStartCount
open SectionThirteenFiniteBound
open SectionThirteenCouplings
open TerminalPrimeCutoff

noncomputable section

/-- The total variation distance appearing in Corollary 13.9. -/
noncomputable def fullDyadicTargetPoissonTotalVariation
    (N L : ℕ) : ℝ :=
  natTotalVariation
    (fullDyadicStartLaw N L)
    (targetPoissonLaw N L)

/-- The Corollary 13.9 total variation distance is nonnegative. -/
theorem fullDyadicTargetPoissonTotalVariation_nonneg
    (N L : ℕ) :
    0 ≤ fullDyadicTargetPoissonTotalVariation N L :=
  natTotalVariation_nonneg _ _

end

end SectionThirteenCritical
end PaperC
