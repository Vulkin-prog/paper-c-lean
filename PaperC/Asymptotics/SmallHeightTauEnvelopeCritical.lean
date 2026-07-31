import PaperC.Asymptotics.CorrectedDefectEnvelope
import PaperC.Asymptotics.ExpSqrtLog
import PaperC.Asymptotics.SmallHeightComponentEnvelopeCritical
import PaperC.Combinatorics.SmallHeightTauEnvelope

/-!
# The small-height residual-exponent envelope in the critical window

The finite envelope for `τ` is the sum of the largest corrected defect and
the small-height residual-component envelope.  Consequently its fourth
power factors as

`4^tauEnvelope = 4^correctedEnvelope * 4^componentEnvelope`.

Both factors are already uniformly subpolynomial in the critical run-length
window, so the multiplicative closure of `UniformSubpolynomialOn` gives the
same conclusion for the complete `τ` envelope.
-/

namespace PaperC
namespace SmallHeightTauEnvelopeCritical

open SmallHeightResidualComponentEnvelope
open SmallHeightTauEnvelope

/--
The complete fourth-power residual-exponent envelope for Proposition 7.4 is
uniformly `N^o(1)` in every fixed critical run-length window.
-/
theorem four_pow_smallHeightTauEnvelope_uniformSubpolynomial
    {C : ℝ} (hC : 0 ≤ C) (A : ℕ) :
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun N L =>
        (((4 ^ smallHeightTauEnvelope A N L : ℕ) : ℝ))) := by
  have hcorrected :
      UniformSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L =>
          (((4 ^
            CorrectedDefectEnvelope.maxCanonicalCorrectedDefectCount
              A N L : ℕ) : ℝ))) :=
    CorrectedDefectEnvelope.four_pow_maxCanonicalCorrectedDefectCount_uniformSubpolynomial
      hC A
  have hcomponents :
      UniformSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun _ L =>
          (((4 ^ smallHeightResidualComponentEnvelope L : ℕ) : ℝ))) :=
    SmallHeightComponentEnvelopeCritical.four_pow_smallHeightResidualComponentEnvelope_uniformSubpolynomial
      hC
  have hproduct :=
    ExpSqrtLog.uniformSubpolynomialOn_mul
      hcorrected hcomponents
  simpa only [smallHeightTauEnvelope, pow_add, Nat.cast_mul] using
    hproduct

end SmallHeightTauEnvelopeCritical
end PaperC
