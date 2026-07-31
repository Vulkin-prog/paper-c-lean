import PaperC.Asymptotics.ExpLogDivLogLog
import PaperC.Asymptotics.LinearPower

/-!
# Critical-window size of the residual certificate envelope

The effective one-channel estimate obtained from Lemmas 7.1 and 7.2 is

`2N · exp(3584 (L+1) / log₂(L+1))`.

This module verifies, with the repository's uniform quantifier convention,
that this envelope is `N^(1+o_C(1))` throughout the literal run-length
window.
-/

namespace PaperC

/-- The explicit real envelope for one nontrivial residual channel. -/
noncomputable def residualCertificateChannelEnvelope
    (N L : ℕ) : ℝ :=
  2 * (N : ℝ) *
    Real.exp
      (3584 * (L + 1 : ℕ) /
        (Nat.log 2 (L + 1) : ℝ))

/--
The effective fixed-channel certificate bound is uniformly
`N^(1+o_C(1))`.
-/
theorem residualCertificateChannelEnvelope_uniformLinear
    {C : ℝ} (hC : 0 ≤ C) :
    UniformLinearSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      residualCertificateChannelEnvelope := by
  have hexp :
      UniformSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun _ L =>
          Real.exp
            (3584 * (L + 1 : ℕ) /
              (Nat.log 2 (L + 1) : ℝ))) :=
    PaperC.ExpLogDivLogLog.criticalRunWindow_exp_height_div_natLog_uniformSubpolynomial
      hC (by norm_num)
  have hq :
      UniformSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun _ L =>
          2 *
            Real.exp
              (3584 * (L + 1 : ℕ) /
                (Nat.log 2 (L + 1) : ℝ))) :=
    ExpSqrtLog.uniformSubpolynomialOn_const_mul 2 hexp
  apply UniformLinear.of_linear_mul_subpolynomial hq
  refine ⟨0, ?_⟩
  intro N _hN L _hwindow
  have hqNonneg :
      0 ≤
        2 *
          Real.exp
            (3584 * (L + 1 : ℕ) /
              (Nat.log 2 (L + 1) : ℝ)) := by
    positivity
  have henvNonneg :
      0 ≤ residualCertificateChannelEnvelope N L := by
    unfold residualCertificateChannelEnvelope
    positivity
  rw [abs_of_nonneg henvNonneg, abs_of_nonneg hqNonneg]
  unfold residualCertificateChannelEnvelope
  ring_nf
  exact le_rfl

end PaperC
