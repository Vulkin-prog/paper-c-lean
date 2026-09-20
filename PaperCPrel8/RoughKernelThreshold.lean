import PaperCPrel8.RoughKernelSaddle
import PaperCV282.SaddlePoissonScales

/-! # The literal stronger-good-set threshold of Appendix G

The real threshold is exp(theta H/u). Flooring it only encodes its comparison
with an integer kernel. Its power under the Rankin tilt is controlled exactly.
-/
namespace PaperC.Prel8.RoughKernelThreshold
open V282.SaddleParameters V282.SaddleScales V282.SaddleAsymptotics
open V282.PrimeEulerFreeScales V282.SaddleCutoffAdmissibility
open Set Filter Topology
noncomputable section

def threshold (theta H : ℝ) : ℝ := Real.exp (theta * H / saddleParameter 1 H)
def tilt (H : ℝ) : ℝ := freeCutoffTilt H (saddleCutoff 1 H)

/-- The free-cutoff tilt at the hard saddle is exactly u/V. -/
theorem tilt_eq {H : ℝ} (hH : saddleThreshold 1 ≤ H) :
    tilt H = saddleParameter 1 H / saddleCutoff 1 H := by
  unfold tilt freeCutoffTilt
  rw [upperSaddleBranch_div_saddleCutoff (by norm_num) hH]

/-- Positivity of the literal tilt. -/
theorem tilt_pos {H : ℝ} (hH : saddleThreshold 1 ≤ H) : 0 < tilt H := by
  rw [tilt_eq hH]
  have hu := (saddleParameter_spec (by norm_num : (0:ℝ)<1) hH).1
  exact div_pos (by linarith [saddleParameterBase_ge_two]) (saddleCutoff_pos (by norm_num) hH)

/-- A polynomial bound suffices for the reciprocal tilt. -/
theorem inv_tilt_le_height {H : ℝ} (hH : saddleThreshold 1 ≤ H) : 1 / tilt H ≤ H := by
  have hv := saddleCutoff_pos (by norm_num : (0:ℝ)<1) hH
  have hu := (saddleParameter_spec (by norm_num : (0:ℝ)<1) hH).1
  have hu1 : 1 ≤ saddleParameter 1 H := by linarith [saddleParameterBase_ge_two]
  have hdom := saddleCutoff_domain (by norm_num : (0:ℝ)<1) hH
  have he : (1:ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hvH : saddleCutoff 1 H ≤ H := by simpa only [one_mul] using (le_div_iff₀ hv).mp (he.trans hdom)
  rw [tilt_eq hH, one_div_div]
  exact (div_le_self hv.le hu1).trans hvH

/-- Exact cancellation of u in the tilted real threshold. -/
theorem threshold_power {H : ℝ} (hH : saddleThreshold 1 ≤ H) (theta : ℝ) :
    threshold theta H ^ tilt H = Real.exp (theta * saddleNu 1 H) := by
  have hu := (saddleParameter_spec (by norm_num : (0:ℝ)<1) hH).1
  have hu0 : saddleParameter 1 H ≠ 0 := by linarith [saddleParameterBase_ge_two]
  rw [threshold, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, tilt_eq hH]
  congr 1
  unfold saddleNu
  field_simp

/-- The actual rounded threshold contributes at most exp(theta nu). -/
theorem floor_threshold_power {H : ℝ} (hH : saddleThreshold 1 ≤ H) (theta : ℝ) :
    (⌊threshold theta H⌋₊ : ℝ) ^ tilt H ≤ Real.exp (theta * saddleNu 1 H) := by
  rw [← threshold_power hH theta]
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (Real.exp_pos _).le) (tilt_pos hH).le

/-- Explicit polynomial prefactor for the literal T_M. -/
theorem threshold_factor {H theta : ℝ} (hH : saddleThreshold 1 ≤ H) (htheta : 0 ≤ theta) :
    1 + (⌊threshold theta H⌋₊ : ℝ) ^ tilt H / tilt H ≤
      (1 + H) * Real.exp (theta * saddleNu 1 H) := by
  have hHp := (saddleThreshold_pos (by norm_num : (0:ℝ)<1)).trans_le hH
  have hnu : 0 ≤ saddleNu 1 H := div_nonneg hHp.le (saddleCutoff_pos (by norm_num) hH).le
  have he : 1 ≤ Real.exp (theta * saddleNu 1 H) := Real.one_le_exp (mul_nonneg htheta hnu)
  have hp := div_le_div_of_nonneg_right (floor_threshold_power hH theta) (tilt_pos hH).le
  have hi := mul_le_mul_of_nonneg_left (inv_tilt_le_height hH) (Real.exp_pos (theta * saddleNu 1 H)).le
  rw [mul_one_div] at hi
  nlinarith

/-- The threshold is subpolynomial: log T/H tends to zero. -/
theorem log_threshold_div_height (theta : ℝ) :
    Tendsto (fun H ↦ Real.log (threshold theta H) / H) atTop (𝓝 0) := by
  have h := ((tendsto_const_nhds (x := theta)).div_atTop
    (tendsto_saddleParameter_atTop (by norm_num : (0:ℝ)<1)))
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with H hH
  simp only [threshold, Real.log_exp]
  field_simp

/-- For positive theta, T_M eventually exceeds the real conditioning cutoff. -/
theorem threshold_gt_cutoff (theta : ℝ) (htheta : 0 < theta) :
    ∀ᶠ H : ℝ in atTop, Real.exp (saddleCutoff 1 H) < threshold theta H := by
  filter_upwards [eventually_ge_atTop (saddleThreshold 1),
    (tendsto_saddleParameter_div_nu (by norm_num : (0:ℝ)<1)).eventually (gt_mem_nhds htheta)] with H hH hr
  have hv := saddleCutoff_pos (by norm_num : (0:ℝ)<1) hH
  have hu := (saddleParameter_spec (by norm_num : (0:ℝ)<1) hH).1
  have hup : 0 < saddleParameter 1 H := by linarith [saddleParameterBase_ge_two]
  have hHp := (saddleThreshold_pos (by norm_num : (0:ℝ)<1)).trans_le hH
  have hnup : 0 < saddleNu 1 H := div_pos hHp hv
  have hh := (div_lt_iff₀ hnup).mp hr
  rw [threshold, Real.exp_lt_exp]
  apply (lt_div_iff₀ hup).mpr
  unfold saddleNu at hh
  have hh' := (lt_div_iff₀ hv).mp (by simpa only [mul_div_assoc] using hh :
    saddleParameter 1 H < theta * H / saddleCutoff 1 H)
  nlinarith

end
end PaperC.Prel8.RoughKernelThreshold
