import PaperCV282.SaddleBranch

/-!
# Asymptotics of the upper branch at a free prime cutoff

The statements quantify over every large nu, independently of how nu=H/w
is later chosen. They therefore remain usable before specializing w to a saddle.
-/

namespace PaperC.V282.SaddleBranchAsymptotics

open Set Filter Topology SaddleBranch

theorem tendsto_log_div_upperSaddleBranch :
    Tendsto (fun nu => Real.log nu / upperSaddleBranch nu) atTop (𝓝 1) := by
  have hsmall : Tendsto (fun nu =>
      Real.log (upperSaddleBranch nu) / upperSaddleBranch nu) atTop (𝓝 0) := by
    simpa only [Function.comp_def, pow_one, one_mul, add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
        tendsto_upperSaddleBranch_atTop
  apply (show Tendsto (fun nu =>
    1 - Real.log (upperSaddleBranch nu) / upperSaddleBranch nu) atTop (𝓝 1) by
      simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hsmall).congr'
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with nu hnu
  rw [log_upperSaddleBranch_identity hnu]
  field_simp [ne_of_gt (upperSaddleBranch_pos hnu)]

theorem tendsto_upperSaddleBranch_div_log :
    Tendsto (fun nu => upperSaddleBranch nu / Real.log nu) atTop (𝓝 1) := by
  simpa only [inv_div, inv_one] using
    tendsto_log_div_upperSaddleBranch.inv₀ (by norm_num : (1 : ℝ) ≠ 0)

theorem upperSaddleBranch_refined_identity {nu : ℝ}
    (hnu : Real.exp 1 ≤ nu) (hnuone : 1 < nu) :
    upperSaddleBranch nu - Real.log nu - Real.log (Real.log nu) =
      Real.log (upperSaddleBranch nu / Real.log nu) := by
  rw [Real.log_div (ne_of_gt (upperSaddleBranch_pos hnu))
    (ne_of_gt (Real.log_pos hnuone))]
  have h := log_upperSaddleBranch_identity hnu
  linarith

theorem tendsto_upperSaddleBranch_second_order :
    Tendsto (fun nu => upperSaddleBranch nu - Real.log nu - Real.log (Real.log nu))
      atTop (𝓝 0) := by
  apply (show Tendsto (fun nu => Real.log (upperSaddleBranch nu / Real.log nu))
      atTop (𝓝 0) by
        simpa only [Function.comp_def, Real.log_one] using
          (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
            tendsto_upperSaddleBranch_div_log).congr'
  filter_upwards [eventually_ge_atTop (Real.exp 1), eventually_gt_atTop (1 : ℝ)]
    with nu hnu hnuone
  exact (upperSaddleBranch_refined_identity hnu hnuone).symm

theorem log_le_upperSaddleBranch {nu : ℝ} (hnu : Real.exp 1 ≤ nu) :
    Real.log nu ≤ upperSaddleBranch nu := by
  rw [log_upperSaddleBranch_identity hnu]
  linarith [Real.log_nonneg (upperSaddleBranch_spec hnu).1]

theorem upperSaddleBranch_le_two_log_eventually :
    ∀ᶠ nu : ℝ in atTop, upperSaddleBranch nu ≤ 2 * Real.log nu := by
  filter_upwards [tendsto_upperSaddleBranch_div_log.eventually
      (gt_mem_nhds (by norm_num : (1 : ℝ) < 2)), eventually_gt_atTop (1 : ℝ)]
    with nu hratio hnu
  exact (div_le_iff₀ (Real.log_pos hnu)).1 hratio.le

end PaperC.V282.SaddleBranchAsymptotics
