import PaperCPrel8.RoughKernelThreshold

/-! # Saddle-scale absorption for the private-pivot cloud estimate

The key ratio nu^2/(u V) diverges at the literal hard saddle. This justifies
absorbing a prefactor whose logarithm is at most V+O(log H).
-/
namespace PaperC.Prel8.RegularCloudSaddle
open Filter Topology V282.SaddleParameters V282.SaddleScales V282.SaddleAsymptotics
open V282.SaddleBranch V282.SaddlePoissonScales V282.PrimeEulerSaddle RoughKernelThreshold
noncomputable section

/-- Exact hard-saddle expression for the ratio used in G.3. -/
theorem squared_nu_ratio {H : ℝ} (hH : saddleThreshold 1≤H) :
    saddleNu 1 H^2/(saddleParameter 1 H*saddleCutoff 1 H) =
      (Real.exp (saddleParameter 1 H)/saddleParameter 1 H^3)/saddleCostFactor (saddleParameter 1 H) := by
  have hu := (saddleParameter_spec (by norm_num : (0:ℝ)<1) hH).1
  have hu0 : saddleParameter 1 H≠0 := by linarith [saddleParameterBase_ge_two]
  rw [saddleNu,div_saddleCutoff_eq_ratio (by norm_num) hH]
  rw [saddleCutoff,saddleCostParam_eq_exp_mul_factor]
  unfold saddleRatio
  field_simp [hu0,Real.exp_ne_zero _]

/-- The cloud regularity exponent dominates the entire saddle cutoff. -/
theorem squared_nu_ratio_tendsto :
    Tendsto (fun H ↦ saddleNu 1 H^2/(saddleParameter 1 H*saddleCutoff 1 H)) atTop atTop := by
  have hu := tendsto_saddleParameter_atTop (by norm_num : (0:ℝ)<1)
  have hf : Tendsto (fun H ↦ (saddleCostFactor (saddleParameter 1 H))⁻¹) atTop (𝓝 1) := by
    simpa only [inv_one,Function.comp_def] using (tendsto_saddleCostFactor.comp hu).inv₀ (by norm_num : (1:ℝ)≠0)
  have h := ((Real.tendsto_exp_div_pow_atTop 3).comp hu).atTop_mul_pos (by norm_num : (0:ℝ)<1) hf
  apply h.congr'
  filter_upwards [eventually_ge_atTop (saddleThreshold 1)] with H hH
  simpa only [div_eq_mul_inv,Function.comp_def] using (squared_nu_ratio hH).symm

/-- The unnormalized private-pivot exponent itself diverges. -/
theorem squared_nu_div_parameter_tendsto :
    Tendsto (fun H ↦ saddleNu 1 H^2/saddleParameter 1 H) atTop atTop := by
  have h := squared_nu_ratio_tendsto.atTop_mul_atTop₀ (tendsto_saddleCutoff_atTop (by norm_num : (0:ℝ)<1))
  apply h.congr'
  filter_upwards [eventually_ge_atTop (saddleThreshold 1)] with H hH
  have hv := saddleCutoff_pos (by norm_num : (0:ℝ)<1) hH
  field_simp [hv.ne']

/-- The paper's last regular-cloud error tends to zero for every c,theta>0. -/
theorem regularity_error_tendsto (c theta : ℝ) (hc : 0<c) (htheta : 0<theta) :
    Tendsto (fun H ↦ Real.exp (-c*theta*saddleNu 1 H^2/(4*saddleParameter 1 H))) atTop (𝓝 0) := by
  have h := squared_nu_div_parameter_tendsto.const_mul_atTop (show 0<c*theta/4 by positivity)
  apply (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h)).congr
  intro H
  dsimp only [Function.comp_def]
  congr 1
  ring

/-- Logarithmic factors are negligible relative to the hard cutoff. -/
theorem log_div_cutoff_tendsto :
    Tendsto (fun H ↦ Real.log H/saddleCutoff 1 H) atTop (𝓝 0) := by
  have h := (tendsto_log_div_saddleNu (by norm_num : (0:ℝ)<1)).mul
    (tendsto_nu_div_saddleCutoff (by norm_num : (0:ℝ)<1))
  apply (show Tendsto (fun H ↦ (Real.log H/saddleNu 1 H)*(saddleNu 1 H/saddleCutoff 1 H)) atTop (𝓝 0) by simpa using h).congr'
  filter_upwards [eventually_ge_atTop (saddleThreshold 1)] with H hH
  have hv := saddleCutoff_pos (by norm_num : (0:ℝ)<1) hH
  have hn : saddleNu 1 H≠0 := ne_of_gt (div_pos ((saddleThreshold_pos (by norm_num : (0:ℝ)<1)).trans_le hH) hv)
  field_simp [hn]

/-- Every prefactor bounded by exp(V+C log H) is negligible on the cloud scale. -/
theorem log_prefactor_ratio_tendsto (C : ℝ) :
    Tendsto (fun H ↦ (saddleCutoff 1 H+C*Real.log H)/(saddleNu 1 H^2/saddleParameter 1 H)) atTop (𝓝 0) := by
  have h := ((log_div_cutoff_tendsto.const_mul C).const_add 1).mul squared_nu_ratio_tendsto.inv_tendsto_atTop
  apply (show Tendsto (fun H ↦ (1+C*(Real.log H/saddleCutoff 1 H))*(saddleNu 1 H^2/(saddleParameter 1 H*saddleCutoff 1 H))⁻¹) atTop (𝓝 0) by simpa using h).congr'
  filter_upwards [eventually_ge_atTop (saddleThreshold 1)] with H hH
  have hv := saddleCutoff_pos (by norm_num : (0:ℝ)<1) hH
  field_simp [hv.ne']

/-- Uniform absorption of all admissible prefactors, before choosing the cloud size. -/
theorem prefactor_absorption_eventually (c theta C : ℝ) (hc : 0<c) (htheta : 0<theta) :
    ∀ᶠ H : ℝ in atTop, ∀ B : ℝ, 0<B → Real.log B≤saddleCutoff 1 H+C*Real.log H →
      B*Real.exp (-c*theta*saddleNu 1 H^2/(2*saddleParameter 1 H)) ≤
        Real.exp (-c*theta*saddleNu 1 H^2/(4*saddleParameter 1 H)) := by
  filter_upwards [eventually_ge_atTop (saddleThreshold 1),
    (log_prefactor_ratio_tendsto C).eventually (gt_mem_nhds (show 0<c*theta/4 by positivity))] with H hH hratio
  intro B hB hlog
  have hu := (saddleParameter_spec (by norm_num : (0:ℝ)<1) hH).1
  have hup : 0<saddleParameter 1 H := by linarith [saddleParameterBase_ge_two]
  have hnu : 0<saddleNu 1 H := div_pos ((saddleThreshold_pos (by norm_num : (0:ℝ)<1)).trans_le hH)
    (saddleCutoff_pos (by norm_num) hH)
  have hh := (div_lt_iff₀ (show 0<saddleNu 1 H^2/saddleParameter 1 H by positivity)).mp hratio
  rw [← Real.exp_log hB,← Real.exp_add,Real.exp_le_exp]
  have he : c*theta/4*(saddleNu 1 H^2/saddleParameter 1 H)+
      (-c*theta*saddleNu 1 H^2/(2*saddleParameter 1 H)) =
      -c*theta*saddleNu 1 H^2/(4*saddleParameter 1 H) := by ring
  linarith

end
end PaperC.Prel8.RegularCloudSaddle
