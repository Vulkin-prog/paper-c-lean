import PaperCV282.PrimeEulerUniform
import PaperCV282.SaddleScales

/-!
# Weighted Euler products at the actual implicit cutoff saddles

The scalar scale conditions used in the uniform weighted-prime theorem are
proved here for every fixed positive saddle multiplier a, including a=1 and
a=2. The only remaining arithmetic premise is the source-form PNT.
-/

namespace PaperC.V282.PrimeEulerSaddle

open Set Filter Topology PrimeEulerPNT PrimeEulerUniform PrimeEulerRankin
open SaddleBranch SaddleParameters SaddleAsymptotics SaddleScales ExponentialIntegral

noncomputable section

/-- The genuine Rankin tilt at the implicit saddle. -/
def saddleTilt (a H : ℝ) : ℝ := saddleParameter a H / saddleCutoff a H

theorem tendsto_saddleCutoff_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (saddleCutoff a) atTop atTop := by
  exact (tendsto_saddleCostParam_atTop.comp (tendsto_saddleParameter_atTop ha)).const_mul_atTop ha

theorem saddleTilt_pos {a H : ℝ} (ha : 0 < a) (hH : saddleThreshold a ≤ H) :
    0 < saddleTilt a H := by
  exact div_pos (by linarith [(saddleParameter_spec ha hH).1, saddleParameterBase_ge_two])
    (saddleCutoff_pos ha hH)

theorem saddleTilt_link {a H : ℝ} (ha : 0 < a) (hH : saddleThreshold a ≤ H) :
    saddleTilt a H * saddleCutoff a H = upperSaddleBranch (saddleNu a H) := by
  rw [saddleTilt, div_mul_cancel₀ _ (saddleCutoff_pos ha hH).ne']
  exact (upperSaddleBranch_div_saddleCutoff ha hH).symm

theorem tendsto_saddleTilt_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (saddleTilt a) atTop (𝓝 0) := by
  have hnum : Tendsto (fun H => saddleParameter a H / Real.exp (saddleParameter a H))
      atTop (𝓝 0) := by
    simpa only [pow_one, Pi.inv_apply, inv_div, Function.comp_def] using
      ((Real.tendsto_exp_div_pow_atTop 1).inv_tendsto_atTop.comp (tendsto_saddleParameter_atTop ha))
  have hfactor := tendsto_saddleCostFactor.comp (tendsto_saddleParameter_atTop ha)
  have hden : Tendsto (fun H => a * saddleCostFactor (saddleParameter a H)) atTop (𝓝 a) := by
    simpa only [Function.comp_def, mul_one] using hfactor.const_mul a
  apply (show Tendsto (fun H =>
    (saddleParameter a H / Real.exp (saddleParameter a H)) /
      (a * saddleCostFactor (saddleParameter a H))) atTop (𝓝 0) by
        have h := hnum.div hden ha.ne'
        simp only [zero_div] at h
        exact h.congr (fun _ => rfl)).congr
  intro H
  dsimp [saddleTilt, saddleCutoff]
  rw [saddleCostParam_eq_exp_mul_factor]
  ring

theorem log_saddleCutoff_identity {a H : ℝ} (ha : 0 < a) (hH : saddleThreshold a ≤ H) :
    Real.log (saddleCutoff a H) = Real.log a + saddleParameter a H +
      Real.log (saddleCostFactor (saddleParameter a H)) := by
  rw [saddleCutoff, saddleCostParam_eq_exp_mul_factor,
    Real.log_mul ha.ne' (mul_pos (Real.exp_pos _)
      (saddleCostFactor_pos (saddleParameter_spec ha hH).1)).ne',
    Real.log_mul (Real.exp_ne_zero _) (saddleCostFactor_pos (saddleParameter_spec ha hH).1).ne',
    Real.log_exp]
  ring

theorem tendsto_log_saddleCutoff_div_nu {a : ℝ} (ha : 0 < a) :
    Tendsto (fun H => Real.log (saddleCutoff a H) / saddleNu a H) atTop (𝓝 0) := by
  have hconst := (tendsto_const_nhds (x := Real.log a)).div_atTop (tendsto_saddleNu_atTop ha)
  have hfactor : Tendsto (fun H => Real.log (saddleCostFactor (saddleParameter a H)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      tendsto_log_saddleCostFactor.comp (tendsto_saddleParameter_atTop ha)
  have hrest := hfactor.div_atTop (tendsto_saddleNu_atTop ha)
  apply (show Tendsto (fun H => Real.log a / saddleNu a H +
    saddleParameter a H / saddleNu a H +
    Real.log (saddleCostFactor (saddleParameter a H)) / saddleNu a H) atTop (𝓝 0) by
      simpa only [add_zero] using (hconst.add (tendsto_saddleParameter_div_nu ha)).add hrest).congr'
  filter_upwards [eventually_ge_atTop (saddleThreshold a)] with H hH
  rw [log_saddleCutoff_identity ha hH, add_div, add_div]

theorem tendsto_log_saddleTilt_div_nu {a : ℝ} (ha : 0 < a) :
    Tendsto (fun H => |Real.log (saddleTilt a H)| / saddleNu a H) atTop (𝓝 0) := by
  have hlogu : Tendsto (fun H => Real.log (saddleParameter a H) / saddleParameter a H)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, pow_one, one_mul, add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
        (tendsto_saddleParameter_atTop ha)
  have hlogunum : Tendsto (fun H => Real.log (saddleParameter a H) / saddleNu a H)
      atTop (𝓝 0) := by
    apply (show Tendsto (fun H =>
      (Real.log (saddleParameter a H) / saddleParameter a H) *
        (saddleParameter a H / saddleNu a H)) atTop (𝓝 0) by
          simpa only [mul_zero] using hlogu.mul (tendsto_saddleParameter_div_nu ha)).congr'
    filter_upwards [eventually_ge_atTop (saddleThreshold a)] with H hH
    have hu : saddleParameter a H ≠ 0 := by
      linarith [(saddleParameter_spec ha hH).1, saddleParameterBase_ge_two]
    field_simp [hu]
  have hsigned : Tendsto (fun H => Real.log (saddleTilt a H) / saddleNu a H)
      atTop (𝓝 0) := by
    apply (show Tendsto (fun H => Real.log (saddleParameter a H) / saddleNu a H -
      Real.log (saddleCutoff a H) / saddleNu a H) atTop (𝓝 0) by
        simpa only [sub_zero] using hlogunum.sub (tendsto_log_saddleCutoff_div_nu ha)).congr'
    filter_upwards [eventually_ge_atTop (saddleThreshold a)] with H hH
    have hu : saddleParameter a H ≠ 0 := by
      linarith [(saddleParameter_spec ha hH).1, saddleParameterBase_ge_two]
    rw [saddleTilt, Real.log_div hu (saddleCutoff_pos ha hH).ne', sub_div]
  apply (show Tendsto (fun H => |Real.log (saddleTilt a H) / saddleNu a H|)
    atTop (𝓝 0) by simpa only [abs_zero] using hsigned.abs).congr'
  filter_upwards [(tendsto_saddleNu_atTop ha).eventually (eventually_gt_atTop (0 : ℝ))] with H hH
  rw [abs_div, abs_of_pos hH]

/-- The weighted prime asymptotic at either actual cutoff saddle. -/
theorem weighted_prime_sum_saddle_error_of_pnt
    (hPNT : PrimeNumberTheoremRemainder) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun H =>
      (rankinPrimeSum ⌊Real.exp (saddleCutoff a H)⌋₊ (saddleTilt a H) -
        exponentialIntegral (upperSaddleBranch (saddleNu a H))) / saddleNu a H)
      atTop (𝓝 0) := by
  apply weighted_prime_sum_normalized_error_of_pnt hPNT (tendsto_saddleCutoff_atTop ha)
    (tendsto_saddleNu_atTop ha) (tendsto_saddleTilt_zero ha) _
    (tendsto_log_saddleTilt_div_nu ha)
  · filter_upwards [eventually_ge_atTop (saddleThreshold a)] with H hH
    exact saddleTilt_link ha hH
  · filter_upwards [eventually_ge_atTop (saddleThreshold a)] with H hH
    exact saddleTilt_pos ha hH

/-- The actual logarithm of the Euler product is Ei(u(nu))+o(nu) at either saddle.
Only the ordinary PNT remainder remains a premise. -/
theorem log_euler_saddle_error_of_pnt
    (hPNT : PrimeNumberTheoremRemainder) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun H =>
      (rankinLogSum ⌊Real.exp (saddleCutoff a H)⌋₊ (saddleTilt a H) -
        exponentialIntegral (upperSaddleBranch (saddleNu a H))) / saddleNu a H)
      atTop (𝓝 0) := by
  apply log_euler_normalized_error_of_pnt hPNT (tendsto_saddleCutoff_atTop ha)
    (tendsto_saddleNu_atTop ha) (tendsto_saddleTilt_zero ha) _
    (tendsto_log_saddleTilt_div_nu ha)
  · filter_upwards [eventually_ge_atTop (saddleThreshold a)] with H hH
    exact saddleTilt_link ha hH
  · filter_upwards [eventually_ge_atTop (saddleThreshold a)] with H hH
    exact saddleTilt_pos ha hH

end
end PaperC.V282.PrimeEulerSaddle
