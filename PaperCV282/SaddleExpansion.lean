import PaperCV282.SaddleAsymptotics

/-!
# The second-order constants of both implicit cutoff scales

For every fixed positive a, the uniquely defined solution V=a D(H/V)
satisfies V^2/H = (a/2)(log H+log log H-log(2a)-2)+o(1).
This supplies the precise constants -log(2)-2 and -log(4)-2 in the
hard and soft specializations. The weighted prime-number calculation is separate.
-/

namespace PaperC.V282.SaddleExpansion

open Set Filter Topology SaddleBranch SaddleParameters ExponentialIntegral SaddleAsymptotics

noncomputable section

theorem tendsto_log_div_saddleParameter {a : ℝ} (ha : 0 < a) :
    Tendsto (fun H => Real.log H / saddleParameter a H) atTop (𝓝 2) := by
  have hu := tendsto_saddleParameter_atTop ha
  have hlog : Tendsto (fun H => Real.log (saddleParameter a H) / saddleParameter a H)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, pow_one, one_mul, add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hu
  have hconstant : Tendsto (fun H => Real.log a / saddleParameter a H) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hu
  have hfactor : Tendsto (fun H =>
      Real.log (saddleCostFactor (saddleParameter a H)) / saddleParameter a H) atTop (𝓝 0) :=
    (tendsto_log_saddleCostFactor.comp hu).div_atTop hu
  have hlimit := (((tendsto_const_nhds (x := (2 : ℝ))).sub hlog).add hconstant).add hfactor
  apply (show Tendsto (fun H =>
    2 - Real.log (saddleParameter a H) / saddleParameter a H +
      Real.log a / saddleParameter a H +
      Real.log (saddleCostFactor (saddleParameter a H)) / saddleParameter a H)
        atTop (𝓝 2) by simpa only [sub_zero, add_zero] using hlimit).congr'
  filter_upwards [eventually_ge_atTop (saddleThreshold a)] with H hH
  have huone := (saddleParameter_spec ha hH).1
  have hune : saddleParameter a H ≠ 0 := by
    have := saddleParameterBase_ge_two
    linarith
  rw [log_saddleParameter_identity ha hH]
  field_simp [hune]

theorem tendsto_saddleParameter_div_log {a : ℝ} (ha : 0 < a) :
    Tendsto (fun H => saddleParameter a H / Real.log H) atTop (𝓝 (1 / 2)) := by
  simpa only [inv_div, invOf_eq_inv, one_div] using
    (tendsto_log_div_saddleParameter ha).inv₀ (by norm_num : (2 : ℝ) ≠ 0)

theorem saddleParameter_refined_identity {a H : ℝ} (ha : 0 < a)
    (hH : saddleThreshold a ≤ H) (hHone : 1 < H) :
    saddleParameter a H - (1 / 2 : ℝ) *
      (Real.log H + Real.log (Real.log H) - Real.log (2 * a)) =
      (1 / 2 : ℝ) * (Real.log (saddleParameter a H / Real.log H) + Real.log 2 -
        Real.log (saddleCostFactor (saddleParameter a H))) := by
  have hupos : 0 < saddleParameter a H := by
    have := (saddleParameter_spec ha hH).1
    linarith [saddleParameterBase_ge_two]
  rw [Real.log_div (ne_of_gt hupos) (ne_of_gt (Real.log_pos hHone)),
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt ha)]
  have hid := log_saddleParameter_identity ha hH
  linarith

theorem tendsto_saddleParameter_second_order {a : ℝ} (ha : 0 < a) :
    Tendsto (fun H => saddleParameter a H - (1 / 2 : ℝ) *
      (Real.log H + Real.log (Real.log H) - Real.log (2 * a))) atTop (𝓝 0) := by
  have hratio := (Real.continuousAt_log (by norm_num : (1 / 2 : ℝ) ≠ 0)).tendsto.comp
    (tendsto_saddleParameter_div_log ha)
  have hfactor := tendsto_log_saddleCostFactor.comp (tendsto_saddleParameter_atTop ha)
  have hlim := ((hratio.add_const (Real.log 2)).sub hfactor).const_mul (1 / 2 : ℝ)
  have hlogtwo : Real.log (1 / 2 : ℝ) + Real.log 2 = 0 := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),
      Real.log_one]
    ring
  apply (show Tendsto (fun H => (1 / 2 : ℝ) *
    (Real.log (saddleParameter a H / Real.log H) + Real.log 2 -
      Real.log (saddleCostFactor (saddleParameter a H)))) atTop (𝓝 0) by
        simpa only [Function.comp_def, hlogtwo, sub_zero, mul_zero] using hlim).congr'
  filter_upwards [eventually_ge_atTop (saddleThreshold a), eventually_gt_atTop (1 : ℝ)]
    with H hH hHone
  exact (saddleParameter_refined_identity ha hH hHone).symm

theorem saddleCutoff_square_div_identity {a H : ℝ} (ha : 0 < a)
    (hH : saddleThreshold a ≤ H) :
    saddleCutoff a H ^ 2 / H =
      a * (saddleParameter a H - normalizedExponentialIntegral (saddleParameter a H)) := by
  let u := saddleParameter a H
  have hupos : 0 < u := by
    have := (saddleParameter_spec ha hH).1
    change 0 < saddleParameter a H
    linarith [saddleParameterBase_ge_two]
  have hGpos : 0 < saddleCostParam u :=
    (mul_pos_iff_of_pos_left ha).1 (saddleCutoff_pos ha hH)
  have hFpos : 0 < saddleRatio u := div_pos (Real.exp_pos _) hupos
  have hheight : H = a * saddleRatio u * saddleCostParam u :=
    (saddleParameter_spec ha hH).2.symm
  change (a * saddleCostParam u) ^ 2 / H =
    a * (u - normalizedExponentialIntegral u)
  rw [hheight]
  calc
    _ = a * saddleCostParam u / saddleRatio u := by
      field_simp [ne_of_gt ha, ne_of_gt hGpos, ne_of_gt hFpos]
    _ = _ := by
      unfold saddleCostParam saddleRatio normalizedExponentialIntegral
      field_simp [ne_of_gt hupos, Real.exp_ne_zero u]

theorem saddle_cutoff_second_order {a : ℝ} (ha : 0 < a) :
    Tendsto (fun H => saddleCutoff a H ^ 2 / H - (a / 2) *
      (Real.log H + Real.log (Real.log H) - Real.log (2 * a) - 2)) atTop (𝓝 0) := by
  have hu := tendsto_saddleParameter_second_order ha
  have hei := tendsto_normalizedExponentialIntegral.comp (tendsto_saddleParameter_atTop ha)
  have hlimit := (hu.sub (hei.sub_const 1)).const_mul a
  apply (show Tendsto (fun H => a *
    ((saddleParameter a H - (1 / 2 : ℝ) *
      (Real.log H + Real.log (Real.log H) - Real.log (2 * a))) -
        (normalizedExponentialIntegral (saddleParameter a H) - 1)))
      atTop (𝓝 0) by simpa only [Function.comp_def, sub_self, mul_zero] using hlimit).congr'
  filter_upwards [eventually_ge_atTop (saddleThreshold a)] with H hH
  rw [saddleCutoff_square_div_identity ha hH]
  ring

theorem hard_saddle_second_order :
    Tendsto (fun H => saddleCutoff 1 H ^ 2 / H - (1 / 2 : ℝ) *
      (Real.log H + Real.log (Real.log H) - Real.log 2 - 2)) atTop (𝓝 0) := by
  simpa only [mul_one] using saddle_cutoff_second_order (by norm_num : (0 : ℝ) < 1)

theorem soft_saddle_second_order :
    Tendsto (fun H => saddleCutoff 2 H ^ 2 / H -
      (Real.log H + Real.log (Real.log H) - Real.log 4 - 2)) atTop (𝓝 0) := by
  simpa only [show (2 : ℝ) * 2 = 4 by norm_num, div_self (by norm_num : (2 : ℝ) ≠ 0),
    one_mul] using saddle_cutoff_second_order (by norm_num : (0 : ℝ) < 2)

end

end PaperC.V282.SaddleExpansion
