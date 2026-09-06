import PaperCV282.SaddleExpansion
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Leading scales and the relative size of the two saddles

These are consequences of the actual roots and their internally proved
expansions. In particular the small error scale H/V dominates log H.
-/

namespace PaperC.V282.SaddleScales

open Set Filter Topology SaddleBranch SaddleParameters ExponentialIntegral
open SaddleAsymptotics SaddleExpansion

noncomputable section

def saddleNu (a H : ℝ) : ℝ := H / saddleCutoff a H

theorem tendsto_saddleCutoff_square_normalized {a : ℝ} (ha : 0 < a) :
    Tendsto (fun H => saddleCutoff a H ^ 2 / (H * Real.log H)) atTop (𝓝 (a / 2)) := by
  have hu := tendsto_saddleParameter_div_log ha
  have hei : Tendsto (fun H =>
      normalizedExponentialIntegral (saddleParameter a H) / Real.log H) atTop (𝓝 0) :=
    (tendsto_normalizedExponentialIntegral.comp (tendsto_saddleParameter_atTop ha)).div_atTop
      Real.tendsto_log_atTop
  apply (show Tendsto (fun H => a *
    (saddleParameter a H / Real.log H -
      normalizedExponentialIntegral (saddleParameter a H) / Real.log H))
      atTop (𝓝 (a / 2)) by
        simpa only [sub_zero, mul_one_div] using (hu.sub hei).const_mul a).congr'
  filter_upwards [eventually_ge_atTop (saddleThreshold a)] with H hH
  rw [← div_div, saddleCutoff_square_div_identity ha hH]
  ring

theorem tendsto_saddleCutoff_normalized {a : ℝ} (ha : 0 < a) :
    Tendsto (fun H => saddleCutoff a H / Real.sqrt (H * Real.log H))
      atTop (𝓝 (Real.sqrt (a / 2))) := by
  apply (show Tendsto (fun H => Real.sqrt (saddleCutoff a H ^ 2 / (H * Real.log H)))
      atTop (𝓝 (Real.sqrt (a / 2))) from
        Real.continuous_sqrt.continuousAt.tendsto.comp
          (tendsto_saddleCutoff_square_normalized ha)).congr'
  filter_upwards [eventually_ge_atTop (saddleThreshold a)] with H hH
  rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (saddleCutoff_pos ha hH).le]

theorem tendsto_soft_div_hard_saddle :
    Tendsto (fun H => saddleCutoff 2 H / saddleCutoff 1 H)
      atTop (𝓝 (Real.sqrt 2)) := by
  have hh := tendsto_saddleCutoff_normalized (by norm_num : (0 : ℝ) < 1)
  have hs := tendsto_saddleCutoff_normalized (by norm_num : (0 : ℝ) < 2)
  have heq : Real.sqrt ((2 : ℝ) / 2) / Real.sqrt ((1 : ℝ) / 2) = Real.sqrt 2 := by
    norm_num [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), div_div]
  apply (show Tendsto (fun H =>
    (saddleCutoff 2 H / Real.sqrt (H * Real.log H)) /
      (saddleCutoff 1 H / Real.sqrt (H * Real.log H)))
      atTop (𝓝 (Real.sqrt 2)) by
        have hquot := hs.div hh (ne_of_gt (Real.sqrt_pos.2 (by norm_num)))
        rw [heq] at hquot
        exact hquot.congr (fun H => rfl)).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with H hH
  have hroot : Real.sqrt (H * Real.log H) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (mul_pos (by linarith) (Real.log_pos hH)))
  field_simp [hroot]

theorem tendsto_saddleNu_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (saddleNu a) atTop atTop := by
  apply (tendsto_saddleRatio_atTop.comp (tendsto_saddleParameter_atTop ha)).congr'
  filter_upwards [eventually_ge_atTop (saddleThreshold a)] with H hH
  exact (div_saddleCutoff_eq_ratio ha hH).symm

theorem tendsto_saddleParameter_div_nu {a : ℝ} (ha : 0 < a) :
    Tendsto (fun H => saddleParameter a H / saddleNu a H) atTop (𝓝 0) := by
  have h := (Real.tendsto_exp_div_pow_atTop 2).inv_tendsto_atTop.comp
    (tendsto_saddleParameter_atTop ha)
  apply (show Tendsto (fun H => (Real.exp (saddleParameter a H) /
    saddleParameter a H ^ 2)⁻¹) atTop (𝓝 0) from h).congr'
  filter_upwards [eventually_ge_atTop (saddleThreshold a)] with H hH
  rw [saddleNu, div_saddleCutoff_eq_ratio ha hH, saddleRatio]
  have hu : saddleParameter a H ≠ 0 := by
    have := (saddleParameter_spec ha hH).1
    linarith [saddleParameterBase_ge_two]
  field_simp [hu, Real.exp_ne_zero _]

theorem tendsto_log_div_saddleNu {a : ℝ} (ha : 0 < a) :
    Tendsto (fun H => Real.log H / saddleNu a H) atTop (𝓝 0) := by
  apply (show Tendsto (fun H =>
    (Real.log H / saddleParameter a H) * (saddleParameter a H / saddleNu a H))
      atTop (𝓝 0) by
        simpa only [mul_zero] using
          (tendsto_log_div_saddleParameter ha).mul (tendsto_saddleParameter_div_nu ha)).congr'
  filter_upwards [eventually_ge_atTop (saddleThreshold a)] with H hH
  have hu : saddleParameter a H ≠ 0 := by
    have := (saddleParameter_spec ha hH).1
    linarith [saddleParameterBase_ge_two]
  field_simp [hu]

theorem hard_saddle_second_order_log_scale :
    Tendsto (fun N : ℝ => saddleCutoff 1 (Real.log N) ^ 2 / Real.log N - (1 / 2 : ℝ) *
      (Real.log (Real.log N) + Real.log (Real.log (Real.log N)) - Real.log 2 - 2))
      atTop (𝓝 0) :=
  hard_saddle_second_order.comp Real.tendsto_log_atTop

theorem soft_saddle_second_order_log_scale :
    Tendsto (fun N : ℝ => saddleCutoff 2 (Real.log N) ^ 2 / Real.log N -
      (Real.log (Real.log N) + Real.log (Real.log (Real.log N)) - Real.log 4 - 2))
      atTop (𝓝 0) :=
  soft_saddle_second_order.comp Real.tendsto_log_atTop

theorem log_log_small_against_hard_nu :
    Tendsto (fun N : ℝ => Real.log (Real.log N) / saddleNu 1 (Real.log N))
      atTop (𝓝 0) :=
  (tendsto_log_div_saddleNu (by norm_num : (0 : ℝ) < 1)).comp Real.tendsto_log_atTop

end

end PaperC.V282.SaddleScales
