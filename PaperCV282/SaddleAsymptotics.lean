import PaperCV282.SaddleParameters
import PaperCV282.ExponentialIntegralAsymptotics

/-!
# Internal analytic asymptotics for the two cutoff saddles

The fixed scalar a is quantified before the limit H -> infinity. These
statements evaluate the actual uniquely defined roots, not arbitrary sequences
assumed to have a prescribed asymptotic expansion.
-/

namespace PaperC.V282.SaddleAsymptotics

open Set Filter Topology SaddleBranch SaddleParameters ExponentialIntegral
open ExponentialIntegralAsymptotics

noncomputable section

def normalizedExponentialIntegral (u : ℝ) : ℝ := u * exponentialIntegral u / Real.exp u

theorem normalizedExponentialIntegral_error_eventually :
    ∀ᶠ u : ℝ in atTop,
      |normalizedExponentialIntegral u - 1 - 1 / u| ≤ 5 / u ^ 2 := by
  filter_upwards [exponentialIntegralRemainder_bound_eventually,
    eventually_ge_atTop (1 : ℝ)] with u hu huone
  have hupos : 0 < u := by linarith
  have hexp : 0 < Real.exp u := Real.exp_pos _
  have heq : normalizedExponentialIntegral u - 1 - 1 / u =
      (u / Real.exp u) * exponentialIntegralRemainder u := by
    unfold normalizedExponentialIntegral exponentialIntegralRemainder
    field_simp [ne_of_gt hupos, ne_of_gt hexp]
  rw [heq, abs_mul, abs_of_pos (div_pos hupos hexp)]
  calc
    _ ≤ (u / Real.exp u) * (5 * (Real.exp u / u ^ 3)) :=
      mul_le_mul_of_nonneg_left hu (div_pos hupos hexp).le
    _ = _ := by field_simp [ne_of_gt hupos, ne_of_gt hexp]

theorem tendsto_normalizedExponentialIntegral :
    Tendsto normalizedExponentialIntegral atTop (𝓝 1) := by
  have hinv : Tendsto (fun u : ℝ => 1 / u) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero
  have hbound : Tendsto (fun u : ℝ => 5 / u ^ 2) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] using
      tendsto_inv_atTop_zero.pow 2 |>.const_mul (5 : ℝ)
  have herr : Tendsto (fun u => normalizedExponentialIntegral u - 1 - 1 / u)
      atTop (𝓝 0) :=
    squeeze_zero_norm' (by simpa only [Real.norm_eq_abs] using
      normalizedExponentialIntegral_error_eventually) hbound
  have h := (herr.add hinv).add_const 1
  convert h using 1 <;> norm_num

def saddleCostFactor (u : ℝ) : ℝ := 1 - exponentialIntegral u / Real.exp u

theorem saddleCostFactor_identity {u : ℝ} (hu : u ≠ 0) :
    saddleCostFactor u = 1 - normalizedExponentialIntegral u / u := by
  unfold saddleCostFactor normalizedExponentialIntegral
  field_simp [hu]

theorem tendsto_saddleCostFactor : Tendsto saddleCostFactor atTop (𝓝 1) := by
  have hquot : Tendsto (fun u => normalizedExponentialIntegral u / u) atTop (𝓝 0) :=
    tendsto_normalizedExponentialIntegral.div_atTop tendsto_id
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hquot
  apply (show Tendsto (fun u => 1 - normalizedExponentialIntegral u / u) atTop (𝓝 1) by
    simpa only [sub_zero] using h).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  exact (saddleCostFactor_identity (ne_of_gt hu)).symm

theorem tendsto_log_saddleCostFactor :
    Tendsto (fun u => Real.log (saddleCostFactor u)) atTop (𝓝 0) := by
  simpa only [Real.log_one, Function.comp_def] using
    (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp tendsto_saddleCostFactor

theorem saddleCostParam_eq_exp_mul_factor (u : ℝ) :
    saddleCostParam u = Real.exp u * saddleCostFactor u := by
  unfold saddleCostParam saddleCostFactor
  field_simp [Real.exp_ne_zero u]

theorem saddleCostFactor_pos {u : ℝ} (hu : saddleParameterBase ≤ u) :
    0 < saddleCostFactor u := by
  have hb : 1 ≤ saddleParameterBase := by linarith [saddleParameterBase_ge_two]
  have hc := strictMonoOn_saddleCostParam.monotoneOn hb (hb.trans hu) hu
  have hpos : 0 < saddleCostParam u := by linarith [saddleCostParam_base_ge_one]
  rw [saddleCostParam_eq_exp_mul_factor] at hpos
  exact (mul_pos_iff_of_pos_left (Real.exp_pos _)).1 hpos

theorem log_saddleHeight {a u : ℝ} (ha : 0 < a) (hu : saddleParameterBase ≤ u) :
    Real.log (saddleHeight a u) =
      2 * u - Real.log u + Real.log a + Real.log (saddleCostFactor u) := by
  have hupos : 0 < u := by linarith [saddleParameterBase_ge_two]
  have hfpos := saddleCostFactor_pos hu
  rw [saddleHeight, saddleRatio, saddleCostParam_eq_exp_mul_factor,
    Real.log_mul (ne_of_gt (mul_pos ha (div_pos (Real.exp_pos _) hupos)))
      (ne_of_gt (mul_pos (Real.exp_pos _) hfpos)),
    Real.log_mul (ne_of_gt ha) (ne_of_gt (div_pos (Real.exp_pos _) hupos)),
    Real.log_div (Real.exp_ne_zero _) (ne_of_gt hupos),
    Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hfpos), Real.log_exp]
  ring

theorem tendsto_saddleParameter_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (saddleParameter a) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop
    (max (saddleThreshold a) (saddleHeight a (max saddleParameterBase b)))] with H hH
  have hdomain : saddleThreshold a ≤ H := (le_max_left _ _).trans hH
  have hu := (saddleParameter_spec ha hdomain).1
  have hv : saddleParameterBase ≤ max saddleParameterBase b := le_max_left _ _
  have hh : saddleHeight a (max saddleParameterBase b) ≤
      saddleHeight a (saddleParameter a H) := by
    rw [(saddleParameter_spec ha hdomain).2]
    exact (le_max_right _ _).trans hH
  exact (le_max_right _ _).trans ((strictMonoOn_saddleHeight ha).le_iff_le hv hu |>.1 hh)

theorem log_saddleParameter_identity {a H : ℝ} (ha : 0 < a)
    (hH : saddleThreshold a ≤ H) :
    Real.log H = 2 * saddleParameter a H - Real.log (saddleParameter a H) +
      Real.log a + Real.log (saddleCostFactor (saddleParameter a H)) := by
  calc
    Real.log H = Real.log (saddleHeight a (saddleParameter a H)) :=
      congrArg Real.log (saddleParameter_spec ha hH).2.symm
    _ = _ := log_saddleHeight ha (saddleParameter_spec ha hH).1

end

end PaperC.V282.SaddleAsymptotics
