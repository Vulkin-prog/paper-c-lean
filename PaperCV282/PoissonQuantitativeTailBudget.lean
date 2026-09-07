import PaperCV282.PoissonQuantitativeModerateLimit
import PaperCV282.HardLocalClosureBudget

/-! # The literal hard moderate-tail budget of companion D.1 -/
namespace PaperC.V282.PoissonQuantitativeTailBudget

open MeasureTheory Real Filter Topology PoissonQuantitativeMills HardLocalClosureBudget
open SaddleParameters SaddleScales SaddleCutoffAdmissibility SaddleRateConvergence
open AggregateCutoffRemainder

noncomputable section

def millsConstant : ℝ := exp (3/2)*sqrt (2*π)
def hardTailCost (I rate t : ℝ) : ℝ := I+max 0 (log rate)+t^2/2+log (1+t)
def hardTailRemainder (N : ℕ) (c : ℝ) : ℝ :=
  20*(millsConstant*exp (-(c/2)*saddleNu 1 (log N))+(N : ℝ)^(-(1/6 : ℝ)))

theorem millsConstant_pos : 0<millsConstant := by unfold millsConstant;positivity

theorem hardTailRemainder_tendsto_zero {c : ℝ} (hc : 0<c) :
    Tendsto (fun N : ℕ => hardTailRemainder N c) atTop (𝓝 0) := by
  have he := margin_exponential_nat_tendsto_zero 1 (2*c) (c/2) (by norm_num) (by linarith)
  have hp := polynomial_error_nat_tendsto_zero (1/6) (by norm_num)
  have hh := ((he.const_mul millsConstant).add hp).const_mul 20
  simpa only [hardTailRemainder,mul_zero,add_zero,
    show 2*c/2-c/2=c/2 by ring,show -(1/3 : ℝ)+1/6= -(1/6 : ℝ) by ring] using hh

theorem normalTail_reciprocal_le {t : ℝ} (ht : 0≤t) :
    (normalTail t)⁻¹≤millsConstant*exp (t^2/2+log (1+t)) := by
  have hp := normalTail_pos t ht
  have ht1 : 0<1+t := by positivity
  have hpi : 0<sqrt (2*π) := by positivity
  have hlo := normalTail_lower t ht
  have hlop : 0<exp (-t^2/2-3/2)/(sqrt (2*π)*(1+t)) := by positivity
  have h := one_div_le_one_div_of_le hlop hlo
  have he : (-t^2/2-3/2)= -(t^2/2+3/2) := by ring
  rw [one_div] at h
  apply h.trans_eq
  rw [he,exp_neg,exp_add,exp_add,exp_log ht1]
  unfold millsConstant
  field_simp

/-- A uniform upper Mills comparison including the boundary t=0. -/
theorem normalTail_uniform_upper {t : ℝ} (ht : 0≤t) :
    normalTail t≤4*exp (-t^2/2)/(1+t) := by
  have ht1 : 0<1+t := by positivity
  by_cases h : t≤1
  · have he : (1 : ℝ)/2≤exp (-t^2/2) := by
      have hh := add_one_le_exp (-t^2/2)
      nlinarith
    have hb : (1 : ℝ)≤4*exp (-t^2/2)/(1+t) :=
      (le_div_iff₀ ht1).mpr (by nlinarith)
    exact (measureReal_le_one (μ := ProbabilityTheory.gaussianReal 0 1)).trans hb
  · have htpos : 0<t := by linarith
    have hpi : 1≤sqrt (2*π) := one_le_sqrt.mpr (by have hp := pi_gt_three;linarith)
    have hh := normalTail_upper_positive t htpos
    have hden : 1+t≤4*(sqrt (2*π)*t) := by
      have hx := mul_le_mul_of_nonneg_right hpi ht
      nlinarith
    apply hh.trans
    apply (div_le_div_iff₀ (by positivity : 0<sqrt (2*π)*t) ht1).mpr
    nlinarith [mul_le_mul_of_nonneg_left hden (exp_pos (-t^2/2)).le]

theorem weighted_tail_inverse_le {I rate t : ℝ} (hr : 0<rate) (ht : 0≤t) :
    exp I*rate*(normalTail t)⁻¹≤millsConstant*exp (hardTailCost I rate t) := by
  have hlambda : rate≤exp (max 0 (log rate)) := by
    nth_rw 1 [← exp_log hr]
    exact exp_le_exp.mpr (le_max_right _ _)
  calc
    _ ≤ exp I*rate*(millsConstant*exp (t^2/2+log (1+t))) :=
      mul_le_mul_of_nonneg_left (normalTail_reciprocal_le ht) (by positivity)
    _ ≤ exp I*exp (max 0 (log rate))*(millsConstant*exp (t^2/2+log (1+t))) := by
      gcongr
      exact mul_nonneg millsConstant_pos.le (exp_nonneg _)
    _ = _ := by rw [hardTailCost,exp_add,exp_add,exp_add,exp_add];ring

theorem hard_leading_div_tail_le {I rate t V nu c eta : ℝ}
    (hr : 0<rate) (ht : 0≤t) (hb : hardTailCost I rate t≤V-c*nu) :
    exp I*rate*exp (-V+eta*nu)/normalTail t≤millsConstant*exp (-(c-eta)*nu) := by
  have hw := (weighted_tail_inverse_le (I := I) hr ht).trans
    (mul_le_mul_of_nonneg_left (exp_le_exp.mpr hb) millsConstant_pos.le)
  calc
    _ = (exp I*rate*(normalTail t)⁻¹)*exp (-V+eta*nu) := by ring
    _ ≤ (millsConstant*exp (V-c*nu))*exp (-V+eta*nu) :=
      mul_le_mul_of_nonneg_right hw (exp_nonneg _)
    _ = _ := by rw [mul_assoc,← exp_add];congr 2;ring

theorem hard_polynomial_div_tail_eventually (c : ℝ) (hc : 0≤c) :
    ∀ᶠ N : ℕ in atTop, ∀ I rate t : ℝ, 0<rate → 0≤t →
      hardTailCost I rate t≤saddleCutoff 1 (log N)-c*saddleNu 1 (log N) →
      exp I*rate*(N : ℝ)^(-(1/3 : ℝ)+1/12)/normalTail t≤(N : ℝ)^(-(1/6 : ℝ)) := by
  have hnu := (tendsto_saddleNu_atTop (a := 1) (by norm_num)).comp
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [constant_exp_saddle_le_power_eventually millsConstant 1 (1/12)
    millsConstant_pos (by norm_num),hnu.eventually (eventually_ge_atTop (0 : ℝ)),
    eventually_ge_atTop (2 : ℕ)] with N hp hnu hN
  intro I rate t hr ht hb
  dsimp only [Function.comp_def] at hnu
  have hb' := hb.trans (sub_le_self _ (mul_nonneg hc hnu))
  have hinv : exp I*rate*(normalTail t)⁻¹≤(N : ℝ)^(1/12 : ℝ) := by
    refine (weighted_tail_inverse_le hr ht).trans ?_
    exact (mul_le_mul_of_nonneg_left (exp_le_exp.mpr hb') millsConstant_pos.le).trans
      (by simpa only [one_mul] using hp)
  calc
    _ = (exp I*rate*(normalTail t)⁻¹)*(N : ℝ)^(-(1/3 : ℝ)+1/12) := by ring
    _ ≤ (N : ℝ)^(1/12 : ℝ)*(N : ℝ)^(-(1/3 : ℝ)+1/12) :=
      mul_le_mul_of_nonneg_right hinv (rpow_nonneg (Nat.cast_nonneg N) _)
    _ = _ := by rw [← rpow_add (by positivity : (0 : ℝ)<N)];congr 1;ring

end
end PaperC.V282.PoissonQuantitativeTailBudget
