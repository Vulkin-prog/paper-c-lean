import PaperCV282.PoissonQuantitativeCDFGeometry
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Effective Mills bounds for the actual standard Gaussian tail -/
namespace PaperC.V282.PoissonQuantitativeMills

open MeasureTheory ProbabilityTheory Real Set PoissonQuantitativeCDFGeometry

noncomputable section

def normalTail (t : ℝ) : ℝ := (gaussianReal 0 1).real (Ici t)

theorem normalTail_lower (t : ℝ) (ht : 0≤t) :
    exp (-t^2/2-3/2)/(sqrt (2*π)*(1+t))≤normalTail t := by
  have hp : 0<1+t := by linarith
  have h0 : 0≤1/(1+t) := by positivity
  have h1 : 1/(1+t)≤1 := (div_le_one hp).mpr (by linarith)
  have h2 : t*(1/(1+t))≤1 := by rw [one_div,← div_eq_mul_inv];exact (div_le_one hp).mpr (by linarith)
  have hl (x : ℝ) (hx : x∈Ico t (t+1/(1+t))) :
      exp (-t^2/2-3/2)/(sqrt (2*π))≤gaussianPDFReal 0 1 x := by
    have hd0 : 0≤x-t := sub_nonneg.mpr hx.1
    have hd1 : x-t≤1/(1+t) := by have h := hx.2;linarith
    have hd2 : x-t≤1 := hd1.trans h1
    have hprod := mul_le_mul_of_nonneg_left hd1 ht
    have hsq : x^2≤t^2+3 := by nlinarith [sq_nonneg (x-t)]
    simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,div_eq_mul_inv]
    rw [mul_comm ((sqrt (2*π))⁻¹)]
    exact mul_le_mul_of_nonneg_right (exp_le_exp.mpr (by linarith)) (by positivity)
  have hi := integrable_gaussianPDFReal (μ := 0) (v := 1)
  have hc : IntegrableOn (fun _ : ℝ => exp (-t^2/2-3/2)/sqrt (2*π)) (Ico t (t+1/(1+t))) :=
    integrableOn_const (by rw [volume_Ico];exact ENNReal.ofReal_ne_top)
  have h := setIntegral_mono_on hc hi.integrableOn measurableSet_Ico hl
  rw [setIntegral_const,measureReal_def,volume_Ico] at h
  simp only [add_sub_cancel_left,ENNReal.toReal_ofReal h0,smul_eq_mul] at h
  have hh := measureReal_mono (μ := gaussianReal 0 1)
    (show Ico t (t+1/(1+t))⊆Ici t from fun _ hx => hx.1)
  rw [gaussian_real_eq_integral] at hh
  unfold normalTail
  apply le_trans _ hh
  convert h using 1; simp only [div_eq_mul_inv,mul_inv_rev]; ring

theorem normalTail_upper_positive (t : ℝ) (ht : 0<t) :
    normalTail t≤exp (-t^2/2)/(sqrt (2*π)*t) := by
  have hi := integrable_gaussianPDFReal (μ := 0) (v := 1)
  have he := integrableOn_exp_mul_Ioi (a := -t) (neg_neg_of_pos ht) t
  have h : (∫ x in Ioi t,gaussianPDFReal 0 1 x)≤
      ∫ x in Ioi t,((sqrt (2*π))⁻¹*exp (t^2/2))*exp ((-t)*x) := by
    apply setIntegral_mono_on hi.integrableOn (he.const_mul _) measurableSet_Ioi
    intro x hx
    simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
    rw [mul_assoc,← exp_add]
    exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by nlinarith [sq_nonneg (x-t)])) (by positivity)
  rw [integral_const_mul,integral_exp_mul_Ioi (neg_neg_of_pos ht)] at h
  have hp : normalTail t=∫ x in Ioi t,gaussianPDFReal 0 1 x := by
    rw [normalTail,gaussian_real_eq_integral,integral_Ici_eq_integral_Ioi]
  rw [hp]
  have hid : ((sqrt (2*π))⁻¹*exp (t^2/2))*(-exp (-t*t)/(-t))=
      exp (-t^2/2)/(sqrt (2*π)*t) := by
    rw [neg_div_neg_eq,← mul_div_assoc,mul_assoc,← exp_add]
    have he : t^2/2+-t*t = -t^2/2 := by ring
    rw [he]
    ring
  rwa [hid] at h

theorem normalTail_pos (t : ℝ) (ht : 0≤t) : 0<normalTail t :=
  lt_of_lt_of_le (by positivity) (normalTail_lower t ht)

end
end PaperC.V282.PoissonQuantitativeMills
