import PaperCV282.PoissonQuantitativeTailCutoff
import PaperCV282.PoissonQuantitativeTailGeometric
import PaperCV282.PoissonQuantitativeMills

/-! # Exponentially small exterior tails, relative to the moderate Gaussian scale -/
namespace PaperC.V282.PoissonQuantitativeTailExterior

open MeasureTheory ProbabilityTheory Real Set
open PoissonQuantitativeLocal PoissonQuantitativeLattice PoissonQuantitativeEnvelope
open PoissonQuantitativeTailCutoff PoissonQuantitativeTailGeometric PoissonQuantitativeMills
open scoped NNReal

noncomputable section

theorem poisson_cutoff_mass_le (rate : ℝ≥0) (hr : (16 : ℝ)≤rate) :
    (poissonMeasure rate).real {centralTailTop rate}≤15*sqrt (rate : ℝ)*exp (-(rate : ℝ)/48) := by
  obtain ⟨hn,hzl,hzu,_⟩ := centralTailTop_bounds hr
  have hsp : 0<sqrt (rate : ℝ) := by positivity
  have hs : 1≤sqrt (rate : ℝ) := one_le_sqrt.mpr (by linarith)
  have hz : 0≤latticePoint rate (centralTailTop rate) := (by positivity : 0≤sqrt (rate : ℝ)/4).trans hzl
  have hsq := sq_sqrt rate.coe_nonneg
  have hdelta : 0≤((centralTailTop rate : ℕ) : ℝ)-(rate : ℝ) := by
    simpa only [zero_mul] using (le_div_iff₀ hsp).mp hz
  have hc : |((centralTailTop rate : ℕ) : ℝ)-(rate : ℝ)|≤(rate : ℝ)/2 := by
    rw [abs_of_nonneg hdelta]
    have hh := (div_le_iff₀ hsp).mp hzu
    nlinarith
  have hlocal := poisson_absolute_gaussian_envelope rate (by linarith : 1≤rate) hn hc
  rw [abs_of_nonneg hz] at hlocal
  have hpi : 1≤sqrt (2*π) := one_le_sqrt.mpr (by have h := pi_gt_three;linarith)
  have hg : gaussianLatticeMass rate (latticePoint rate (centralTailTop rate))≤
      (1/sqrt (rate : ℝ))*exp (-(latticePoint rate (centralTailTop rate))^2/3) := by
    rw [gaussianLatticeMass_eq_density (by linarith : (0 : ℝ)<rate)]
    apply (div_le_div_of_nonneg_right (show gaussianPDFReal 0 1 (latticePoint rate (centralTailTop rate))≤
        exp (-(latticePoint rate (centralTailTop rate))^2/3) from by
      simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
      apply (mul_le_of_le_one_left (exp_pos _).le (inv_le_one_of_one_le₀ hpi)).trans
      exact exp_le_exp.mpr (by nlinarith [sq_nonneg (latticePoint rate (centralTailTop rate))])) hsp.le).trans
    exact le_of_eq (by ring)
  have hz3 := pow_le_pow_left₀ hz (hzu.trans (by linarith : sqrt (rate : ℝ)/2≤sqrt (rate : ℝ))) 3
  have hs3 : 1≤(sqrt (rate : ℝ))^3 := one_le_pow₀ hs
  have hcube : (sqrt (rate : ℝ))^3=(rate : ℝ)*sqrt rate := by
    nlinarith [congrArg (fun u : ℝ => u*sqrt (rate : ℝ)) hsq]
  have hpoly : 1+(latticePoint rate (centralTailTop rate))^3≤2*(rate : ℝ)*sqrt rate := by
    rw [hcube] at hs3 hz3
    linarith
  have hcoef1 : 1/sqrt (rate : ℝ)≤sqrt rate := (div_le_iff₀ hsp).mpr (by nlinarith)
  have hcoef2 : (7/(rate : ℝ))*(1+(latticePoint rate (centralTailTop rate))^3)≤14*sqrt rate := by
    have h := mul_le_mul_of_nonneg_left hpoly (by positivity : 0≤7/(rate : ℝ))
    have he : (7/(rate : ℝ))*(2*(rate : ℝ)*sqrt rate)=14*sqrt rate := by field_simp;norm_num
    rwa [he] at h
  have hpoint : (poissonMeasure rate).real {centralTailTop rate}≤
      (1/sqrt (rate : ℝ)+(7/(rate : ℝ))*(1+(latticePoint rate (centralTailTop rate))^3))*
        exp (-(latticePoint rate (centralTailTop rate))^2/3) := by
    have h := le_abs_self ((poissonMeasure rate).real {centralTailTop rate}-gaussianLatticeMass rate (latticePoint rate (centralTailTop rate)))
    nlinarith only [h,hlocal,hg]
  have he : exp (-(latticePoint rate (centralTailTop rate))^2/3)≤exp (-(rate : ℝ)/48) := by
    apply exp_le_exp.mpr
    nlinarith [pow_le_pow_left₀ (by positivity : 0≤sqrt (rate : ℝ)/4) hzl 2]
  exact hpoint.trans (mul_le_mul (by linarith) he (exp_pos _).le (by positivity))

theorem poisson_cutoff_tail_le (rate : ℝ≥0) (hr : (16 : ℝ)≤rate) :
    (poissonMeasure rate).real (Ici (centralTailTop rate))≤45*sqrt (rate : ℝ)*exp (-(rate : ℝ)/48) := by
  have hq := (centralTailTop_bounds hr).2.2.2
  have hq1 : (rate : ℝ)/(centralTailTop rate+1)<1 := by linarith
  have hn := (div_lt_one (by positivity : (0 : ℝ)<centralTailTop rate+1)).mp hq1
  have hg := poisson_tail_le_geometric rate (centralTailTop rate) hn
  have hden := one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<1/3)
    (show (1 : ℝ)/3≤1-(rate : ℝ)/(centralTailTop rate+1) by linarith)
  norm_num at hden
  have hm := mul_le_mul_of_nonneg_left hden (measureReal_nonneg (μ := poissonMeasure rate) (s := {centralTailTop rate}))
  have h := hg.trans (by simpa only [div_eq_mul_inv,one_div] using hm)
  exact h.trans (by have hh := mul_le_mul_of_nonneg_right (poisson_cutoff_mass_le rate hr) (by norm_num : (0 : ℝ)≤3);convert hh using 1;ring)

theorem poisson_moderate_exterior_le (rate : ℝ≥0) (hr : (4096 : ℝ)≤rate) (t : ℝ)
    (ht : 0≤t) (hcubic : t^3/sqrt rate≤1) :
    (poissonMeasure rate).real (Ici (centralTailTop rate))≤(5760/sqrt (rate : ℝ))*exp (-t^2/2) := by
  have hb := moderate_parameter_bound hr ht hcubic
  have hsp : 0<sqrt (rate : ℝ) := by positivity
  have hsq := sq_sqrt rate.coe_nonneg
  have ht2 := pow_le_pow_left₀ ht hb 2
  have hbase : (rate : ℝ)≤128*exp ((rate : ℝ)/128) := by
    have h := add_one_le_exp ((rate : ℝ)/128)
    linarith
  have he : (rate : ℝ)*exp (-(rate : ℝ)/48)≤128*exp (-t^2/2) := by
    have h := mul_le_mul_of_nonneg_right hbase (exp_pos (-(rate : ℝ)/48)).le
    rw [mul_assoc,← exp_add] at h
    exact h.trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by nlinarith)) (by norm_num))
  have hp := poisson_cutoff_tail_le rate (by linarith)
  have hm := mul_le_mul_of_nonneg_left he (by positivity : 0≤45/sqrt (rate : ℝ))
  have hid : (45/sqrt (rate : ℝ))*((rate : ℝ)*exp (-(rate : ℝ)/48))=
      45*sqrt (rate : ℝ)*exp (-(rate : ℝ)/48) := by
    field_simp
    nlinarith only [hsq]
  rw [hid] at hm
  exact hp.trans (by convert hm using 1;ring)

theorem gaussian_moderate_exterior_le {rate t : ℝ} (hr : 4096≤rate) (ht : 0≤t)
    (hcubic : t^3/sqrt rate≤1) :
    normalTail (latticePoint rate (centralTailTop rate))≤(4/sqrt rate)*exp (-t^2/2) := by
  have hsp : 0<sqrt rate := by positivity
  have hb := moderate_parameter_bound hr ht hcubic
  have hzl := (centralTailTop_bounds (by linarith : 16≤rate)).2.1
  have hz : 0<latticePoint rate (centralTailTop rate) := lt_of_lt_of_le (by positivity) hzl
  have hpi : 1≤sqrt (2*π) := one_le_sqrt.mpr (by have h := pi_gt_three;linarith)
  have hden : sqrt rate/4≤sqrt (2*π)*latticePoint rate (centralTailTop rate) :=
    hzl.trans (le_mul_of_one_le_left hz.le hpi)
  have hcoef := one_div_le_one_div_of_le (by positivity : 0<sqrt rate/4) hden
  have he : exp (-(latticePoint rate (centralTailTop rate))^2/2)≤exp (-t^2/2) := by
    apply exp_le_exp.mpr
    have htz : t≤latticePoint rate (centralTailTop rate) := by linarith
    nlinarith [pow_le_pow_left₀ ht htz 2]
  have hh := mul_le_mul he hcoef (by positivity) (exp_pos _).le
  have h := normalTail_upper_positive (latticePoint rate (centralTailTop rate)) hz
  exact h.trans (by simpa only [div_eq_mul_inv,one_div,inv_mul_cancel₀,mul_inv_rev,inv_inv,one_mul,mul_comm] using hh)

end
end PaperC.V282.PoissonQuantitativeTailExterior
