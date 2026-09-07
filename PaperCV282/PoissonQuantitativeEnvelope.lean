import PaperCV282.PoissonQuantitativeAbsolute
import PaperCV282.PoissonQuantitativeLattice
import Mathlib.Analysis.Real.Pi.Bounds

/-! # A summable Gaussian envelope for absolute local Poisson errors -/
namespace PaperC.V282.PoissonQuantitativeEnvelope

open MeasureTheory ProbabilityTheory Real PoissonQuantitativeAbsolute PoissonQuantitativeLocal
open PoissonQuantitativeLattice
open scoped NNReal

noncomputable section

theorem sqrt_central_lower {rate value : ℝ} (hr : 0<rate) (hv : rate/2≤value) :
    sqrt rate/2≤sqrt value := by
  have hp : 0≤value := by linarith
  nlinarith [sq_sqrt hr.le,sq_sqrt hp,sqrt_nonneg rate,sqrt_nonneg value]

theorem inv_sqrt_central_le {rate value : ℝ} (hr : 0<rate) (hv : rate/2≤value) :
    (sqrt value)⁻¹≤2/sqrt rate := by
  have hp : 0<value := by linarith
  have h := one_div_le_one_div_of_le (by positivity : 0<sqrt rate/2) (sqrt_central_lower hr hv)
  simpa only [one_div,inv_div] using h

/-- An explicit Lipschitz estimate for the varying square-root prefactor. -/
theorem inv_sqrt_difference_le {rate value : ℝ} (hr : 0<rate) (hv : rate/2≤value) :
    |(sqrt value)⁻¹-(sqrt rate)⁻¹|≤2*|value-rate|/(rate*sqrt rate) := by
  have hp : 0<value := by linarith
  have ha : 0<sqrt value := sqrt_pos.mpr hp
  have hb : 0<sqrt rate := sqrt_pos.mpr hr
  have hs := sqrt_central_lower hr hv
  have hsq := sq_sqrt hr.le
  have hvq := sq_sqrt hp.le
  have he : (sqrt value)⁻¹-(sqrt rate)⁻¹=
      (rate-value)/(sqrt value*sqrt rate*(sqrt value+sqrt rate)) := by
    field_simp
    nlinarith
  rw [he,abs_div,abs_sub_comm rate,abs_of_pos (by positivity : 0<sqrt value*sqrt rate*(sqrt value+sqrt rate))]
  have hm : rate/2≤sqrt value*sqrt rate := by nlinarith
  have hden : rate*sqrt rate/2≤sqrt value*sqrt rate*(sqrt value+sqrt rate) := by
    have h := mul_le_mul hm (show sqrt rate≤sqrt value+sqrt rate by linarith) hb.le (by positivity)
    nlinarith
  have h := div_le_div_of_nonneg_left (abs_nonneg (value-rate)) (by positivity : 0<rate*sqrt rate/2) hden
  calc
    _≤|value-rate|/(rate*sqrt rate/2) := h
    _=2*|value-rate|/(rate*sqrt rate) := by ring

/-- The factor 1/sqrt(2*pi) never worsens these elementary prefactor bounds. -/
theorem gaussian_prefactor_bounds {rate value : ℝ} (hr : 0<rate) (hv : rate/2≤value) :
    (sqrt (2*π*value))⁻¹≤2/sqrt rate ∧
    |(sqrt (2*π*value))⁻¹-(sqrt (2*π*rate))⁻¹|≤2*|value-rate|/(rate*sqrt rate) := by
  have hp : 0<value := by linarith
  have hpi : 1≤sqrt (2*π) := (one_le_sqrt).mpr (by have h := pi_gt_three;linarith)
  have hfac : 0≤(sqrt (2*π))⁻¹ := by positivity
  have hfacOne : (sqrt (2*π))⁻¹≤1 := inv_le_one_of_one_le₀ hpi
  rw [sqrt_mul (by positivity : 0≤2*π),sqrt_mul (by positivity : 0≤2*π),mul_inv_rev,mul_inv_rev]
  constructor
  · calc
      (sqrt value)⁻¹*(sqrt (2*π))⁻¹≤(sqrt value)⁻¹ := mul_le_of_le_one_right (by positivity) hfacOne
      _≤_ := inv_sqrt_central_le hr hv
  · rw [← sub_mul,abs_mul,abs_of_nonneg hfac]
    exact (mul_le_of_le_one_right (abs_nonneg _) hfacOne).trans (inv_sqrt_difference_le hr hv)

/-- The common algebraic prefactor for any valid entropy envelope. -/
theorem central_prefactor_error_le (rate : ℝ≥0) (hr : 1≤rate) {n : ℕ} (hn : 0<n)
    (hc : |(n : ℝ)-(rate : ℝ)|≤(rate : ℝ)/2) :
    (sqrt (2*π*n))⁻¹*(1/(12*n)+2*|(n : ℝ)-rate|^3/(rate : ℝ)^2)+
        |(sqrt (2*π*n))⁻¹-(sqrt (2*π*rate))⁻¹|≤
      (7/(rate : ℝ))*(1+|latticePoint rate n|^3) := by
  have hrp : (0 : ℝ)<rate := lt_of_lt_of_le zero_lt_one hr
  have hval : (rate : ℝ)/2≤n := by have h := neg_abs_le ((n : ℝ)-rate);linarith
  obtain ⟨hpre,hdif⟩ := gaussian_prefactor_bounds hrp hval
  have hs : 1≤sqrt (rate : ℝ) := one_le_sqrt.mpr hr
  have hsp : 0<sqrt (rate : ℝ) := by positivity
  have hsq := sq_sqrt rate.coe_nonneg
  have hst : 1/(12*(n : ℝ))≤1/(6*(rate : ℝ)) := by
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have hz : |(n : ℝ)-rate|=|latticePoint rate n| *sqrt (rate : ℝ) := by
    rw [latticePoint,abs_div,abs_of_pos hsp,div_mul_cancel₀ _ hsp.ne']
  have hsum : 1/(12*(n : ℝ))+2*|(n : ℝ)-rate|^3/(rate : ℝ)^2≤
      1/(6*(rate : ℝ))+2*|(n : ℝ)-rate|^3/(rate : ℝ)^2 := add_le_add hst le_rfl
  have h1 := add_le_add (mul_le_mul hpre hsum
    (by positivity) (by positivity)) hdif
  apply h1.trans
  have hid : (2/sqrt (rate : ℝ))*(1/(6*(rate : ℝ))+2*|(n : ℝ)-rate|^3/(rate : ℝ)^2)+
      2*|(n : ℝ)-rate|/((rate : ℝ)*sqrt (rate : ℝ))=
    (1/(3*sqrt (rate : ℝ))+2*|latticePoint rate n|+4*|latticePoint rate n|^3)/(rate : ℝ) := by
    rw [hz]
    field_simp
    linear_combination 72*sqrt (rate : ℝ)*|latticePoint rate n|^3*hsq
  rw [hid]
  have hu : 1/(3*sqrt (rate : ℝ))≤1 := (div_le_one (by positivity)).mpr (by linarith)
  have hx : |latticePoint rate n|≤1+|latticePoint rate n|^3 := by
    by_cases h : |latticePoint rate n|≤1
    · nlinarith [pow_nonneg (abs_nonneg (latticePoint rate n)) 3]
    · have hp := le_self_pow₀ (le_of_not_ge h) (by norm_num : (3 : ℕ)≠0)
      linarith
  have hpoly : 1/(3*sqrt (rate : ℝ))+2*|latticePoint rate n|+4*|latticePoint rate n|^3≤
      7*(1+|latticePoint rate n|^3) := by nlinarith [pow_nonneg (abs_nonneg (latticePoint rate n)) 3]
  convert div_le_div_of_nonneg_right hpoly hrp.le using 1; ring


/-- Uniform local absolute error, without a small-cubic-remainder premise. -/
theorem poisson_absolute_gaussian_envelope (rate : ℝ≥0) (hr : 1≤rate) {n : ℕ} (hn : 0<n)
    (hc : |(n : ℝ)-(rate : ℝ)|≤(rate : ℝ)/2) :
    |(poissonMeasure rate).real {n}-gaussianLatticeMass rate (latticePoint rate n)|≤
      (7/(rate : ℝ))*(1+|latticePoint rate n|^3)*exp (-(latticePoint rate n)^2/3) := by
  have hrp : (0 : ℝ)<rate := lt_of_lt_of_le zero_lt_one hr
  have hlocal := poisson_central_absolute_error rate hrp hn hc
  have hpref := central_prefactor_error_le rate hr hn hc
  have hex : -((n : ℝ)-rate)^2/(3*rate)=-(latticePoint rate n)^2/3 := by
    rw [latticePoint,div_pow,sq_sqrt rate.coe_nonneg]
    ring
  have h := hlocal.trans (mul_le_mul_of_nonneg_left hpref (exp_pos _).le)
  rw [hex] at h
  simpa only [latticePoint,mul_comm,mul_left_comm,mul_assoc] using h

end
end PaperC.V282.PoissonQuantitativeEnvelope
