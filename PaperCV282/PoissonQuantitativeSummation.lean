import PaperCV282.PoissonQuantitativeEnvelope

/-! # Summed central absolute errors at the Berry scale

This is an actual sum over Poisson atoms. The central set can be any finite
selection in the half-rate interval, uniformly in the positive real rate.
-/
namespace PaperC.V282.PoissonQuantitativeSummation

open MeasureTheory ProbabilityTheory Real PoissonQuantitativeLocal PoissonQuantitativeEnvelope
open PoissonQuantitativeLattice
open scoped NNReal

noncomputable section

theorem polynomial_gaussian_domination (x : ℝ) :
    (1+|x|^3)*exp (-x^2/3)≤145*exp (-x^2/6) := by
  have hp : 0≤x^2/12 := by positivity
  have hbase : x^2/12≤exp (x^2/12) := by have h := add_one_le_exp (x^2/12);linarith
  have hquad : |x|^4≤144*exp (x^2/6) := by
    have hh := mul_self_le_mul_self hp hbase
    have he : exp (x^2/12)*exp (x^2/12)=exp (x^2/6) := by rw [← exp_add];congr 1;ring
    rw [he] at hh
    rw [show |x|^4=(x^2)^2 by rw [show |x|^4=(|x|^2)^2 by ring,sq_abs]]
    nlinarith
  have he : 1≤exp (x^2/6) := one_le_exp_iff.mpr (by positivity)
  have hpoly : 1+|x|^3≤145*exp (x^2/6) := by
    by_cases hx : |x|≤1
    · have hc := pow_le_pow_left₀ (abs_nonneg x) hx 3
      norm_num at hc
      linarith
    · have hc := pow_le_pow_right₀ (le_of_not_ge hx) (by norm_num : (3 : ℕ)≤4)
      linarith
  calc
    _≤(145*exp (x^2/6))*exp (-x^2/3) := mul_le_mul_of_nonneg_right hpoly (exp_pos _).le
    _=145*exp (-x^2/6) := by rw [mul_assoc,← exp_add];congr 1;ring

theorem gaussian_polynomial_lattice_sum_le {rate : ℝ} (hr : 1≤rate) (s : Finset ℕ) :
    (1/sqrt rate)*(∑ n∈s,(1+|latticePoint rate n|^3)*exp (-(latticePoint rate n)^2/3))≤
      145*exp (1/6)*sqrt (12*π) := by
  have h := Finset.sum_le_sum (s := s) (fun n _ => polynomial_gaussian_domination (latticePoint rate n))
  rw [← Finset.mul_sum] at h
  have hh := (mul_le_mul_of_nonneg_left h (by positivity : 0≤1/sqrt rate)).trans
    (by convert mul_le_mul_of_nonneg_left (gaussian_lattice_sum_le hr s) (by norm_num : (0 : ℝ)≤145) using 1; ring)
  simpa only [mul_assoc] using hh

def localSummationConstant : ℝ := 1015*exp (1/6)*sqrt (12*π)

/-- Central summed local error has the intrinsic 1/sqrt(rate) scale. -/
theorem poisson_central_sum_error_le (rate : ℝ≥0) (hr : 1≤rate) (s : Finset ℕ)
    (hcentral : ∀n∈s,|(n : ℝ)-(rate : ℝ)|≤(rate : ℝ)/2) :
    (∑ n∈s,|(poissonMeasure rate).real {n}-gaussianLatticeMass rate (latticePoint rate n)|)≤
      localSummationConstant/sqrt rate := by
  have h := Finset.sum_le_sum (s := s) (fun n hn =>
    poisson_absolute_gaussian_envelope rate hr
      (show 0<n from by
        have hc := hcentral n hn
        by_contra hz
        have he : n=0 := by omega
        rw [he,Nat.cast_zero,zero_sub,abs_neg,abs_of_nonneg rate.coe_nonneg] at hc
        have hp : (0 : ℝ)<rate := lt_of_lt_of_le zero_lt_one hr
        linarith)
      (hcentral n hn))
  simp only [mul_assoc] at h
  rw [← Finset.mul_sum] at h
  have hs := mul_le_mul_of_nonneg_left (gaussian_polynomial_lattice_sum_le (rate := (rate : ℝ)) hr s)
    (by positivity : 0≤7/sqrt (rate : ℝ))
  have hsq := sq_sqrt rate.coe_nonneg
  have hid : 7/sqrt (rate : ℝ)*(1/sqrt (rate : ℝ))=7/(rate : ℝ) := by
    rw [div_mul_div_comm,mul_one,← pow_two,hsq]
  rw [← mul_assoc,hid] at hs
  have hout : (7/sqrt (rate : ℝ))*(145*exp (1/6)*sqrt (12*π))=
      localSummationConstant/sqrt rate := by unfold localSummationConstant;ring
  rw [hout] at hs
  exact h.trans hs

end
end PaperC.V282.PoissonQuantitativeSummation
