import PaperCV282.PoissonQuantitativeTailEntropy

/-! # Local errors retaining the Gaussian cost of a moving tail threshold -/
namespace PaperC.V282.PoissonQuantitativeTailLocal

open MeasureTheory ProbabilityTheory Real
open PoissonQuantitativeLocal PoissonQuantitativeLattice PoissonQuantitativeAbsolute
open PoissonQuantitativeEnvelope PoissonQuantitativeTailEntropy PoissonEntropyTaylor PoissonStirlingBounds
open scoped NNReal

noncomputable section

theorem poisson_absolute_of_entropy_lower (rate : ℝ≥0) (hr : 1≤rate) {n : ℕ} (hn : 0<n)
    (hc : |(n : ℝ)-(rate : ℝ)|≤(rate : ℝ)/2) (q : ℝ)
    (ha : q≤(rate : ℝ)*poissonEntropy ((n : ℝ)/rate))
    (hb : q≤(latticePoint rate n)^2/2) :
    |(poissonMeasure rate).real {n}-gaussianLatticeMass rate (latticePoint rate n)|≤
      (7/(rate : ℝ))*(1+|latticePoint rate n|^3)*exp (-q) := by
  have hrp : (0 : ℝ)<rate := lt_of_lt_of_le zero_lt_one hr
  have hcoord : (latticePoint rate n)^2/2=((n : ℝ)-rate)^2/(2*rate) := by
    rw [latticePoint,div_pow,sq_sqrt rate.coe_nonneg]
    ring
  have ht := weighted_exponential_error
    ((rate : ℝ)*poissonEntropy ((n : ℝ)/rate)) ((latticePoint rate n)^2/2)
    (stirlingLogError n) q ((sqrt (2*π*n))⁻¹) ((sqrt (2*π*rate))⁻¹)
    (stirlingLogError_nonneg hn) (by positivity) ha hb
  have he := entropy_central_remainder_le (rate := (rate : ℝ)) hrp hc
  rw [← hcoord] at he
  have hs := stirlingLogError_le hn
  have hpre := central_prefactor_error_le rate hr hn hc
  have hm := mul_le_mul_of_nonneg_left (add_le_add_right
    (mul_le_mul_of_nonneg_left (add_le_add hs he) (by positivity : 0≤(sqrt (2*π*n))⁻¹))
    |(sqrt (2*π*n))⁻¹-(sqrt (2*π*rate))⁻¹|) (exp_pos (-q)).le
  have h := ht.trans (by simpa only [add_comm] using hm)
  have hfinal := h.trans (by simpa only [add_comm] using mul_le_mul_of_nonneg_left hpre (exp_pos (-q)).le)
  rw [poissonMeasure_real_singleton,poisson_local_exact (rate := (rate : ℝ)) hrp hn]
  unfold poissonLocalApprox gaussianLatticeMass
  simpa only [neg_mul,mul_neg,neg_div,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using hfinal

/-- Uniform throughout the central upper-tail sector, before any summation. -/
theorem poisson_tail_local_error (rate : ℝ≥0) (hr : 1≤rate) {n : ℕ} (hn : 0<n)
    (t : ℝ) (ht : 0≤t) (htz : t≤latticePoint rate n)
    (hz : latticePoint rate n≤sqrt (rate : ℝ)/2) :
    |(poissonMeasure rate).real {n}-gaussianLatticeMass rate (latticePoint rate n)|≤
      (7/(rate : ℝ))*(1+(latticePoint rate n)^3)*
        exp (-t^2/2+2*t^3/sqrt rate-((latticePoint rate n)^2-t^2)/3) := by
  have hrp : (0 : ℝ)<rate := lt_of_lt_of_le zero_lt_one hr
  have hsp : 0<sqrt (rate : ℝ) := sqrt_pos.mpr hrp
  have hz0 := ht.trans htz
  have hdelta : 0≤(n : ℝ)-(rate : ℝ) := by simpa only [zero_mul] using (le_div_iff₀ hsp).mp hz0
  have hc : |(n : ℝ)-(rate : ℝ)|≤(rate : ℝ)/2 := by
    rw [abs_of_nonneg hdelta]
    have h := (div_le_iff₀ hsp).mp hz
    nlinarith [sq_sqrt rate.coe_nonneg]
  have he : (n : ℝ)/(rate : ℝ)=1+latticePoint rate n/sqrt rate := by
    rw [latticePoint,div_div,← pow_two,sq_sqrt rate.coe_nonneg]
    field_simp
    ring
  have ha := entropy_from_threshold hrp ht htz hz
  rw [← he] at ha
  have hb : t^2/2-2*t^3/sqrt rate+((latticePoint rate n)^2-t^2)/3≤(latticePoint rate n)^2/2 := by
    have ht2 := pow_le_pow_left₀ ht htz 2
    have hp : 0≤2*t^3/sqrt rate := by positivity
    nlinarith
  have h := poisson_absolute_of_entropy_lower rate hr hn hc _ ha hb
  rw [abs_of_nonneg hz0] at h
  convert h using 1
  congr 2
  ring

end
end PaperC.V282.PoissonQuantitativeTailLocal
