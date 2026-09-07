import PaperCV282.PoissonQuantitativeEntropy

/-! # Absolute local error with Gaussian decay

Unlike a relative central bound, this estimate keeps the decaying factor on
the whole half-rate interval. It is suitable for summation over lattice cells.
-/
namespace PaperC.V282.PoissonQuantitativeAbsolute

open MeasureTheory ProbabilityTheory Real PoissonStirlingBounds PoissonQuantitativeLocal
open PoissonQuantitativeEntropy PoissonEntropyTaylor PoissonCentralAsymptotics
open scoped NNReal

noncomputable section

theorem abs_exp_neg_sub_one_le {c : ℝ} (hc : 0≤c) : |exp (-c)-1|≤c := by
  have he : exp (-c)≤1 := exp_le_one_iff.mpr (by linarith)
  rw [abs_of_nonpos (by linarith)]
  have h := add_one_le_exp (-c)
  linarith

/-- Elementary comparison of the Stirling and Gaussian exponentials. -/
theorem weighted_exponential_error (a b c q u v : ℝ) (hc : 0≤c) (hu : 0≤u)
    (ha : q≤a) (hb : q≤b) :
    |exp (-c)*exp (-a)*u-exp (-b)*v|≤
      exp (-q)*(u*(c+|a-b|)+|u-v|) := by
  have hea : exp (-a)≤exp (-q) := exp_le_exp.mpr (neg_le_neg ha)
  have heb : exp (-b)≤exp (-q) := exp_le_exp.mpr (neg_le_neg hb)
  have hex := abs_exp_neg_sub_le a b
  have hem : exp (-min a b)≤exp (-q) := exp_le_exp.mpr (neg_le_neg (le_min ha hb))
  have h1 : |exp (-c)*exp (-a)*u-exp (-a)*u|≤c*exp (-q)*u := by
    rw [show exp (-c)*exp (-a)*u-exp (-a)*u=(exp (-c)-1)*exp (-a)*u by ring,
      abs_mul,abs_mul,abs_of_pos (exp_pos _),abs_of_nonneg hu]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (abs_exp_neg_sub_one_le hc) hea (exp_pos _).le hc) hu
  have h2 : |exp (-a)*u-exp (-b)*u|≤exp (-q)*|a-b| *u := by
    rw [← sub_mul,abs_mul,abs_of_nonneg hu]
    exact mul_le_mul_of_nonneg_right (hex.trans (mul_le_mul_of_nonneg_right hem (abs_nonneg _))) hu
  have h3 : |exp (-b)*u-exp (-b)*v|≤exp (-q)*|u-v| := by
    rw [← mul_sub,abs_mul,abs_of_pos (exp_pos _)]
    exact mul_le_mul_of_nonneg_right heb (abs_nonneg _)
  have ht := abs_sub_le (exp (-c)*exp (-a)*u) (exp (-a)*u) (exp (-b)*v)
  have hs := abs_sub_le (exp (-a)*u) (exp (-b)*u) (exp (-b)*v)
  nlinarith

/-- The actual local absolute error, with a retained exp(-z²/3) envelope. -/
theorem poisson_central_absolute_error (rate : ℝ≥0) (hr : 0<rate) {n : ℕ} (hn : 0<n)
    (hc : |(n : ℝ)-(rate : ℝ)|≤(rate : ℝ)/2) :
    |(poissonMeasure rate).real {n}-gaussianLatticeMass rate (((n : ℝ)-rate)/sqrt rate)|≤
      exp (-((n : ℝ)-rate)^2/(3*rate))*
        ((sqrt (2*π*n))⁻¹*(1/(12*n)+2*|(n : ℝ)-rate|^3/(rate : ℝ)^2)+
          |(sqrt (2*π*n))⁻¹-(sqrt (2*π*rate))⁻¹|) := by
  have hlo := entropy_central_lower (rate := (rate : ℝ)) hr hc
  have ht := weighted_exponential_error
    ((rate : ℝ)*poissonEntropy ((n : ℝ)/rate)) (((n : ℝ)-rate)^2/(2*rate))
    (stirlingLogError n) (((n : ℝ)-rate)^2/(3*rate))
    ((sqrt (2*π*n))⁻¹) ((sqrt (2*π*rate))⁻¹)
    (stirlingLogError_nonneg hn) (by positivity) hlo (by
      have hr' : (0 : ℝ)<rate := hr
      apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      linarith)
  have he := entropy_central_remainder_le (rate := (rate : ℝ)) hr hc
  have hs := stirlingLogError_le hn
  have hbound := mul_le_mul_of_nonneg_left
    (add_le_add_right (mul_le_mul_of_nonneg_left (add_le_add hs he) (by positivity : 0≤(sqrt (2*π*n))⁻¹))
      |(sqrt (2*π*n))⁻¹-(sqrt (2*π*rate))⁻¹|)
    (exp_pos (-(((n : ℝ)-rate)^2/(3*rate)))).le
  have h := ht.trans (by simpa only [add_comm] using hbound)
  rw [poissonMeasure_real_singleton,poisson_local_exact (rate := (rate : ℝ)) hr hn]
  unfold poissonLocalApprox gaussianLatticeMass
  have hpow : -((((n : ℝ)-rate)/sqrt rate)^2)/2 = -(((n : ℝ)-rate)^2/(2*rate)) := by
    rw [div_pow,sq_sqrt rate.coe_nonneg]
    ring
  rw [hpow]
  simpa only [neg_mul,neg_div,div_eq_mul_inv,mul_assoc,add_comm] using h

end
end PaperC.V282.PoissonQuantitativeAbsolute
