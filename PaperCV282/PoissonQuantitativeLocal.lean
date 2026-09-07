import PaperCV282.PoissonEntropyTaylor
import PaperCV282.PoissonCentralAsymptotics
import Mathlib.Probability.Distributions.Gaussian.Real

/-! # Effective Gaussian local estimates for the true Poisson atom

Stirling's correction and the entropy error are kept separate. The Gaussian
quantity is the genuine standard normal density on the Poisson lattice scale.
No local-limit theorem or normal approximation is assumed.
-/
namespace PaperC.V282.PoissonQuantitativeLocal

open MeasureTheory ProbabilityTheory Real PoissonStirlingBounds PoissonEntropyTaylor
open PoissonCentralAsymptotics
open scoped NNReal

noncomputable section

/-- Standard normal density times the lattice mesh 1/sqrt(rate). -/
def gaussianLatticeMass (rate t : ℝ) : ℝ := exp (-(t^2)/2)/sqrt (2*π*rate)

/-- Exact logarithmic ratio of a Poisson atom to its Gaussian local expression. -/
def localLogCorrection (rate : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (log rate-log n)/2-stirlingLogError n-(rate*poissonEntropy (n/rate)-t^2/2)

/-- Explicit central error size in the actual displacement. -/
def centralError (rate : ℝ) (n : ℕ) : ℝ :=
  1/(12*n)+|(n : ℝ)-rate|/rate+2*|(n : ℝ)-rate|^3/rate^2

theorem gaussianLatticeMass_pos {rate : ℝ} (hr : 0<rate) (t : ℝ) :
    0<gaussianLatticeMass rate t := by unfold gaussianLatticeMass;positivity

theorem gaussianLatticeMass_eq_density {rate : ℝ} (_hr : 0<rate) (t : ℝ) :
    gaussianLatticeMass rate t=gaussianPDFReal 0 1 t/sqrt rate := by
  simp only [gaussianLatticeMass,gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
  rw [sqrt_mul (by positivity : 0≤2*π)]
  ring

/-- Equality for every positive rate, every positive atom, and every real reference coordinate. -/
theorem poisson_atom_exact (rate : ℝ≥0) (hr : 0<rate) {n : ℕ} (hn : 0<n) (t : ℝ) :
    (poissonMeasure rate).real {n}=exp (localLogCorrection rate n t)*gaussianLatticeMass rate t := by
  have hgp : 0<gaussianLatticeMass (rate : ℝ) t := gaussianLatticeMass_pos (rate := (rate : ℝ)) hr t
  rw [poissonMeasure_real_singleton]
  apply log_injOn_pos (by change (0 : ℝ)<_;positivity)
    (by change (0 : ℝ)<_;exact mul_pos (exp_pos _) (gaussianLatticeMass_pos hr t))
  rw [log_div (by positivity) (by positivity),log_mul (by positivity) (by positivity),
    log_exp,log_pow,log_factorial_eq hn,
    log_mul (exp_pos (localLogCorrection (rate : ℝ) n t)).ne' hgp.ne',log_exp]
  unfold gaussianLatticeMass localLogCorrection
  rw [log_div (by positivity) (by positivity),log_exp,
    poisson_entropy_identity (rate := (rate : ℝ)) hr hn,log_sqrt (by positivity),log_sqrt (by positivity),
    log_mul (by positivity) (by positivity),log_mul (by positivity) (by positivity),
    log_mul (by positivity) (by positivity),log_mul (by positivity) (by positivity)]
  ring

/-- A Lipschitz logarithm bound on the literal central interval. -/
theorem central_log_error_le {rate value : ℝ} (hr : 0<rate)
    (hv : |value-rate|≤rate/2) :
    |log value-log rate|≤2*|value-rate|/rate := by
  have hx : |(value-rate)/rate|≤1/2 := by
    rw [abs_div,abs_of_pos hr]
    exact (div_le_iff₀ hr).mpr (by linarith)
  have hrem := log_one_add_remainder_le hx
  have he : 1+(value-rate)/rate=value/rate := by field_simp;ring
  rw [he] at hrem
  have hval : 0<value := by have h := neg_abs_le (value-rate);linarith
  rw [log_div hval.ne' hr.ne'] at hrem
  have ht := abs_add_le ((log value-log rate)-(value-rate)/rate) ((value-rate)/rate)
  rw [sub_add_cancel] at ht
  have hsq : 2*|(value-rate)/rate|^2≤|(value-rate)/rate| := by
    nlinarith [abs_nonneg ((value-rate)/rate)]
  have hb : |log value-log rate|≤2*|(value-rate)/rate| := by linarith
  simpa only [abs_div,abs_of_pos hr,mul_div_assoc] using hb

theorem centralError_nonneg {rate : ℝ} (hr : 0≤rate) (n : ℕ) : 0≤centralError rate n := by
  unfold centralError
  positivity

/-- Uniform logarithmic relative error on the full interval |n-rate| <= rate/2. -/
theorem localLogCorrection_central_le {rate : ℝ} (hr : 0<rate) {n : ℕ} (hn : 0<n)
    (hc : |(n : ℝ)-rate|≤rate/2) :
    |localLogCorrection rate n (((n : ℝ)-rate)/sqrt rate)|≤centralError rate n := by
  have hs := stirlingLogError_nonneg hn
  have ht := stirlingLogError_le hn
  have hl := central_log_error_le hr hc
  have he := entropy_central_remainder_le hr hc
  rw [normalized_coordinate_square hr] at he
  have hb := abs_sub ((log rate-log n)/2-stirlingLogError n)
    (rate*poissonEntropy (n/rate)-(((n : ℝ)-rate)/sqrt rate)^2/2)
  have ha := abs_sub ((log rate-log n)/2) (stirlingLogError n)
  rw [abs_div,abs_of_nonneg (by norm_num : (0 : ℝ)≤2),abs_sub_comm (log rate),abs_of_nonneg hs] at ha
  have hl2 : |log (n : ℝ)-log rate|/2≤|(n : ℝ)-rate|/rate := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ)<2)).mpr
    calc
      _≤2*|(n : ℝ)-rate|/rate := hl
      _=|(n : ℝ)-rate|/rate*2 := by ring
  unfold localLogCorrection centralError
  linarith only [hb,ha,ht,he,hl2]

/-- Effective relative local error, requiring only that its displayed explicit bound is small. -/
theorem poisson_central_relative_error (rate : ℝ≥0) (hr : 0<rate) {n : ℕ} (hn : 0<n)
    (hc : |(n : ℝ)-(rate : ℝ)|≤(rate : ℝ)/2) (he : centralError rate n≤1) :
    |(poissonMeasure rate).real {n}/gaussianLatticeMass rate (((n : ℝ)-rate)/sqrt rate)-1|≤
      2*centralError rate n := by
  have hp : gaussianLatticeMass (rate : ℝ) (((n : ℝ)-rate)/sqrt rate)≠0 :=
    (gaussianLatticeMass_pos (rate := (rate : ℝ)) hr _).ne'
  rw [poisson_atom_exact rate hr hn (((n : ℝ)-rate)/sqrt rate),mul_div_cancel_right₀ _ hp]
  have h := localLogCorrection_central_le hr hn hc
  exact (abs_exp_sub_one_le (h.trans he)).trans (mul_le_mul_of_nonneg_left h (by norm_num))

end
end PaperC.V282.PoissonQuantitativeLocal
