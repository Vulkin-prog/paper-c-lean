import PaperCV282.PoissonPolynomialIntegrability
import Mathlib.Probability.Distributions.Gaussian.Real

/-! # Exact moments and exterior tails of the two genuine probability laws -/
namespace PaperC.V282.PoissonQuantitativeMoments

open MeasureTheory ProbabilityTheory Real PoissonPolynomialIntegrability PoissonFillingIdentity
open scoped NNReal

noncomputable section

theorem poisson_shift_integral (rate : ℝ≥0) (f : ℕ→ℝ)
    (hf : Integrable f (poissonMeasure rate)) :
    (∫ n, (n : ℝ)*f (n-1) ∂poissonMeasure rate)=(rate : ℝ)*(∫ n,f n ∂poissonMeasure rate) := by
  have hs := (hasSum_integral_poissonMeasure hf).mul_left (rate : ℝ)
  simp only [smul_eq_mul] at hs
  have hshift : HasSum (fun n : ℕ =>
      ScalarSteinInput.poissonMass rate (n+1)*((n+1 : ℕ) : ℝ)*f n)
      ((rate : ℝ)*(∫ n,f n ∂poissonMeasure rate)) := by
    apply HasSum.congr_fun hs
    intro n
    rw [mul_comm (ScalarSteinInput.poissonMass rate (n+1)),poisson_mass_recurrence]
    simp only [ScalarSteinInput.poissonMass,poissonMeasure_real_singleton]
    ring
  have hall : HasSum (fun n : ℕ => ScalarSteinInput.poissonMass rate n*((n : ℝ)*f (n-1)))
      ((rate : ℝ)*(∫ n,f n ∂poissonMeasure rate)) := by
    rw [← hasSum_nat_add_iff' 1]
    simpa only [Finset.sum_range_one,Nat.cast_zero,zero_mul,mul_zero,sub_zero,
      Nat.add_sub_cancel,mul_assoc] using hshift
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  simpa only [ScalarSteinInput.poissonMass,poissonMeasure_real_singleton] using hall.tsum_eq

theorem poisson_mean (rate : ℝ≥0) :
    (∫ n : ℕ,(n : ℝ) ∂poissonMeasure rate)=rate := by
  simpa using poisson_shift_integral rate (fun _ => 1) (integrable_const _)

theorem poisson_factorial_second (rate : ℝ≥0) :
    (∫ n : ℕ,(n : ℝ)*((n : ℝ)-1) ∂poissonMeasure rate)=(rate : ℝ)^2 := by
  have hi : Integrable (fun n : ℕ => (n : ℝ)) (poissonMeasure rate) := by
    simpa using integrable_poisson_nat_pow rate 1
  have h := poisson_shift_integral rate (fun n => (n : ℝ)) hi
  rw [poisson_mean] at h
  convert h using 1
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall fun n => by
      cases n with
      | zero => simp
      | succ n => simp only [Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel];ring
  · ring

theorem poisson_centered_second (rate : ℝ≥0) :
    (∫ n : ℕ,((n : ℝ)-(rate : ℝ))^2 ∂poissonMeasure rate)=rate := by
  have hi : Integrable (fun n : ℕ => (n : ℝ)) (poissonMeasure rate) := by
    simpa using integrable_poisson_nat_pow rate 1
  have hi2 := integrable_poisson_nat_pow rate 2
  have hf : Integrable (fun n : ℕ => (n : ℝ)*((n : ℝ)-1)) (poissonMeasure rate) := by
    convert hi2.sub hi using 1
    ext n
    simp only [Pi.sub_apply]
    ring
  have he (n : ℕ) : ((n : ℝ)-(rate : ℝ))^2=
      (n : ℝ)*((n : ℝ)-1)+(1-2*(rate : ℝ))*(n : ℝ)+(rate : ℝ)^2 := by ring
  simp_rw [he]
  have hlin : Integrable (fun n : ℕ => (1-2*(rate : ℝ))*(n : ℝ)) (poissonMeasure rate) := hi.const_mul _
  have hconst : Integrable (fun _ : ℕ => (rate : ℝ)^2) (poissonMeasure rate) := integrable_const _
  have hsum := integral_add (hf.add hlin) hconst
  have hsum2 := integral_add hf hlin
  simp only [Pi.add_apply] at hsum hsum2
  rw [hsum,hsum2,integral_const_mul,poisson_factorial_second,poisson_mean]
  simp only [integral_const,probReal_univ,one_smul]
  ring

theorem poisson_outer_tail (rate : ℝ≥0) (R : ℝ) (hR : 0<R) :
    (poissonMeasure rate).real {n : ℕ | R≤|(n : ℝ)-(rate : ℝ)|}≤(rate : ℝ)/R^2 := by
  have hi : Integrable (fun n : ℕ => ((n : ℝ)-(rate : ℝ))^2) (poissonMeasure rate) := by
    have h1 : Integrable (fun n : ℕ => (n : ℝ)) (poissonMeasure rate) := by
      simpa using integrable_poisson_nat_pow rate 1
    have hh : Integrable (fun n : ℕ => (n : ℝ)^2-2*(rate : ℝ)*(n : ℝ)+(rate : ℝ)^2) (poissonMeasure rate) :=
      ((integrable_poisson_nat_pow rate 2).sub (h1.const_mul (2*(rate : ℝ)))).add (integrable_const _)
    apply hh.congr
    exact Filter.Eventually.of_forall fun n => by ring
  have h := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun n : ℕ => sq_nonneg ((n : ℝ)-(rate : ℝ))) hi (R^2)
  rw [poisson_centered_second] at h
  have he : {n : ℕ | R^2≤((n : ℝ)-(rate : ℝ))^2}={n : ℕ | R≤|(n : ℝ)-(rate : ℝ)|} := by
    ext n
    simp only [Set.mem_setOf_eq,← sq_abs ((n : ℝ)-(rate : ℝ))]
    exact sq_le_sq₀ hR.le (abs_nonneg _)
  rw [he] at h
  exact (le_div_iff₀ (sq_pos_of_pos hR)).mpr (by simpa only [mul_comm] using h)

theorem gaussian_centered_second : (∫ x : ℝ,x^2 ∂gaussianReal 0 1)=1 := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa using h

theorem gaussian_outer_tail (R : ℝ) (hR : 0<R) :
    (gaussianReal 0 1).real {x : ℝ | R≤|x|}≤1/R^2 := by
  have hi : Integrable (fun x : ℝ => x^2) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal 2).integrable_sq
  have h := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun x : ℝ => sq_nonneg x) hi (R^2)
  rw [gaussian_centered_second] at h
  have he : {x : ℝ | R^2≤x^2}={x : ℝ | R≤|x|} := by
    ext x
    simp only [Set.mem_setOf_eq,← sq_abs x]
    exact sq_le_sq₀ hR.le (abs_nonneg _)
  rw [he] at h
  exact (le_div_iff₀ (sq_pos_of_pos hR)).mpr (by simpa only [mul_comm] using h)

end
end PaperC.V282.PoissonQuantitativeMoments
