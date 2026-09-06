import PaperCV282.PoissonFillingIdentity
import Mathlib.Analysis.Complex.Exponential

/-!
# Polynomial integrability for the actual independent Poisson filling

Every scalar moment is dominated by an exponential series. Product-field
coordinates and their cross products are then controlled by the genuine
Poisson total. These facts justify linearity in the Stein filling argument.
-/
namespace PaperC.V282.PoissonPolynomialIntegrability

open MeasureTheory ProbabilityTheory PoissonFieldMeasure PoissonFillingIdentity
open scoped BigOperators NNReal

noncomputable section

theorem integrable_poisson_nat_pow (rate : ℝ≥0) (k : ℕ) :
    Integrable (fun n : ℕ => (n : ℝ)^k) (poissonMeasure rate) := by
  rw [integrable_poissonMeasure_iff]
  have hs := (NormedSpace.expSeries_div_hasSum_exp ((rate : ℝ)*Real.exp 1)).summable.mul_left
    ((k.factorial : ℝ)*Real.exp (-(rate : ℝ)))
  apply hs.of_nonneg_of_le (fun n => by positivity)
  intro n
  rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (Nat.cast_nonneg _) _)]
  have hfact : (0 : ℝ)<k.factorial := by positivity
  have hpow := (div_le_iff₀ hfact).mp (Real.pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg n) k)
  have he : Real.exp (n : ℝ)=(Real.exp 1)^n := by
    simp [← Real.exp_nat_mul]
  calc
    _ ≤ (Real.exp (-(rate : ℝ))*(rate : ℝ)^n/(n.factorial : ℝ))*
        (Real.exp (n : ℝ)*(k.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by rw [he,mul_pow];ring

/-- Integrability is transferred along a genuine law, not inferred from the value of an integral. -/
theorem integrable_poisson_total_pow {ι : Type*} [Fintype ι]
    (rate : ι → ℝ≥0) (k : ℕ) :
    Integrable (fun z : ι → ℕ => (∑ i, (z i : ℝ))^k) (fieldMeasure rate) := by
  have hlaw := hasLaw_coordinate_sum rate Finset.univ
  have h := (hlaw.measurePreserving (measurable_of_countable _)).integrable_comp_of_integrable
    (integrable_poisson_nat_pow (∑ i, rate i) k)
  simpa only [Nat.cast_sum,Function.comp_def] using h

theorem integrable_poisson_coordinate {ι : Type*} [Fintype ι]
    (rate : ι → ℝ≥0) (i : ι) :
    Integrable (fun z : ι → ℕ => (z i : ℝ)) (fieldMeasure rate) := by
  have h := ((hasLaw_coordinate rate i).measurePreserving (measurable_of_countable _)).integrable_comp_of_integrable
    (integrable_poisson_nat_pow (rate i) 1)
  simpa only [pow_one,Function.comp_def] using h

theorem coordinate_le_total {ι : Type*} [Fintype ι] (z : ι → ℕ) (i : ι) :
    (z i : ℝ)≤∑ j, (z j : ℝ) :=
  Finset.single_le_sum (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ i)

theorem integrable_poisson_coordinate_mul {ι : Type*} [Fintype ι]
    (rate : ι → ℝ≥0) (i j : ι) :
    Integrable (fun z : ι → ℕ => (z i : ℝ)*(z j : ℝ)) (fieldMeasure rate) := by
  apply (integrable_poisson_total_pow rate 2).mono' (measurable_of_countable _).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  have h := mul_le_mul (coordinate_le_total z i) (coordinate_le_total z j)
    (Nat.cast_nonneg _) (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))
  simpa only [pow_two] using h

/-- Affine growth under the true filling law is integrable. -/
theorem integrable_of_affine_bound {ι : Type*} [Fintype ι]
    (rate : ι → ℝ≥0) (f : (ι → ℕ) → ℝ) (A B : ℝ)
    (hf : ∀ z, |f z|≤A+B*(∑ i, (z i : ℝ))) : Integrable f (fieldMeasure rate) := by
  have h := (integrable_const A).add ((integrable_poisson_total_pow rate 1).const_mul B)
  simp only [pow_one] at h
  exact h.mono' (measurable_of_countable _).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs,Pi.add_apply] using hf z))

/-- Quadratic growth controls a coordinate multiplied by a Stein gradient. -/
theorem integrable_of_quadratic_bound {ι : Type*} [Fintype ι]
    (rate : ι → ℝ≥0) (f : (ι → ℕ) → ℝ) (A B C : ℝ)
    (hf : ∀ z, |f z|≤A+B*(∑ i, (z i : ℝ))+C*(∑ i, (z i : ℝ))^2) :
    Integrable f (fieldMeasure rate) := by
  have h := ((integrable_const A).add ((integrable_poisson_total_pow rate 1).const_mul B)).add
    ((integrable_poisson_total_pow rate 2).const_mul C)
  simp only [pow_one] at h
  exact h.mono' (measurable_of_countable _).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs,Pi.add_apply] using hf z))

end
end PaperC.V282.PoissonPolynomialIntegrability
