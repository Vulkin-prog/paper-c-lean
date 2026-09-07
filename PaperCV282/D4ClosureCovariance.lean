import PaperCV282.D4ClosureThreshold
import PaperCV282.PoissonQuantitativeMoments
import Mathlib.Probability.Moments.Covariance

/-! # Exact covariance of the actual Poisson threshold process -/
namespace PaperC.V282.D4ClosureCovariance

open MeasureTheory ProbabilityTheory
open PoissonFieldMeasure PoissonPolynomialIntegrability PoissonQuantitativeMoments
open D4ClosureThreshold PoissonThresholdTarget GaussianThresholdIncrements
open ThresholdPathEquivalence GeometricMarkedConfiguration
open scoped BigOperators NNReal

noncomputable section

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

theorem poisson_coordinate_memLp_two {I : Type*} [Fintype I]
    (rate : I → ℝ≥0) (i : I) :
    MemLp (fun k : I → ℕ => (k i : ℝ)) 2 (fieldMeasure rate) := by
  apply (memLp_two_iff_integrable_sq (measurable_of_countable _).aestronglyMeasurable).2
  simpa only [pow_two] using integrable_poisson_coordinate_mul rate i i

theorem poisson_coordinate_covariance {I : Type*} [Fintype I] [DecidableEq I]
    (rate : I → ℝ≥0) (i j : I) :
    covariance (fun k : I → ℕ => (k i : ℝ)) (fun k => (k j : ℝ)) (fieldMeasure rate) =
      if i = j then (rate i : ℝ) else 0 := by
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, covariance]
    have hmean : (∫ k : I → ℕ, (k i : ℝ) ∂fieldMeasure rate) = rate i :=
      ((hasLaw_coordinate rate i).integral_comp
        (measurable_of_countable (fun n : ℕ => (n : ℝ))).aestronglyMeasurable).trans
          (poisson_mean (rate i))
    rw [hmean]
    simp_rw [← pow_two]
    exact ((hasLaw_coordinate rate i).integral_comp
      (measurable_of_countable (fun n : ℕ => ((n : ℝ)-(rate i : ℝ))^2)).aestronglyMeasurable).trans
        (poisson_centered_second (rate i))
  · rw [if_neg hij]
    exact (((independent_coordinates rate).indepFun hij).comp
      (measurable_of_countable (fun n : ℕ => (n : ℝ)))
      (measurable_of_countable (fun n : ℕ => (n : ℝ)))).covariance_eq_zero
        (poisson_coordinate_memLp_two rate i) (poisson_coordinate_memLp_two rate j)

theorem poisson_selected_sum_covariance {I : Type*} [Fintype I] [DecidableEq I]
    (rate : I → ℝ≥0) (a b : I → Prop) :
    covariance (fun k : I → ℕ => ∑ i, if a i then (k i : ℝ) else 0)
      (fun k => ∑ j, if b j then (k j : ℝ) else 0) (fieldMeasure rate) =
        ∑ i, if a i ∧ b i then (rate i : ℝ) else 0 := by
  classical
  have hmem (p : I → Prop) (i : I) :
      MemLp (fun k : I → ℕ => if p i then (k i : ℝ) else 0) 2 (fieldMeasure rate) := by
    by_cases hi : p i
    · simpa only [if_pos hi] using poisson_coordinate_memLp_two rate i
    · simpa only [if_neg hi] using (memLp_const (0 : ℝ) : MemLp (fun _ : I → ℕ => (0 : ℝ)) 2 (fieldMeasure rate))
  rw [covariance_fun_sum_fun_sum (hmem a) (hmem b)]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hai : a i
  · simp only [if_pos hai]
    have hpoint (j : I) : covariance (fun k : I → ℕ => (k i : ℝ))
        (fun k => if b j then (k j : ℝ) else 0) (fieldMeasure rate) =
          if i = j then (if b i then (rate i : ℝ) else 0) else 0 := by
      by_cases hij : i = j
      · subst j
        by_cases hb : b i <;> simp [hb, poisson_coordinate_covariance]
      · by_cases hb : b j <;> simp [hb, poisson_coordinate_covariance, hij]
    simp_rw [hpoint]
    simp [hai]
  · simp [hai]

/-- The printed covariance, for the true infinite-tail counts. -/
theorem threshold_covariance (rate : ℝ≥0) (k l : ℕ) :
    covariance (fun c => (tailCount c k : ℝ)) (fun c => (tailCount c l : ℝ))
      (configurationMeasure rate) = (rate : ℝ) / 2^(max k l) := by
  classical
  let J := max k l
  let rates := fun i : Fin (J+1) => rate * incrementVariance J i
  have hsum (a : ℕ) (ha : a ≤ J) (c : ℕ →₀ ℕ) :
      (∑ i : Fin (J+1), if a ≤ i.val then (clippedCounts J c i : ℝ) else 0) =
        (tailCount c a : ℝ) := by
    exact_mod_cast sum_clippedCounts_tail J a ha c
  have heq := covariance_map_fun
    (μ := configurationMeasure rate) (Z := clippedCounts J)
    (X := fun v : Fin (J+1) → ℕ => ∑ i, if k ≤ i.val then (v i : ℝ) else 0)
    (Y := fun v => ∑ i, if l ≤ i.val then (v i : ℝ) else 0)
    (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_countable _).aemeasurable
  rw [(hasLaw_clippedCounts rate J).map_eq] at heq
  simp_rw [hsum k (le_max_left _ _), hsum l (le_max_right _ _)] at heq
  rw [← heq]
  have hsel := poisson_selected_sum_covariance rates (fun i => k ≤ i.val) (fun i => l ≤ i.val)
  have hsel' : covariance
      (fun v : Fin (J+1) → ℕ => ∑ i, if k ≤ i.val then (v i : ℝ) else 0)
      (fun v => ∑ i, if l ≤ i.val then (v i : ℝ) else 0) (fieldMeasure rates) =
        ∑ i, if k ≤ i.val ∧ l ≤ i.val then (rates i : ℝ) else 0 := by
    convert hsel using 1 <;> congr! 4
  rw [hsel']
  have he (i : Fin (J+1)) :
      (if k ≤ i.val ∧ l ≤ i.val then ((rates i : ℝ≥0) : ℝ) else 0) =
        (rate : ℝ) * (if J ≤ i.val then (incrementVariance J i : ℝ) else 0) := by
    simp only [← max_le_iff, rates, NNReal.coe_mul]
    split_ifs <;> simp_all [J]
  change (∑ i : Fin (J+1), if k ≤ i.val ∧ l ≤ i.val then (rates i : ℝ) else 0) = _
  simp_rw [he]
  rw [← Finset.mul_sum, sum_tail_incrementVariance J J le_rfl]
  simp [J, div_eq_mul_inv]

end
end PaperC.V282.D4ClosureCovariance
