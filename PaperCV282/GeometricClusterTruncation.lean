import PaperCV282.GeometricClusterTarget
import PaperCV282.CompoundPoissonTransform

/-!
# Exact finite Poisson targets as truncated compound random sums

A mark above the retained excess cutoff is deleted, rather than shortened.
The independent Poisson coordinates at excess e have rate lambda/2^(e+1).
Their weighted sum is identified with an actual compound random sum.
-/

namespace PaperC.V282.GeometricClusterTruncation

open MeasureTheory ProbabilityTheory CompoundPoissonTarget CompoundPoissonTransform
open GeometricClusterTarget PoissonFieldMeasure
open scoped BigOperators NNReal ENNReal

noncomputable section

def truncateMark (E h : ℕ) : ℕ := if h ≤ E + 1 then h else 0

def truncatedGeometricMeasure (E : ℕ) : Measure ℕ :=
  geometricClusterMeasure.map (truncateMark E)

instance instProbabilityTruncatedGeometric (E : ℕ) :
    IsProbabilityMeasure (truncatedGeometricMeasure E) := by
  unfold truncatedGeometricMeasure
  exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

theorem truncated_power_identity (E h : ℕ) (z : ℂ) :
    z ^ truncateMark E h = 1 + ∑ e ∈ Finset.range (E + 1),
      if h = e + 1 then z ^ (e + 1) - 1 else 0 := by
  cases h with
  | zero => simp [truncateMark]
  | succ h =>
    simp only [Nat.add_right_cancel_iff]
    rw [Finset.sum_ite_eq]
    by_cases hE : h < E + 1
    · simp [truncateMark, hE, show h + 1 ≤ E + 1 by omega]
    · simp [truncateMark, hE, show ¬h + 1 ≤ E + 1 by omega]

theorem integral_truncated_mark_powers (mu : Measure ℕ) [IsProbabilityMeasure mu]
    (E : ℕ) (z : ℂ) :
    (∫ h, z ^ truncateMark E h ∂mu) =
      1 + ∑ e ∈ Finset.range (E + 1), (mu.real {e + 1} : ℂ) * (z ^ (e + 1) - 1) := by
  have hi (e : ℕ) : Integrable (fun h : ℕ => if h = e + 1 then z ^ (e + 1) - 1 else 0) mu := by
    have heq : (fun h : ℕ => if h = e + 1 then z ^ (e + 1) - 1 else 0) =
        ({e + 1} : Set ℕ).indicator (fun _ => z ^ (e + 1) - 1) := by
      funext h
      by_cases hh : h = e + 1 <;> simp [hh]
    rw [heq]
    exact (integrable_const _).indicator (measurableSet_singleton _)
  simp_rw [truncated_power_identity]
  rw [integral_add (integrable_const _) (integrable_finsetSum _ (fun e _ => hi e)),
    integral_const, integral_finsetSum _ (fun e _ => hi e)]
  simp only [probReal_univ, one_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  have h := integral_indicator_const (μ := mu) (z ^ (e + 1) - 1) (measurableSet_singleton (e + 1))
  simpa only [Set.indicator, Set.mem_singleton_iff, Complex.real_smul] using h

theorem truncated_geometric_complex_transform (E : ℕ) (z : ℂ) :
    (∫ h, z ^ h ∂truncatedGeometricMeasure E) =
      1 + ∑ e ∈ Finset.range (E + 1),
        (1 / (2 : ℂ) ^ (e + 1)) * (z ^ (e + 1) - 1) := by
  rw [truncatedGeometricMeasure, integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable (fun h : ℕ => z ^ h)).aestronglyMeasurable,
    integral_truncated_mark_powers]
  simp only [geometricClusterMeasure_real_succ, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_pow, Complex.ofReal_ofNat]

theorem weighted_poisson_complex_transform {I : Type*} [Fintype I]
    (rate : I → ℝ≥0) (weight : I → ℕ) (z : ℂ) :
    (∫ k : I → ℕ, z ^ (∑ i, weight i * k i) ∂fieldMeasure rate) =
      Complex.exp (∑ i, (rate i : ℂ) * (z ^ weight i - 1)) := by
  classical
  have hdep := (independent_coordinates rate).comp
    (fun i => fun n : ℕ => (z ^ weight i) ^ n) (fun _ => measurable_of_countable _)
  have hp := hdep.integral_fun_prod_eq_prod_integral
    (fun i => ((measurable_of_countable (fun n : ℕ => (z ^ weight i) ^ n)).comp
      (measurable_pi_apply i)).aestronglyMeasurable)
  have hi (i : I) :
      (∫ k : I → ℕ, (z ^ weight i) ^ k i ∂fieldMeasure rate) =
        Complex.exp ((rate i : ℂ) * (z ^ weight i - 1)) := by
    exact ((hasLaw_coordinate rate i).integral_comp
      (measurable_of_countable (fun n : ℕ => (z ^ weight i) ^ n)).aestronglyMeasurable).trans
        (integral_poisson_complex_powers _ _)
  simp only [Function.comp_apply] at hp
  simp_rw [hi] at hp
  rw [← Complex.exp_sum] at hp
  convert hp using 1
  congr 1
  funext k
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro i hi
  exact pow_mul _ _ _

def geometricCoordinateRates (rate : ℝ≥0) (E : ℕ) (e : Fin (E + 1)) : ℝ≥0 :=
  rate / 2 ^ (e.val + 1)

def weightedGeometricPoissonMeasure (rate : ℝ≥0) (E : ℕ) : Measure ℕ :=
  (fieldMeasure (geometricCoordinateRates rate E)).map
    (fun k => ∑ e : Fin (E + 1), (e.val + 1) * k e)

instance instProbabilityWeightedGeometric (rate : ℝ≥0) (E : ℕ) :
    IsProbabilityMeasure (weightedGeometricPoissonMeasure rate E) := by
  unfold weightedGeometricPoissonMeasure
  exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

/-- The full finite-coordinate target equals a genuine truncated compound law. -/
theorem weightedGeometricPoisson_eq_compound (rate : ℝ≥0) (E : ℕ) :
    weightedGeometricPoissonMeasure rate E = compoundMeasure rate (truncatedGeometricMeasure E) := by
  apply natural_law_eq_of_unit_transforms
  intro z hz
  rw [weightedGeometricPoissonMeasure, integral_map
    (measurable_of_countable _).aemeasurable
    (measurable_of_countable (fun n : ℕ => z ^ n)).aestronglyMeasurable,
    weighted_poisson_complex_transform,
    compound_complex_transform rate (truncatedGeometricMeasure E) hz.le,
    truncated_geometric_complex_transform]
  congr 1
  rw [add_sub_cancel_left, Finset.mul_sum]
  simp only [geometricCoordinateRates, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat]
  push_cast
  rw [Fin.sum_univ_eq_sum_range
    (fun e : ℕ => (rate : ℂ) / (2 : ℂ) ^ (e + 1) * (z ^ (e + 1) - 1)) (E + 1)]
  apply Finset.sum_congr rfl
  intro e he
  ring

end
end PaperC.V282.GeometricClusterTruncation
