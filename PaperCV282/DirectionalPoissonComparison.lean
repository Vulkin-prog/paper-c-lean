import PaperCV282.DirectionalSteinIntegration

/-! # Directional Poisson comparison with genuine independent filling

The only external input is the published Stein equation and its two quadratic
Hessian bounds. Graph telescoping, entry extraction, growth, integrability,
Poisson cancellation and the total-variation comparison are proved here.
-/
namespace PaperC.V282.DirectionalPoissonComparison

open MeasureTheory DirectionalSteinInput DirectionalHessian DirectionalSteinComparison
open DirectionalSteinIntegration PoissonFilling PoissonFieldMeasure InfiniteMassCoupling
open FiniteFieldTotalVariation FiniteFieldPoissonCoupling ArratiaGoldsteinGordonInput
open IndependentThinning SteinFiniteExpectation
open scoped BigOperators NNReal

noncomputable section

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

variable {Ω ι κ : Type} [Fintype Ω] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] in
/-- A Stein solution evaluates the discrepancy of the actual filled law. -/
theorem filled_generator_test_identity (mu : FinitePMF Ω) (X : ι → Ω → Bool) (kind : ι → κ)
    (fill t : κ → ℝ≥0) (g : (κ → ℕ) → ℝ) (A : Set (κ → ℕ))
    (hEq : ∀ z, steinGenerator t g z=(if z∈A then 1 else 0)-poissonTestMass t A) :
    finitePMFExpectation mu (fun omega =>
      ∫ z, steinGenerator t g (z+typedSum X kind Finset.univ omega) ∂fieldMeasure fill)=
      (∑' k, if k∈A then filledLaw mu X kind fill k else 0)-poissonTestMass t A := by
  have heq (omega : Ω) :
      (∫ z, steinGenerator t g (z+typedSum X kind Finset.univ omega) ∂fieldMeasure fill)=
      (fieldMeasure fill).real {z | z+typedSum X kind Finset.univ omega∈A}-poissonTestMass t A := by
    have hi : Integrable (fun z => if z+typedSum X kind Finset.univ omega∈A then (1 : ℝ) else 0)
        (fieldMeasure fill) := by
      exact Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
        (Filter.Eventually.of_forall (fun z => by split_ifs <;> norm_num))
    have he := integral_indicator_one (μ := fieldMeasure fill)
      ((Set.to_countable {z | z+typedSum X kind Finset.univ omega∈A}).measurableSet)
    simp only [Set.indicator_apply,Pi.one_apply,Set.mem_setOf_eq] at he
    simp_rw [hEq]
    rw [integral_sub hi (integrable_const _),he,integral_const]
    simp
  simp_rw [heq]
  rw [expectation_sub,expectation_const,← restricted_filledLaw_eq]

/-- The exact entrywise dependency-graph bound, valid even with no retained sites. -/
theorem directional_poisson_filling_comparison
    (hStein : DirectionalSteinFactorsStatement) (hcard : 2≤Fintype.card κ)
    (mu : FinitePMF Ω) (X : ι → Ω → Bool) (kind : ι → κ)
    (G : SimpleGraph ι) (hdep : HasExactDependencyGraph mu X G)
    (fill t : κ → ℝ≥0) (ht : ∀ j, 0<t j)
    (hbalance : ∀ j, t j=fill j+categoryRate mu X kind j) :
    massTotalVariation (filledLaw mu X kind fill) (poissonFieldMass t)≤
      typedCost mu X kind G (entryFactor t) := by
  apply massTotalVariation_le_of_test_sets (hasSum_filledLaw mu X kind fill)
    (hasSum_poissonFieldMass t) (filledLaw_nonneg mu X kind fill) (poissonFieldMass_nonneg t)
  intro A
  obtain ⟨g,hEq,hOne,hWeighted⟩ := hStein κ hcard t ht A
  have hentry := secondDifference_le_entryFactor t ht g hOne hWeighted
  have hsecond (z : κ → ℕ) (i j : κ) : |secondDifference g i j z|≤1 :=
    (hentry z i j).trans (entryFactor_le_one t i j)
  change |(∑' k, if k∈A then filledLaw mu X kind fill k else 0)-poissonTestMass t A|≤_
  rw [← filled_generator_test_identity mu X kind fill t g A hEq,
    average_integral_generator_eq_error mu X kind fill t hbalance g hsecond]
  exact integral_typed_error_le mu X kind G hdep (firstDifference g) (entryFactor t)
    (by intro i z j;rw [firstDifference_addPoint];exact hentry z i j) fill

/-- The same theorem stated on the genuine independent product probability space. -/
theorem directional_product_poisson_comparison [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (hStein : DirectionalSteinFactorsStatement) (hcard : 2≤Fintype.card κ)
    (mu : FinitePMF Ω) (X : ι → Ω → Bool) (kind : ι → κ)
    (G : SimpleGraph ι) (hdep : HasExactDependencyGraph mu X G)
    (fill t : κ → ℝ≥0) (ht : ∀ j, 0<t j)
    (hbalance : ∀ j, t j=fill j+categoryRate mu X kind j) :
    massTotalVariation (observableLaw (fillingMeasure mu fill)
      (fun pair => pair.2+typedSum X kind Finset.univ pair.1)) (poissonFieldMass t)≤
      typedCost mu X kind G (entryFactor t) := by
  rw [← filledLaw_eq_product]
  exact directional_poisson_filling_comparison hStein hcard mu X kind G hdep fill t ht hbalance

end
end PaperC.V282.DirectionalPoissonComparison
