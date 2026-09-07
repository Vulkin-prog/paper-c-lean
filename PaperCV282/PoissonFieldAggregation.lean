import PaperCV282.PoissonFieldMeasure

/-!
# Exact independent Poisson laws for disjoint column sums

Grouping coordinates by their word label preserves mutual independence,
including when the number of labels grows. This is an identity of full
probability laws, not merely a calculation of marginal means.
-/

namespace PaperC.V282.PoissonFieldAggregation

open MeasureTheory ProbabilityTheory PoissonFieldMeasure FiniteFieldPoissonCoupling MassPushforward
open scoped BigOperators NNReal ENNReal

noncomputable section

def columnField {ι κ : Type*} (k : ι × κ → ℕ) : κ → ι → ℕ := fun j i => k (i,j)

/-- Rearrangement of the product coordinates has the product of the column laws. -/
theorem hasLaw_columnField {ι κ : Type*} [Fintype ι] [Fintype κ] (rate : ι × κ → ℝ≥0) :
    HasLaw columnField (Measure.pi (fun j => fieldMeasure (fun i => rate (i,j))))
      (fieldMeasure rate) := by
  classical
  refine ⟨(measurable_of_countable _).aemeasurable, ?_⟩
  apply Measure.ext_of_singleton
  intro k
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have hpre : columnField ⁻¹' {k} = {fun ij : ι × κ => k ij.2 ij.1} := by
    ext x
    simp only [Set.mem_preimage,Set.mem_singleton_iff]
    constructor
    · intro h
      funext ij
      exact congrFun (congrFun h ij.2) ij.1
    · intro h
      subst x
      rfl
  rw [hpre]
  simp only [fieldMeasure,Measure.pi_singleton,Fintype.prod_prod_type]
  exact Finset.prod_comm

/-- The vector of masked column sums consists of mutually independent Poisson variables. -/
theorem hasLaw_column_sums {ι κ : Type*} [Fintype ι] [Fintype κ]
    (rate : ι × κ → ℝ≥0) (s : κ → Finset ι) :
    HasLaw (fun k : ι × κ → ℕ => fun j => ∑ i ∈ s j, k (i,j))
      (fieldMeasure (fun j => ∑ i ∈ s j, rate (i,j))) (fieldMeasure rate) := by
  have hcols : HasLaw (fun k : κ → ι → ℕ => fun j => ∑ i ∈ s j, k j i)
      (fieldMeasure (fun j => ∑ i ∈ s j, rate (i,j)))
      (Measure.pi (fun j => fieldMeasure (fun i => rate (i,j)))) := by
    refine ⟨(measurable_of_countable _).aemeasurable, ?_⟩
    rw [Measure.pi_map_pi (fun _ => (measurable_of_countable _).aemeasurable)]
    congr 1
    funext j
    exact (hasLaw_coordinate_sum (fun i => rate (i,j)) (s j)).map_eq
  exact hcols.fun_comp (hasLaw_columnField rate)

/-- Exact product-mass target of the column-count statistic. -/
theorem pushforward_poissonFieldMass_column_sums {ι κ : Type*} [Fintype ι] [Fintype κ]
    (rate : ι × κ → ℝ≥0) (s : κ → Finset ι) :
    pushforwardMass (fun k : ι × κ → ℕ => fun j => ∑ i ∈ s j, k (i,j))
      (poissonFieldMass rate) = poissonFieldMass (fun j => ∑ i ∈ s j, rate (i,j)) := by
  rw [pushforward_poissonFieldMass_of_hasLaw rate _ _ (hasLaw_column_sums rate s)]
  exact funext (fieldMeasure_real_singleton _)

end
end PaperC.V282.PoissonFieldAggregation
