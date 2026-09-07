import PaperCV282.BulkMarkedTypes
import PaperCV282.SignedAggregateConfiguration
import PaperCV282.PoissonFieldAggregation
import PaperCV282.DirectionalSteinComparison

/-! # The actual aggregated signed configuration and its finite projections -/
namespace PaperC.V282.MacroAggregateModel

open BulkMarkedTypes SignedAggregateConfiguration ExactMarkedModel MeasureTheory ConditionalStartProbability
open PoissonFieldAggregation PoissonFieldMeasure DirectionalSteinComparison
open scoped BigOperators NNReal

noncomputable section

def aggregateSigned (sites : Finset ℕ) (config : SpatialMarkedConfig sites) : SignedAggregateConfig :=
  config.mapDomain Prod.snd

def finiteSignedAggregate (sites : Finset ℕ) (E : ℕ) (k : BulkSupportGraph.LabelledIndex sites (Fin (E+1) × F₂) → ℕ) (a : Fin (E+1) × F₂) : ℕ :=
  ∑ x : {x : ℕ // x ∈ sites}, k (x,a)

theorem finiteSignedAggregate_finsupp (sites : Finset ℕ) (E : ℕ) (k : BulkSupportGraph.LabelledIndex sites (Fin (E+1) × F₂) → ℕ) :
    (Finsupp.equivFunOnFinite.symm k).mapDomain Prod.snd=
      Finsupp.equivFunOnFinite.symm (finiteSignedAggregate sites E k) := by
  classical
  ext a
  simp only [Finsupp.mapDomain,Finsupp.sum_apply]
  rw [Finsupp.sum_fintype]
  · rw [Fintype.sum_prod_type]
    simp [Finsupp.single_apply,finiteSignedAggregate]
  · intro i;simp

/-- Forgetting positions commutes exactly with the finite embedding. -/
theorem aggregate_embed_configuration (sites : Finset ℕ) (E : ℕ) (k : BulkSupportGraph.LabelledIndex sites (Fin (E+1) × F₂) → ℕ) :
    aggregateSigned sites (embedConfiguration sites E k)=
      embedSignedAggregate E (finiteSignedAggregate sites E k) := by
  unfold aggregateSigned embedConfiguration embedSignedAggregate
  simp only [Finsupp.embDomain_eq_mapDomain,← Finsupp.mapDomain_comp]
  have he : (Prod.snd : SpatialMarkedIndex sites → ℕ × F₂) ∘ finiteMarkedEmbedding sites E=
      aggregateMarkEmbedding E ∘ (Prod.snd : BulkSupportGraph.LabelledIndex sites (Fin (E+1) × F₂) → Fin (E+1) × F₂) := rfl
  rw [he,Finsupp.mapDomain_comp,finiteSignedAggregate_finsupp]

/-- Literal category counts coincide with the generic Stein typed sum. -/
theorem finiteSignedAggregate_indicator (sites : Finset ℕ) (E : ℕ) {Ω : Type*}
    (X : BulkSupportGraph.LabelledIndex sites (Fin (E+1) × F₂) → Ω → Bool) (omega : Ω) :
    finiteSignedAggregate sites E (fun i => if X i omega=true then 1 else 0)=
      typedSum X Prod.snd Finset.univ omega := by
  classical
  funext a
  unfold finiteSignedAggregate typedSum
  rw [Finset.sum_apply,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [ite_apply,Pi.single_apply,Pi.zero_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b hb hba
    by_cases h : X (x,b) omega=true <;> simp [h,Ne.symm hba]
  · simp

/-- Actual independent site coordinates aggregate to the product of their summed rates. -/
theorem hasLaw_finiteSignedAggregate (sites : Finset ℕ) (E : ℕ) (rate : BulkSupportGraph.LabelledIndex sites (Fin (E+1) × F₂) → ℝ≥0) :
    ProbabilityTheory.HasLaw (finiteSignedAggregate sites E)
      (fieldMeasure (fun a => ∑ x : {x : ℕ // x ∈ sites}, rate (x,a)))
      (fieldMeasure rate) :=
  hasLaw_column_sums rate (fun _ => Finset.univ)

end
end PaperC.V282.MacroAggregateModel
