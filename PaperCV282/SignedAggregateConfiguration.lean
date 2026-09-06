import PaperCV282.SpatialMarkedTypes
import PaperCV282.PoissonFieldAggregation
import PaperCV282.DirectionalSteinComparison

/-! # The actual aggregated signed configuration and its finite projections -/
namespace PaperC.V282.SignedAggregateConfiguration

open SpatialMarkedTypes ExactMarkedModel MeasureTheory ConditionalStartProbability
open PoissonFieldAggregation PoissonFieldMeasure DirectionalSteinComparison
open scoped BigOperators NNReal

noncomputable section

@[reducible]
def SignedAggregateConfig := (ℕ × F₂) →₀ ℕ

instance instMeasurableSignedAggregateConfig : MeasurableSpace SignedAggregateConfig := ⊤

instance instMeasurableSingletonSignedAggregateConfig :
    MeasurableSingletonClass SignedAggregateConfig := by infer_instance

def aggregateSigned (N : ℕ) (config : SpatialMarkedConfig N) : SignedAggregateConfig :=
  config.mapDomain Prod.snd

def finiteSignedAggregate (N E : ℕ) (k : SignedMarkIndex N E → ℕ) (a : Fin (E+1) × F₂) : ℕ :=
  ∑ x : {x : ℕ // x ∈ dyadicBlock N}, k (x,a)

def aggregateMarkEmbedding (E : ℕ) : (Fin (E+1) × F₂) ↪ (ℕ × F₂) where
  toFun a := (a.1.val,a.2)
  inj' := by
    intro a b h
    exact Prod.ext (Fin.ext (congrArg (fun c : ℕ × F₂ => c.1) h)) (congrArg (fun c : ℕ × F₂ => c.2) h)

def embedSignedAggregate (E : ℕ) (k : (Fin (E+1) × F₂) → ℕ) : SignedAggregateConfig :=
  (Finsupp.equivFunOnFinite.symm k).embDomain (aggregateMarkEmbedding E)

def projectSignedAggregate (E : ℕ) (config : SignedAggregateConfig) (a : Fin (E+1) × F₂) : ℕ :=
  config (a.1.val,a.2)

theorem project_embed_signedAggregate (E : ℕ) (k : (Fin (E+1) × F₂) → ℕ) :
    projectSignedAggregate E (embedSignedAggregate E k)=k := by
  funext a
  exact Finsupp.embDomain_apply_self _ _ _

theorem finiteSignedAggregate_finsupp (N E : ℕ) (k : SignedMarkIndex N E → ℕ) :
    (Finsupp.equivFunOnFinite.symm k).mapDomain Prod.snd=
      Finsupp.equivFunOnFinite.symm (finiteSignedAggregate N E k) := by
  classical
  ext a
  simp only [Finsupp.mapDomain,Finsupp.sum_apply]
  rw [Finsupp.sum_fintype]
  · rw [Fintype.sum_prod_type]
    simp [Finsupp.single_apply,finiteSignedAggregate]
  · intro i;simp

/-- Forgetting positions commutes exactly with the finite embedding. -/
theorem aggregate_embed_configuration (N E : ℕ) (k : SignedMarkIndex N E → ℕ) :
    aggregateSigned N (embedConfiguration N E k)=
      embedSignedAggregate E (finiteSignedAggregate N E k) := by
  unfold aggregateSigned embedConfiguration embedSignedAggregate
  simp only [Finsupp.embDomain_eq_mapDomain,← Finsupp.mapDomain_comp]
  have he : (Prod.snd : SpatialMarkedIndex N → ℕ × F₂) ∘ finiteMarkedEmbedding N E=
      aggregateMarkEmbedding E ∘ (Prod.snd : SignedMarkIndex N E → Fin (E+1) × F₂) := rfl
  rw [he,Finsupp.mapDomain_comp,finiteSignedAggregate_finsupp]

/-- Literal category counts coincide with the generic Stein typed sum. -/
theorem finiteSignedAggregate_indicator (N E : ℕ) {Ω : Type*}
    (X : SignedMarkIndex N E → Ω → Bool) (omega : Ω) :
    finiteSignedAggregate N E (fun i => if X i omega=true then 1 else 0)=
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
theorem hasLaw_finiteSignedAggregate (N E : ℕ) (rate : SignedMarkIndex N E → ℝ≥0) :
    ProbabilityTheory.HasLaw (finiteSignedAggregate N E)
      (fieldMeasure (fun a => ∑ x : {x : ℕ // x ∈ dyadicBlock N}, rate (x,a)))
      (fieldMeasure rate) :=
  hasLaw_column_sums rate (fun _ => Finset.univ)

end
end PaperC.V282.SignedAggregateConfiguration
