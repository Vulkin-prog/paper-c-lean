import PaperCV282.SignedAggregateConfiguration
import PaperCV282.MovingMarkedSource

/-! # Exact coefficient formulas for counts with positions and signs forgotten -/
namespace PaperC.V282.AggregateCoordinateIdentities

open SignedAggregateConfiguration SpatialMarkedTypes ExactMarkedModel MovingMarkedSource
open ConditionalStartProbability
open scoped BigOperators

noncomputable section

theorem mapDomain_snd_apply {α β : Type*} [Fintype α] (config : α × β →₀ ℕ) (b : β) :
    config.mapDomain Prod.snd b=∑ a, config (a,b) := by
  classical
  induction config using Finsupp.induction_linear with
  | zero => simp
  | single ab n =>
    rcases ab with ⟨a,b'⟩
    by_cases h : b'=b
    · subst b';simp [Finsupp.single_apply]
    · simp [h]
  | add f g hf hg =>
    rw [Finsupp.mapDomain_add,Finsupp.add_apply,hf,hg]
    simp [Finset.sum_add_distrib]

theorem mapDomain_fst_apply {α β : Type*} [Fintype β] (config : α × β →₀ ℕ) (a : α) :
    config.mapDomain Prod.fst a=∑ b, config (a,b) := by
  classical
  induction config using Finsupp.induction_linear with
  | zero => simp
  | single ab n =>
    rcases ab with ⟨a',b⟩
    by_cases h : a'=a
    · subst a';simp [Finsupp.single_apply]
    · simp [h]
  | add f g hf hg =>
    rw [Finsupp.mapDomain_add,Finsupp.add_apply,hf,hg]
    simp [Finset.sum_add_distrib]

def forgetAggregateSigns (config : SignedAggregateConfig) : ℕ →₀ ℕ := config.mapDomain Prod.fst

theorem forget_aggregateSigned (N : ℕ) (config : SpatialMarkedConfig N) :
    forgetAggregateSigns (aggregateSigned N config)=aggregateExcess N config := by
  unfold forgetAggregateSigns aggregateSigned aggregateExcess
  rw [← Finsupp.mapDomain_comp]
  rfl

theorem aggregateSigned_apply (N : ℕ) (config : SpatialMarkedConfig N) (a : ℕ × F₂) :
    aggregateSigned N config a=∑ x : Fin N, config (x,a) := mapDomain_snd_apply config a

theorem forgetAggregateSigns_apply (config : SignedAggregateConfig) (e : ℕ) :
    forgetAggregateSigns config e=∑ s : F₂, config (e,s) := mapDomain_fst_apply config e

theorem aggregateExcess_coefficient (N : ℕ) (config : SpatialMarkedConfig N) (e : ℕ) :
    aggregateExcess N config e=∑ x : Fin N, ∑ s : F₂, config (x,(e,s)) := by
  rw [← forget_aggregateSigned,forgetAggregateSigns_apply]
  simp only [aggregateSigned_apply]
  exact Finset.sum_comm

/-- Intrinsic projection of the aggregate equals aggregation of the spatial projection. -/
theorem project_aggregateSigned (N E : ℕ) (config : SpatialMarkedConfig N) :
    projectSignedAggregate E (aggregateSigned N config)=
      finiteSignedAggregate N E (projectConfiguration N E config) := by
  funext a
  change aggregateSigned N config (a.1.val,a.2)=_
  rw [aggregateSigned_apply]
  simpa only [finiteSignedAggregate,projectConfiguration,finiteMarkedEmbedding,
    Function.Embedding.coeFn_mk,Equiv.symm_apply_apply] using
    (dyadicSiteEquiv N).sum_comp (fun x => projectConfiguration N E config (x,a))

def forgetFiniteSigns (E : ℕ) (k : (Fin (E+1) × F₂) → ℕ) (e : Fin (E+1)) : ℕ :=
  ∑ s : F₂, k (e,s)

def unsignedProjection (E : ℕ) (config : ℕ →₀ ℕ) (e : Fin (E+1)) : ℕ := config e.val

theorem unsignedProjection_aggregate (N E : ℕ) (config : SpatialMarkedConfig N) :
    unsignedProjection E (aggregateExcess N config)=
      forgetFiniteSigns E (finiteSignedAggregate N E (projectConfiguration N E config)) := by
  rw [← project_aggregateSigned]
  funext e
  change aggregateExcess N config e.val=∑ s : F₂, aggregateSigned N config (e.val,s)
  rw [← forget_aggregateSigned,forgetAggregateSigns_apply]

end
end PaperC.V282.AggregateCoordinateIdentities
