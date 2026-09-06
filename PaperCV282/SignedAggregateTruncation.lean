import PaperCV282.SignedAggregateConfiguration
import PaperCV282.SignedDirectionalFactors
import PaperCV282.SpatialMarkedFieldComparison
import PaperCV282.ConditionedCountableLaw

/-!
# Removing both tails from the actual signed aggregate laws

The finite middle term is the actual event-conditioned count law. Its target
is the full product Poisson law at λ q_(e,s), obtained by summing site rates.
The tails are those of the genuine infinite source and target configurations.
-/
namespace PaperC.V282.SignedAggregateTruncation

open MeasureTheory ProbabilityTheory SignedAggregateConfiguration SignedDirectionalFactors
open SpatialMarkedTypes SpatialMarkedSource SpatialMarkedTarget SpatialMarkedTargetProjection
open SpatialMarkedFieldComparison ExactMarkedModel ExactMarkedInfinite ExactMarkedFieldTransfer
open InfiniteMassCoupling FiniteFieldTotalVariation FiniteFieldPoissonCoupling PoissonFieldMeasure
open InfiniteRademacher ConditionedCountableLaw CountableLawTransfer ConditionalStartProbability
open AllStartSoftPoisson InfiniteCylinderTransfer InfiniteExactLengthProbabilityTransfer
open ExactMarkedSourceTail MarkedDetruncation

open scoped BigOperators NNReal

noncomputable section

local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

def signedAggregateSource (N L : ℕ) := aggregateSigned N ∘ spatialMarkedSource N L

def signedAggregateTargetLaw (N L : ℕ) : SignedAggregateConfig → ℝ :=
  observableLaw (spatialTargetMeasure N L) (aggregateSigned N)

def conditionalSignedAggregateDistance (N L : ℕ) (C : Set InfiniteSample) : ℝ :=
  massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure C (signedAggregateSource N L))
    (signedAggregateTargetLaw N L)

def conditionalFiniteSignedAggregateDistance (N L E : ℕ) (C : Set InfiniteSample) : ℝ :=
  massTotalVariation
    (conditionalObservableLaw infiniteRademacherMeasure C
      (finiteSignedAggregate N E ∘ infiniteSignedField N L E (dyadicBlock N)))
    (poissonFieldMass (signedAggregateRates (fullRate N L) E))

theorem measurable_signedAggregateSource (N L : ℕ) : Measurable (signedAggregateSource N L) :=
  (measurable_of_countable _).comp (measurable_spatialMarkedSource N L)

theorem sum_site_rates_eq_signedAggregateRates (N L E : ℕ) (a : Fin (E+1) × F₂) :
    (∑ x : {x : ℕ // x ∈ dyadicBlock N}, allSignedRates N L E (dyadicBlock N) (x,a))=
      signedAggregateRates (fullRate N L) E a := by
  have hc : Fintype.card {x : ℕ // x ∈ dyadicBlock N}=N := by
    exact (Fintype.card_congr (dyadicSiteEquiv N)).symm.trans (Fintype.card_fin N)
  have hrate (x : {x : ℕ // x ∈ dyadicBlock N}) :
      allSignedRates N L E (dyadicBlock N) (x,a)=signedMarkRate L a.1.val := if_pos x.property
  simp_rw [hrate]
  apply NNReal.coe_injective
  simp only [Finset.sum_const,Finset.card_univ,hc,nsmul_eq_mul,NNReal.coe_mul,NNReal.coe_natCast,
    signedAggregateRates,signedMarkRate_coe,fullRate_coe]
  rw [show L+a.1.val+2=L+(a.1.val+2) by omega,pow_add]
  ring

/-- Summing positions gives the literal product target, including zero site count. -/
theorem hasLaw_project_signedAggregate (N L E : ℕ) :
    HasLaw (finiteSignedAggregate N E ∘ projectConfiguration N E)
      (fieldMeasure (signedAggregateRates (fullRate N L) E)) (spatialTargetMeasure N L) := by
  have h := (hasLaw_finiteSignedAggregate N E (allSignedRates N L E (dyadicBlock N))).fun_comp
    (hasLaw_projectConfiguration N L E)
  have hr : (fun a => ∑ x : {x : ℕ // x ∈ dyadicBlock N},
      allSignedRates N L E (dyadicBlock N) (x,a))=signedAggregateRates (fullRate N L) E :=
    funext (sum_site_rates_eq_signedAggregateRates N L E)
  rw [hr] at h
  exact h

theorem observableLaw_project_signedAggregate (N L E : ℕ) :
    observableLaw (spatialTargetMeasure N L) (finiteSignedAggregate N E ∘ projectConfiguration N E)=
      poissonFieldMass (signedAggregateRates (fullRate N L) E) := by
  rw [observableLaw_of_hasLaw _ _ (hasLaw_project_signedAggregate N L E)]
  exact funext (fieldMeasure_real_singleton _)

/-- Aggregation can only decrease the event on which the source and its embedding disagree. -/
theorem source_aggregate_disagreement_le (N L E : ℕ) :
    infiniteRademacherMeasure.real {omega | signedAggregateSource N L omega≠
      embedSignedAggregate E (finiteSignedAggregate N E
        (infiniteSignedField N L E (dyadicBlock N) omega))}≤
      infiniteMarkTailProbability N L E := by
  apply (measureReal_mono (μ := infiniteRademacherMeasure) (s₂ :=
    {omega | spatialMarkedSource N L omega≠embedConfiguration N E
      (infiniteSignedField N L E (dyadicBlock N) omega)}) ?_).trans
      (source_embedding_disagreement_le N L E)
  intro omega h hsame
  apply h
  change aggregateSigned N (spatialMarkedSource N L omega)=_
  rw [hsame,aggregate_embed_configuration]

theorem target_aggregate_disagreement_le (N L E : ℕ) :
    (spatialTargetMeasure N L).real {config | aggregateSigned N config≠
      embedSignedAggregate E (finiteSignedAggregate N E (projectConfiguration N E config))}≤
        (fullRate N L : ℝ)/(2 : ℝ)^(E+1) := by
  apply (measureReal_mono (μ := spatialTargetMeasure N L) (s₂ :=
    {config | config≠embedConfiguration N E (projectConfiguration N E config)}) ?_).trans
      (target_embedding_disagreement_le N L E)
  intro config h hsame
  apply h
  have hh := congrArg (aggregateSigned N) hsame
  exact hh.trans (aggregate_embed_configuration N E _)

/-- A true countable conditional comparison, with no independence assumption on tail events. -/
theorem conditional_signedAggregate_tv_le_finite_and_tails (N L E : ℕ)
    (C : Set InfiniteSample) (hC : MeasurableSet C) (hpos : 0 < infiniteRademacherMeasure.real C) :
    conditionalSignedAggregateDistance N L C≤
      infiniteMarkTailProbability N L E/infiniteRademacherMeasure.real C+
      conditionalFiniteSignedAggregateDistance N L E C+(fullRate N L : ℝ)/(2 : ℝ)^(E+1) := by
  letI : IsProbabilityMeasure (cond infiniteRademacherMeasure C) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hpos)
  have hf : Measurable (finiteSignedAggregate N E ∘ infiniteSignedField N L E (dyadicBlock N)) :=
    (measurable_of_countable _).comp (measurable_infiniteSignedField_full N L E)
  have hs := (conditional_event_le_div_probability infiniteRademacherMeasure C hC
    {omega | signedAggregateSource N L omega≠embedSignedAggregate E
      (finiteSignedAggregate N E (infiniteSignedField N L E (dyadicBlock N) omega))}).trans
    (div_le_div_of_nonneg_right (source_aggregate_disagreement_le N L E) hpos.le)
  have hm : massTotalVariation
      (observableLaw (cond infiniteRademacherMeasure C)
        (finiteSignedAggregate N E ∘ infiniteSignedField N L E (dyadicBlock N)))
      (observableLaw (spatialTargetMeasure N L) (finiteSignedAggregate N E ∘ projectConfiguration N E))=
        conditionalFiniteSignedAggregateDistance N L E C := by
    rw [observableLaw_project_signedAggregate]
    rfl
  exact truncation_tv_le_of_bounds (cond infiniteRademacherMeasure C) (spatialTargetMeasure N L)
    (measurable_signedAggregateSource N L) (measurable_of_countable _) hf (measurable_of_countable _)
    (embedSignedAggregate E) hs hm.le (target_aggregate_disagreement_le N L E)

end
end PaperC.V282.SignedAggregateTruncation
