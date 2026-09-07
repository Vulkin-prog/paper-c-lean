import PaperCV282.MacroAggregateComparison
import PaperCV282.BulkMarkedComparison

/-! # Actual countable signed aggregate source, target and both truncation tails -/
namespace PaperC.V282.MacroAggregateTruncation

open MeasureTheory ProbabilityTheory SignedAggregateConfiguration SignedDirectionalFactors
open MacroAggregateModel MacroAggregateComparison BulkMarkedTypes BulkMarkedSource BulkMarkedTarget
open BulkMarkedTargetProjection BulkMarkedInfinite BulkMarkedTransfer ExactMarkedModel
open InfiniteMassCoupling FiniteFieldTotalVariation FiniteFieldPoissonCoupling PoissonFieldMeasure
open InfiniteRademacher ConditionedCountableLaw CountableLawTransfer ConditionalStartProbability
open FiniteStartMaskAverages
open scoped BigOperators NNReal

noncomputable section

local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

def signedAggregateSource (sites : Finset ℕ) (L : ℕ) := aggregateSigned sites ∘ spatialMarkedSource sites L

def signedAggregateTargetLaw (sites : Finset ℕ) (L : ℕ) : SignedAggregateConfig → ℝ :=
  observableLaw (spatialTargetMeasure sites L) (aggregateSigned sites)

def conditionalSignedAggregateDistance (sites : Finset ℕ) (L : ℕ) (C : Set InfiniteSample) : ℝ :=
  massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure C (signedAggregateSource sites L))
    (signedAggregateTargetLaw sites L)

theorem measurable_signedAggregateSource (sites : Finset ℕ) (L : ℕ) : Measurable (signedAggregateSource sites L) :=
  (measurable_of_countable _).comp (measurable_spatialMarkedSource sites L)

theorem sum_site_rates_eq_signedAggregateRates (sites : Finset ℕ) (L E : ℕ) (a : Fin (E+1) × F₂) :
    (∑ x : {x : ℕ // x ∈ sites}, allSignedRates sites L E sites (x,a))=
      signedAggregateRates (maskRate L sites) E a := by
  have hrate (x : {x : ℕ // x ∈ sites}) :
      allSignedRates sites L E sites (x,a)=signedMarkRate L a.1.val := if_pos x.property
  simp_rw [hrate]
  apply NNReal.coe_injective
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,NNReal.coe_mul,NNReal.coe_natCast,
    signedAggregateRates,signedMarkRate_coe,maskRate,Nat.zero_add]
  change (sites.card : ℝ)*(1/(2 : ℝ)^(L+a.1.val+2))=
    ((sites.card : ℝ)/(2 : ℝ)^L)*(1/(2 : ℝ)^(a.1.val+2))
  rw [show L+a.1.val+2=L+(a.1.val+2) by omega,pow_add]
  ring

/-- Summing positions gives the literal product target, including zero site count. -/
theorem hasLaw_project_signedAggregate (sites : Finset ℕ) (L E : ℕ) :
    HasLaw (finiteSignedAggregate sites E ∘ projectConfiguration sites E)
      (fieldMeasure (signedAggregateRates (maskRate L sites) E)) (spatialTargetMeasure sites L) := by
  have h := (hasLaw_finiteSignedAggregate sites E (allSignedRates sites L E sites)).fun_comp
    (hasLaw_projectConfiguration sites L E)
  have hr : (fun a => ∑ x : {x : ℕ // x ∈ sites},
      allSignedRates sites L E sites (x,a))=signedAggregateRates (maskRate L sites) E :=
    funext (sum_site_rates_eq_signedAggregateRates sites L E)
  rw [hr] at h
  exact h

theorem observableLaw_project_signedAggregate (sites : Finset ℕ) (L E : ℕ) :
    observableLaw (spatialTargetMeasure sites L) (finiteSignedAggregate sites E ∘ projectConfiguration sites E)=
      poissonFieldMass (signedAggregateRates (maskRate L sites) E) := by
  rw [observableLaw_of_hasLaw _ _ (hasLaw_project_signedAggregate sites L E)]
  exact funext (fieldMeasure_real_singleton _)

/-- Aggregation can only decrease the event on which the source and its embedding disagree. -/
theorem source_aggregate_disagreement_le (sites : Finset ℕ) (L E : ℕ) :
    infiniteRademacherMeasure.real {omega | signedAggregateSource sites L omega≠
      embedSignedAggregate E (finiteSignedAggregate sites E
        (infiniteSignedField sites L E sites omega))}≤
      infiniteRademacherMeasure.real (spatialSourceTail sites L E) := by
  apply measureReal_mono ?_ (measure_ne_top _ _)
  intro omega h
  by_contra hn
  apply h
  have hh := spatialMarkedSource_eq_truncate_off_tail sites L E omega hn
  rw [← embed_project_configuration,project_spatialMarkedSource] at hh
  exact (congrArg (MacroAggregateModel.aggregateSigned sites) hh).trans
    (MacroAggregateModel.aggregate_embed_configuration sites E _)

theorem target_aggregate_disagreement_le (sites : Finset ℕ) (L E : ℕ) :
    (spatialTargetMeasure sites L).real {config | aggregateSigned sites config≠
      embedSignedAggregate E (finiteSignedAggregate sites E (projectConfiguration sites E config))}≤
        (maskRate L sites : ℝ)/(2 : ℝ)^(E+1) := by
  apply (measureReal_mono (μ := spatialTargetMeasure sites L) (s₂ :=
    {config | config≠embedConfiguration sites E (projectConfiguration sites E config)}) ?_).trans
      (BulkMarkedComparison.target_embedding_disagreement_le sites L E)
  intro config h hsame
  apply h
  have hh := congrArg (aggregateSigned sites) hsame
  exact hh.trans (MacroAggregateModel.aggregate_embed_configuration sites E _)

/-- A true countable conditional comparison, with no independence assumption on tail events. -/
theorem conditional_signedAggregate_tv_le_finite_and_tails (sites : Finset ℕ) (L E : ℕ)
    (C : Set InfiniteSample) (hC : MeasurableSet C) (hpos : 0 < infiniteRademacherMeasure.real C) :
    conditionalSignedAggregateDistance sites L C≤
      infiniteRademacherMeasure.real (spatialSourceTail sites L E)/infiniteRademacherMeasure.real C+
      conditionalFiniteAggregateDistance sites L E C+(maskRate L sites : ℝ)/(2 : ℝ)^(E+1) := by
  letI instProbabilityConditionalSource : IsProbabilityMeasure (cond infiniteRademacherMeasure C) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hpos)
  have hf : Measurable (finiteSignedAggregate sites E ∘ infiniteSignedField sites L E sites) :=
    (measurable_of_countable _).comp (MacroAggregateComparison.measurable_infiniteSignedField sites L E)
  have hs := (conditional_event_le_div_probability infiniteRademacherMeasure C hC
    {omega | signedAggregateSource sites L omega≠embedSignedAggregate E
      (finiteSignedAggregate sites E (infiniteSignedField sites L E sites omega))}).trans
    (div_le_div_of_nonneg_right (source_aggregate_disagreement_le sites L E) hpos.le)
  have hm : massTotalVariation
      (observableLaw (cond infiniteRademacherMeasure C)
        (finiteSignedAggregate sites E ∘ infiniteSignedField sites L E sites))
      (observableLaw (spatialTargetMeasure sites L) (finiteSignedAggregate sites E ∘ projectConfiguration sites E))=
        conditionalFiniteAggregateDistance sites L E C := by
    rw [observableLaw_project_signedAggregate]
    rfl
  exact truncation_tv_le_of_bounds (cond infiniteRademacherMeasure C) (spatialTargetMeasure sites L)
    (measurable_signedAggregateSource sites L) (measurable_of_countable _) hf (measurable_of_countable _)
    (embedSignedAggregate E) hs hm.le (target_aggregate_disagreement_le sites L E)

end
end PaperC.V282.MacroAggregateTruncation
