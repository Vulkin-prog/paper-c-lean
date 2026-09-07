import PaperCV282.MacroAggregateTheorem
import PaperCV282.UnsignedAggregateComparison

/-! # The complete unsigned geometric target and contraction from the signed aggregate -/
namespace PaperC.V282.MacroAggregateUnsigned

open MeasureTheory ProbabilityTheory MacroAggregateModel MacroAggregateTruncation BulkMarkedTypes
open BulkMarkedSource BulkMarkedTarget BulkMarkedInfinite BulkMarkedTransfer MacroAggregateRestoration
open SignedAggregateConfiguration SignedDirectionalFactors AggregateCoordinateIdentities
open UnsignedAggregateTarget GeometricMarkedConfiguration GeometricClusterTruncation
open FiniteStartMaskAverages PoissonFieldMeasure InfiniteMassCoupling ConditionedCountableLaw
open CountableLawTransfer InfiniteRademacher FiniteFieldTotalVariation
open scoped BigOperators NNReal

noncomputable section

local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

def aggregateExcess (sites : Finset ℕ) (config : SpatialMarkedConfig sites) : ℕ→₀ℕ :=
  config.mapDomain (fun j => j.2.1)

theorem aggregateSigned_apply (sites : Finset ℕ) (config : SpatialMarkedConfig sites) (a : ℕ×F₂) :
    MacroAggregateModel.aggregateSigned sites config a=∑ x : sites,config (x,a) :=
  mapDomain_snd_apply config a

theorem forget_aggregateSigned (sites : Finset ℕ) (config : SpatialMarkedConfig sites) :
    forgetAggregateSigns (MacroAggregateModel.aggregateSigned sites config)=aggregateExcess sites config := by
  unfold forgetAggregateSigns MacroAggregateModel.aggregateSigned aggregateExcess
  rw [← Finsupp.mapDomain_comp]
  rfl

theorem project_aggregateSigned (sites : Finset ℕ) (E : ℕ) (config : SpatialMarkedConfig sites) :
    projectSignedAggregate E (MacroAggregateModel.aggregateSigned sites config)=
      MacroAggregateModel.finiteSignedAggregate sites E (projectConfiguration sites E config) := by
  funext a
  change MacroAggregateModel.aggregateSigned sites config (a.1.val,a.2)=_
  rw [aggregateSigned_apply]
  rfl

theorem unsignedProjection_aggregate (sites : Finset ℕ) (E : ℕ) (config : SpatialMarkedConfig sites) :
    unsignedProjection E (aggregateExcess sites config)=
      forgetFiniteSigns E (MacroAggregateModel.finiteSignedAggregate sites E (projectConfiguration sites E config)) := by
  rw [← project_aggregateSigned]
  funext e
  change aggregateExcess sites config e.val=∑ s : F₂,MacroAggregateModel.aggregateSigned sites config (e.val,s)
  rw [← forget_aggregateSigned,forgetAggregateSigns_apply]

theorem hasLaw_unsigned_projection (sites : Finset ℕ) (L E : ℕ) :
    HasLaw (unsignedProjection E ∘ aggregateExcess sites)
      (fieldMeasure (geometricCoordinateRates (maskRate L sites) E)) (spatialTargetMeasure sites L) := by
  have h := (hasLaw_forgetFiniteSigns (maskRate L sites) E).fun_comp
    (MacroAggregateTruncation.hasLaw_project_signedAggregate sites L E)
  have he : unsignedProjection E ∘ aggregateExcess sites=
      fun config => forgetFiniteSigns E (MacroAggregateModel.finiteSignedAggregate sites E
        (projectConfiguration sites E config)) := funext (unsignedProjection_aggregate sites E)
  rw [he]
  exact h

/-- Equality of every finite projection proves the full, independently marked geometric Poisson law. -/
theorem hasLaw_aggregateExcess (sites : Finset ℕ) (L : ℕ) :
    HasLaw (aggregateExcess sites) (configurationMeasure (maskRate L sites)) (spatialTargetMeasure sites L) := by
  refine ⟨(measurable_of_countable _).aemeasurable,?_⟩
  apply configurationMeasure_ext
  intro E
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    (hasLaw_unsigned_projection sites L E).map_eq]
  exact (hasLaw_finite_configuration (maskRate L sites) E).map_eq.symm

def unsignedAggregateSource (sites : Finset ℕ) (L : ℕ) := aggregateExcess sites ∘ spatialMarkedSource sites L

def conditionalUnsignedAggregateDistance (sites : Finset ℕ) (L : ℕ) (A : Set InfiniteSample) : ℝ :=
  massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure A (unsignedAggregateSource sites L))
    (UnsignedAggregateComparison.geometricConfigurationLaw (maskRate L sites))

theorem measurable_unsignedAggregateSource (sites : Finset ℕ) (L : ℕ) : Measurable (unsignedAggregateSource sites L) :=
  (measurable_of_countable _).comp (measurable_spatialMarkedSource sites L)

theorem actual_unsigned_target_law (sites : Finset ℕ) (L : ℕ) :
    observableLaw (spatialTargetMeasure sites L) (aggregateExcess sites)=
      UnsignedAggregateComparison.geometricConfigurationLaw (maskRate L sites) :=
  observableLaw_of_hasLaw _ _ (hasLaw_aggregateExcess sites L)

theorem conditional_unsigned_le_signed (sites : Finset ℕ) (L : ℕ) (A : Set InfiniteSample)
    (hpos : 0 < infiniteRademacherMeasure.real A) :
    conditionalUnsignedAggregateDistance sites L A≤conditionalSignedAggregateDistance sites L A := by
  have h := conditional_statistic_tv_le infiniteRademacherMeasure A hpos (spatialTargetMeasure sites L)
    (measurable_signedAggregateSource sites L) (measurable_of_countable (MacroAggregateModel.aggregateSigned sites)) forgetAggregateSigns
  have hs : forgetAggregateSigns ∘ signedAggregateSource sites L=unsignedAggregateSource sites L :=
    funext (fun omega => forget_aggregateSigned sites _)
  have ht : forgetAggregateSigns ∘ MacroAggregateModel.aggregateSigned sites=aggregateExcess sites :=
    funext (forget_aggregateSigned sites)
  rw [hs,ht,actual_unsigned_target_law] at h
  exact h

end
end PaperC.V282.MacroAggregateUnsigned
