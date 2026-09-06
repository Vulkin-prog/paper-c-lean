import PaperCV282.UnsignedAggregateTarget
import PaperCV282.MovingMarkedComparison

/-! # The actual unsigned counts and the whole threshold path follow from the signed aggregate comparison -/
namespace PaperC.V282.UnsignedAggregateComparison

open MeasureTheory ProbabilityTheory InfiniteRademacher InfiniteCylinderTransfer InfiniteMassCoupling
open SignedAggregateConfiguration SignedAggregateTruncation AggregateCoordinateIdentities
open UnsignedAggregateTarget SpatialMarkedTypes SpatialMarkedSource SpatialMarkedTarget
open GeometricMarkedConfiguration AllStartSoftPoisson ConditionedCountableLaw CountableLawTransfer
open MovingMarkedSource MovingMarkedComparison FiniteFieldTotalVariation PoissonFieldMeasure
open MassPushforward ThresholdPathEquivalence InfiniteStartProbabilityTransfer

open scoped NNReal

noncomputable section

local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

def unsignedAggregateSource (N L : ℕ) := aggregateExcess N ∘ spatialMarkedSource N L

def geometricConfigurationLaw (rate : ℝ≥0) : (ℕ →₀ ℕ) → ℝ :=
  observableLaw (configurationMeasure rate) id

def conditionalUnsignedAggregateDistance (N L : ℕ) (C : Set InfiniteSample) : ℝ :=
  massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure C (unsignedAggregateSource N L))
    (geometricConfigurationLaw (fullRate N L))

theorem measurable_unsignedAggregateSource (N L : ℕ) : Measurable (unsignedAggregateSource N L) :=
  (measurable_of_countable _).comp (measurable_spatialMarkedSource N L)

theorem actual_unsigned_target_law (N L : ℕ) :
    observableLaw (spatialTargetMeasure N L) (aggregateExcess N)=geometricConfigurationLaw (fullRate N L) :=
  observableLaw_of_hasLaw _ _ (hasLaw_aggregateExcess N L)

/-- Summing the two signs contracts the true event-conditioned distance. -/
theorem conditional_unsigned_le_signed (N L : ℕ) (C : Set InfiniteSample)
    (hpos : 0 < infiniteRademacherMeasure.real C) :
    conditionalUnsignedAggregateDistance N L C≤conditionalSignedAggregateDistance N L C := by
  have h := conditional_statistic_tv_le infiniteRademacherMeasure C hpos (spatialTargetMeasure N L)
    (measurable_signedAggregateSource N L) (measurable_of_countable (aggregateSigned N)) forgetAggregateSigns
  have hs : forgetAggregateSigns ∘ signedAggregateSource N L=unsignedAggregateSource N L := by
    funext omega
    exact forget_aggregateSigned N _
  have ht : forgetAggregateSigns ∘ aggregateSigned N=aggregateExcess N :=
    funext (forget_aggregateSigned N)
  rw [hs,ht,actual_unsigned_target_law] at h
  exact h

/-- The literal infinite path of start counts has exactly the same total variation distance. -/
theorem conditional_path_distance_eq {N L : ℕ} (hN : 2≤N) (C : Set InfiniteSample) :
    massTotalVariation
      (conditionalObservableLaw infiniteRademacherMeasure C
        (fun omega m => infiniteDyadicStartCount N (L+m) omega))
      (pushforwardMass thresholdFunction (geometricConfigurationLaw (fullRate N L)))=
        conditionalUnsignedAggregateDistance N L C :=
  conditional_start_path_totalVariation_eq hN C _

end
end PaperC.V282.UnsignedAggregateComparison
