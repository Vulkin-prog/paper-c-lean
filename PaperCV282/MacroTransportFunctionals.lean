import PaperCV282.MacroTransportCoordinates

/-! # All deterministic functionals of the complete base-contained field

A functional can encode spatial masks, marked order statistics, or forgetting
signs. Both its source law and its target law are the actual images.
-/
namespace PaperC.V282.MacroTransportFunctionals

open MeasureTheory ProbabilityTheory MacroTransportModel MacroTransportRestoration
open BulkMarkedTypes InfiniteRademacher InfiniteMassCoupling CountableLawTransfer
open ConditionedCountableLaw MassPushforward FiniteFieldTotalVariation

noncomputable section
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- The exact image of the true event-conditioned source, not a separately postulated law. -/
theorem conditional_functional_law_eq {β : Type*} (M L : ℕ) (A : Set InfiniteSample)
    (stat : SpatialMarkedConfig (containedStarts M L) → β) :
    conditionalObservableLaw infiniteRademacherMeasure A (stat ∘ source M L)=
      pushforwardMass stat (conditionalObservableLaw infiniteRademacherMeasure A (source M L)) := by
  exact (pushforwardMass_observableLaw (cond infiniteRademacherMeasure A) (measurable_source M L) stat).symm

theorem target_functional_law_eq {β : Type*} (M L : ℕ)
    (stat : SpatialMarkedConfig (containedStarts M L) → β) :
    observableLaw (targetMeasure M L) stat=pushforwardMass stat (observableLaw (targetMeasure M L) id) := by
  exact (pushforwardMass_observableLaw (targetMeasure M L) measurable_id stat).symm

theorem hasSum_conditional_functional_law {β : Type*} (M L : ℕ) (A : Set InfiniteSample)
    (hpos : 0 < infiniteRademacherMeasure.real A)
    (stat : SpatialMarkedConfig (containedStarts M L) → β) :
    HasSum (conditionalObservableLaw infiniteRademacherMeasure A (stat ∘ source M L)) 1 := by
  rw [conditional_functional_law_eq]
  exact hasSum_pushforwardMass stat
    (hasSum_conditionalObservableLaw infiniteRademacherMeasure A hpos (measurable_source M L))

theorem hasSum_target_functional_law {β : Type*} (M L : ℕ)
    (stat : SpatialMarkedConfig (containedStarts M L) → β) :
    HasSum (observableLaw (targetMeasure M L) stat) 1 := by
  rw [target_functional_law_eq]
  exact hasSum_pushforwardMass stat (hasSum_observableLaw _ measurable_id)

/-- Every functional of the labelled field transfers with no extra error. -/
theorem conditional_functional_distance_le {β : Type*} (M L : ℕ) (A : Set InfiniteSample)
    (hpos : 0 < infiniteRademacherMeasure.real A)
    (stat : SpatialMarkedConfig (containedStarts M L) → β) :
    massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure A (stat ∘ source M L))
      (observableLaw (targetMeasure M L) stat)≤conditionalDistance M L A := by
  letI instProbabilityConditional : IsProbabilityMeasure (cond infiniteRademacherMeasure A) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hpos)
  rw [conditional_functional_law_eq,target_functional_law_eq]
  apply (massTotalVariation_pushforward_le stat
    (hasSum_conditionalObservableLaw infiniteRademacherMeasure A hpos (measurable_source M L))
    (hasSum_observableLaw _ measurable_id)
    (conditionalObservableLaw_nonneg _ _ _) (observableLaw_nonneg _ id)).trans_eq
  exact (map_distance_eq_mass _ _ (measurable_source M L)).symm

end
end PaperC.V282.MacroTransportFunctionals
