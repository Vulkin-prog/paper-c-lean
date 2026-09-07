import PaperCV282.MacroTransportRestoration

/-! # Restoring sites after a compatible countable statistic -/
namespace PaperC.V282.MacroTransportStatistics

open MeasureTheory ProbabilityTheory BulkMarkedTypes BulkMarkedSource BulkMarkedTarget
open MacroTransportRestriction MacroTransportRestoration InfiniteMassCoupling CountableLawTransfer
open SharpConditioning SharpConditioningDiscrete ConditionedCountableLaw FiniteFieldTotalVariation
open InfiniteRademacher InfiniteStartProbabilityTransfer FiniteStartMaskAverages
open scoped BigOperators NNReal ENNReal

noncomputable section
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- Two different underlying spaces give exactly the same discrete TV convention. -/
theorem two_map_distance_eq_mass {Ω Ω' α : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : Ω → α} {g : Ω' → α} (hf : Measurable f) (hg : Measurable g) :
    measureTotalVariation (μ.map f) (ν.map g)=
      massTotalVariation (observableLaw μ f) (observableLaw ν g) := by
  letI instProbabilityTarget : IsProbabilityMeasure (ν.map g) := Measure.isProbabilityMeasure_map hg.aemeasurable
  rw [map_distance_eq_mass _ _ hf]
  congr 1
  funext a
  exact (observableLaw_eq_map ν hg a).symm

/-- The middle comparison is the comparison of the statistic itself, with no labelled loss. -/
theorem conditional_statistic_restoration_le {s t : Finset ℕ} (h : s ⊆ t) (L : ℕ)
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (statS : SpatialMarkedConfig s → α) (statT : SpatialMarkedConfig t → α)
    (hcompat : ∀ c, statT (embedSites h c)=statS c)
    (A : Set InfiniteSample) (hA : MeasurableSet A) (hpos : 0 < infiniteRademacherMeasure.real A) :
    measureTotalVariation ((cond infiniteRademacherMeasure A).map (statT ∘ spatialMarkedSource t L))
      ((spatialTargetMeasure t L).map statT) ≤
      (∑ x∈t\s, infiniteStartProbability x L)/infiniteRademacherMeasure.real A +
        measureTotalVariation ((cond infiniteRademacherMeasure A).map (statS ∘ spatialMarkedSource s L))
          ((spatialTargetMeasure s L).map statS) + (maskRate L (t\s) : ℝ) := by
  letI instProbabilityConditional : IsProbabilityMeasure (cond infiniteRademacherMeasure A) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hpos)
  rw [two_map_distance_eq_mass _ _ ((measurable_of_countable statT).comp (measurable_spatialMarkedSource t L))
      (measurable_of_countable _),
    two_map_distance_eq_mass _ _ ((measurable_of_countable statS).comp (measurable_spatialMarkedSource s L))
      (measurable_of_countable _)]
  have hs0 : infiniteRademacherMeasure.real {omega | (statT ∘ spatialMarkedSource t L) omega≠
      (statS ∘ spatialMarkedSource s L) omega} ≤ ∑ x∈t\s, infiniteStartProbability x L := by
    apply (measureReal_mono (s₁ := {omega | (statT ∘ spatialMarkedSource t L) omega≠(statS ∘ spatialMarkedSource s L) omega})
      (s₂ := {omega | spatialMarkedSource t L omega≠embedSites h (spatialMarkedSource s L omega)})
      (fun omega hw he => hw (by dsimp; rw [he,hcompat])) (measure_ne_top _ _)).trans
    exact source_restoration_probability_le h L
  have hs := (conditional_event_le_div_probability infiniteRademacherMeasure A hA
    {omega | (statT ∘ spatialMarkedSource t L) omega≠(statS ∘ spatialMarkedSource s L) omega}).trans
    (div_le_div_of_nonneg_right hs0 hpos.le)
  have ht : (spatialTargetMeasure t L).real {c | statT c≠(statS ∘ restrictSites h) c} ≤
      (maskRate L (t\s) : ℝ) := by
    apply (measureReal_mono (s₁ := {c | statT c≠(statS ∘ restrictSites h) c})
      (s₂ := {c | c≠embedSites h (restrictSites h c)})
      (fun c hc he => hc ((congrArg statT he).trans (hcompat _)))).trans
    exact target_restoration_probability_le h L
  have htarget : HasLaw (statS ∘ restrictSites h)
      ((spatialTargetMeasure s L).map statS) (spatialTargetMeasure t L) :=
    (show HasLaw statS ((spatialTargetMeasure s L).map statS) (spatialTargetMeasure s L) from
      ⟨(measurable_of_countable _).aemeasurable,rfl⟩).fun_comp (hasLaw_restrictSites h L)
  have he : observableLaw (spatialTargetMeasure t L) (statS ∘ restrictSites h)=
      observableLaw (spatialTargetMeasure s L) statS := by
    rw [observableLaw_of_hasLaw _ _ htarget]
    funext a
    exact (observableLaw_eq_map _ (measurable_of_countable _) a).symm
  apply truncation_tv_le_of_bounds (cond infiniteRademacherMeasure A) (spatialTargetMeasure t L)
    ((measurable_of_countable statT).comp (measurable_spatialMarkedSource t L))
    (measurable_of_countable _)
    ((measurable_of_countable statS).comp (measurable_spatialMarkedSource s L))
    (measurable_of_countable _) id hs
  · rw [he]
  · exact ht

end
end PaperC.V282.MacroTransportStatistics
