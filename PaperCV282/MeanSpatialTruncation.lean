import PaperCV282.FinitePrimeEnvironment
import PaperCV282.SpatialMarkedEventComparison
import PaperCV282.DirectionalMarkedCosts

/-!
# The true averaged conditional distance of the complete labelled field

The actual conditional source-tail probabilities are averaged before the
cutoff is removed. Consequently no number-of-environments factor occurs.
-/

namespace PaperC.V282.MeanSpatialTruncation

open MeasureTheory ProbabilityTheory FinitePrimeEnvironment SpatialMarkedEventComparison
open InfiniteRademacher InfiniteCylinderTransfer InfiniteConditionalWords ConditionedCountableLaw
open CountablePrimeEventTransfer CountableLawTransfer InfiniteMassCoupling FiniteFieldTotalVariation
open SpatialMarkedTypes SpatialMarkedSource SpatialMarkedTarget SpatialMarkedTargetProjection
open ExactMarkedInfinite ExactMarkedModel SpatialMarkedFieldComparison ConditionalStartProbability
open SectionThirteenFiniteBound ConditionalAGGAverage FiniteFieldPoissonCoupling
open MarkedDetruncation AllStartSoftPoisson
open ExactMarkedFieldTransfer ExactMarkedFieldBounds
open DirectionalMarkedCosts

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

def spatialTailEvent (N L E : ℕ) : Set InfiniteSample :=
  {omega | spatialMarkedSource N L omega ≠
    embedConfiguration N E (infiniteSignedField N L E (dyadicBlock N) omega)}

theorem measurableSet_spatialTailEvent (N L E : ℕ) :
    MeasurableSet (spatialTailEvent N L E) :=
  (measurableSet_eq_fun (measurable_spatialMarkedSource N L)
    ((measurable_of_countable (embedConfiguration N E)).comp
      (measurable_infiniteSignedField_full N L E))).compl

/-- Pointwise truncation pays the conditional tail, not the tail divided by the atom mass. -/
theorem conditional_spatial_le_actual_tail (N L E : ℕ) (A : Set InfiniteSample)
    (hpos : 0 < infiniteRademacherMeasure.real A) :
    spatialEventDistance N L A ≤
      (cond infiniteRademacherMeasure A).real (spatialTailEvent N L E) +
      massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure A
        (infiniteSignedField N L E (dyadicBlock N)))
        (poissonFieldMass (allSignedRates N L E (dyadicBlock N))) +
      (fullRate N L : ℝ) / (2 : ℝ) ^ (E + 1) := by
  letI instProbabilityConditionalSource : IsProbabilityMeasure (cond infiniteRademacherMeasure A) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hpos)
  have htarget : observableLaw (spatialTargetMeasure N L) (projectConfiguration N E) =
      poissonFieldMass (allSignedRates N L E (dyadicBlock N)) :=
    funext (spatial_project_mass_eq N L E)
  have h := truncation_tv_le_of_bounds (cond infiniteRademacherMeasure A) (spatialTargetMeasure N L)
    (measurable_spatialMarkedSource N L) measurable_id (measurable_infiniteSignedField_full N L E)
    (measurable_of_countable (projectConfiguration N E)) (embedConfiguration N E)
    (le_refl _) (le_refl _) (target_embedding_disagreement_le N L E)
  rw [htarget] at h
  exact h

/-- The full actual average has only the one unconditional source tail. -/
theorem mean_spatial_le_finite_and_tails (C N L E Y : ℕ) :
    meanAtomDistance C Y (spatialMarkedSource N L) (spatialTargetLaw N L) ≤
      infiniteMarkTailProbability N L E +
      ExactMarkedFieldBounds.exactSignedConditionalDistance C N L E Y (dyadicBlock N) +
      (fullRate N L : ℝ) / (2 : ℝ) ^ (E + 1) := by
  have hpos (sigma : SmallSample C Y) :
      0 < infiniteRademacherMeasure.real (infiniteSmallPrimeAtom C Y sigma) := by
    rw [PrimeFieldEventConditioning.real_atom_mass]
    positivity
  have ht := finiteUniformAverage_mono (fun sigma : SmallSample C Y =>
    conditional_spatial_le_actual_tail N L E (infiniteSmallPrimeAtom C Y sigma) (hpos sigma))
  rw [finiteUniformAverage_add, finiteUniformAverage_add] at ht
  have htail : finiteUniformAverage (fun sigma : SmallSample C Y =>
      (cond infiniteRademacherMeasure (infiniteSmallPrimeAtom C Y sigma)).real
        (spatialTailEvent N L E)) ≤ infiniteMarkTailProbability N L E := by
    change uniformAverage _ ≤ _
    rw [average_conditional_event C Y _ (measurableSet_spatialTailEvent N L E)]
    exact source_embedding_disagreement_le N L E
  have hfinite := finite_meanAtomDistance_eq C N L E Y
  have hconst : finiteUniformAverage (fun _sigma : SmallSample C Y =>
      (fullRate N L : ℝ) / (2 : ℝ) ^ (E + 1)) =
      (fullRate N L : ℝ) / (2 : ℝ) ^ (E + 1) := by simp [finiteUniformAverage]
  rw [hconst] at ht
  change meanAtomDistance C Y (spatialMarkedSource N L) (spatialTargetLaw N L) ≤
    finiteUniformAverage _ + meanAtomDistance C Y _ _ + _ at ht
  rw [hfinite] at ht
  linarith

end
end PaperC.V282.MeanSpatialTruncation
