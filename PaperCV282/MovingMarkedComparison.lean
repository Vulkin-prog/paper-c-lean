import PaperCV282.MovingMarkedSource
import PaperCV282.SpatialMarkedHardBudget
import PaperCV282.SpatialMarkedMovableBudget

/-!
# The actual moving-coordinate field and all threshold paths

The complete signed spatial comparison is preserved exactly when excesses are
renamed as integer levels. Arithmetic conditioning uses the actual normalized
restriction. These are labelled-field consequences, not the stronger
aggregate one-factor assertion of Theorem 5.8(ii).
-/
namespace PaperC.V282.MovingMarkedComparison

open MeasureTheory ProbabilityTheory Filter Topology InfiniteRademacher InfiniteCylinderTransfer
open MovingMarkedLevels MovingMarkedSource GrowingLevelParameters ThresholdPathEquivalence
open SpatialMarkedTypes SpatialMarkedSource SpatialMarkedTarget SpatialMarkedEventComparison SpatialMarkedFieldComparison
open CountableLawTransfer ConditionedCountableLaw InfiniteMassCoupling FiniteFieldTotalVariation
open MassPushforward PrimeEulerPNT ProcessAGGInput AllStartSoftPoisson RareConditioningRates
open LabelledInformationBudget MovableMarkedBudget SaddleParameters SaddleScales
open HardPoissonRates SoftRateAssembly SpatialMarkedHardBudget SpatialMarkedMovableBudget
open InfiniteStartProbabilityTransfer

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

local instance instMeasurableExcessConfiguration : MeasurableSpace (ℕ →₀ ℕ) := ⊤

local instance instMeasurableSingletonExcessConfiguration : MeasurableSingletonClass (ℕ →₀ ℕ) := by infer_instance

local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- No coordinate or sign is forgotten in this actual conditional-law identity. -/
theorem conditional_moving_source_tv_eq (N d : ℕ) (A : Set InfiniteSample)
    (q : SpatialMarkedConfig N → ℝ) :
    massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure A (movingSource N d))
      (pushforwardMass (configurationEquiv (Fin N) F₂ d) q) =
      massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure A
        (spatialMarkedSource N (movingLength N d))) q := by
  unfold movingSource conditionalObservableLaw
  have he := pushforwardMass_observableLaw (cond infiniteRademacherMeasure A)
    (measurable_spatialMarkedSource N (movingLength N d)) (configurationEquiv (Fin N) F₂ d)
  simp only [Function.comp_def] at he
  rw [← he]
  exact massTotalVariation_equiv _ _ q

def movingEventDistance (N d : ℕ) (A : Set InfiniteSample) : ℝ :=
  massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure A (movingSource N d))
    (pushforwardMass (configurationEquiv (Fin N) F₂ d) (spatialTargetLaw N (movingLength N d)))

theorem movingEventDistance_eq (N d : ℕ) (A : Set InfiniteSample) :
    movingEventDistance N d A = spatialEventDistance N (movingLength N d) A :=
  conditional_moving_source_tv_eq N d A _

/-- The hard labelled conclusion in the literal integer coordinates of (5.17). -/
theorem moving_labelled_hard_tendsto_zero (hAGG : ProcessAGGStatement)
    (hPNT : PrimeNumberTheoremRemainder) (c : ℝ) (hc : 0<c)
    (d : ℕ → ℕ) (hd : Tendsto (fun N : ℕ => (d N : ℝ)/Real.log N) atTop (𝓝 0))
    (A : ℕ → Set InfiniteSample)
    (hA : ∀ᶠ N in atTop,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff N)) inferInstance] (A N))
    (hpos : ∀ᶠ N in atTop, 0 < infiniteRademacherMeasure.real (A N))
    (hbudget : ∀ᶠ N in atTop,
      labelledLogCost (eventInformation (A N)) (fullRate N (movingLength N (d N)))≤
        saddleCutoff 1 (Real.log N)-c*saddleNu 1 (Real.log N)) :
    Tendsto (fun N => movingEventDistance N (d N) (A N)) atTop (𝓝 0) := by
  apply (theorem_five_eight_labelled_hard hAGG hPNT c hc d hd A hA hpos hbudget).congr'
  exact Filter.Eventually.of_forall (fun N => (movingEventDistance_eq N (d N) (A N)).symm)

/-- The movable labelled conclusion, still preserving all positions and both signs. -/
theorem moving_labelled_movable_tendsto_zero (hAGG : ProcessAGGStatement)
    (hPNT : PrimeNumberTheoremRemainder) (c : ℝ) (hc : 0<c)
    (d : ℕ → ℕ) (hd : Tendsto (fun N : ℕ => (d N : ℝ)/Real.log N) atTop (𝓝 0))
    (A : ℕ → Set InfiniteSample)
    (hA : ∀ᶠ N in atTop,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (softCutoff N)) inferInstance] (A N))
    (hpos : ∀ᶠ N in atTop, 0 < infiniteRademacherMeasure.real (A N))
    (hbudget : ∀ᶠ N in atTop,
      movableLogCost (eventInformation (A N)) (fullRate N (movingLength N (d N)))≤
        saddleCutoff 2 (Real.log N)/2-c*saddleNu 2 (Real.log N)) :
    Tendsto (fun N => movingEventDistance N (d N) (A N)) atTop (𝓝 0) := by
  apply (theorem_five_eight_labelled_movable hAGG hPNT c hc d hd A hA hpos hbudget).congr'
  exact Filter.Eventually.of_forall (fun N => (movingEventDistance_eq N (d N) (A N)).symm)

/-- The full literal threshold path preserves the exact-level distance also after conditioning. -/
theorem conditional_start_path_totalVariation_eq {N L : ℕ} (hN : 2≤N)
    (A : Set InfiniteSample) (q : (ℕ →₀ ℕ) → ℝ) :
    massTotalVariation
      (conditionalObservableLaw infiniteRademacherMeasure A
        (fun omega m => infiniteDyadicStartCount N (L+m) omega))
      (pushforwardMass thresholdFunction q) =
      massTotalVariation
        (conditionalObservableLaw infiniteRademacherMeasure A
          (fun omega => aggregateExcess N (spatialMarkedSource N L omega))) q := by
  unfold conditionalObservableLaw
  rw [actual_start_path_law_eq hN cond_absolutelyContinuous]
  have hm : Measurable (fun omega => aggregateExcess N (spatialMarkedSource N L omega)) :=
    (measurable_of_countable (aggregateExcess N)).comp (measurable_spatialMarkedSource N L)
  have he := pushforwardMass_observableLaw (cond infiniteRademacherMeasure A) hm thresholdFunction
  simp only [Function.comp_def] at he
  rw [← he]
  exact massTotalVariation_injective _ thresholdFunction_injective _ q

end
end PaperC.V282.MovingMarkedComparison
