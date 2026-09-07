import PaperCV282.MacroAggregatePaths
import PaperCV282.AggregateMovingCoordinates

/-! # Literal centered exact counts and whole paths on the contained population -/
namespace PaperC.V282.MacroAggregateCoordinates

open MeasureTheory Filter Topology InfiniteRademacher InfiniteCylinderTransfer
open MovingMarkedLevels GrowingLevelParameters SignedAggregateConfiguration
open MacroAggregateTruncation MacroAggregateUnsigned MacroAggregatePaths MacroAggregateRestoration
open MacroAggregateTheorem MacroTransportModel AggregateMovingCoordinates
open ConditionedCountableLaw InfiniteMassCoupling FiniteFieldTotalVariation MassPushforward
open UnsignedAggregateComparison (geometricConfigurationLaw)
open AllStartSoftPoisson RareConditioningRates AggregateInformationBudget HardPoissonRates
open SaddleParameters SaddleScales DirectionalSteinInput PrimeEulerPNT
open LaishramUniformInput PostQuadraticLiterature ThresholdPathEquivalence
open scoped BigOperators

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

def signedMovingAggregateSource (N d : ℕ) :=
  signedLevelConfigEquiv d ∘ signedAggregateSource (containedStarts N (movingLength N d)) (movingLength N d)

def unsignedMovingAggregateSource (N d : ℕ) :=
  unsignedLevelConfigEquiv d ∘ unsignedAggregateSource (containedStarts N (movingLength N d)) (movingLength N d)

theorem signedMovingAggregateSource_apply (N d e : ℕ) (s : F₂) (omega : InfiniteSample) :
    signedMovingAggregateSource N d omega (levelEquiv d e,s)=
      signedAggregateSource (containedStarts N (movingLength N d)) (movingLength N d) omega (e,s) :=
  signedLevelConfigEquiv_apply d _ e s

theorem unsignedMovingAggregateSource_apply (N d e : ℕ) (omega : InfiniteSample) :
    unsignedMovingAggregateSource N d omega (levelEquiv d e)=
      unsignedAggregateSource (containedStarts N (movingLength N d)) (movingLength N d) omega e :=
  unsignedLevelConfigEquiv_apply d _ e

def signedMovingAggregateDistance (N d : ℕ) (A : Set InfiniteSample) : ℝ :=
  massTotalVariation
    (conditionalObservableLaw infiniteRademacherMeasure A (signedMovingAggregateSource N d))
    (pushforwardMass (signedLevelConfigEquiv d) (signedAggregateTargetLaw (containedStarts N (movingLength N d)) (movingLength N d)))

def unsignedMovingAggregateDistance (N d : ℕ) (A : Set InfiniteSample) : ℝ :=
  massTotalVariation
    (conditionalObservableLaw infiniteRademacherMeasure A (unsignedMovingAggregateSource N d))
    (pushforwardMass (unsignedLevelConfigEquiv d) (geometricConfigurationLaw (containedRate N (movingLength N d))))

/-- Positivity is unnecessary for this identity; positive events are required by the comparison. -/
theorem signedMovingAggregateDistance_eq (N d : ℕ) (A : Set InfiniteSample) :
    signedMovingAggregateDistance N d A=
      containedAggregateDistance N (movingLength N d) A := by
  unfold signedMovingAggregateDistance signedMovingAggregateSource
  rw [conditionalObservableLaw_equiv_eq]
  exact massTotalVariation_equiv _ _ _

theorem unsignedMovingAggregateDistance_eq (N d : ℕ) (A : Set InfiniteSample) :
    unsignedMovingAggregateDistance N d A=
      conditionalUnsignedAggregateDistance (containedStarts N (movingLength N d)) (movingLength N d) A := by
  unfold unsignedMovingAggregateDistance unsignedMovingAggregateSource
  rw [conditionalObservableLaw_equiv_eq]
  exact massTotalVariation_equiv _ _ _

/-- The aggregate coordinate is the actual sum of signed exact indicators, with no upper censoring. -/
theorem signedMovingAggregateSource_coordinate (N d e : ℕ) (s : F₂) (omega : InfiniteSample) :
    signedMovingAggregateSource N d omega (levelEquiv d e,s)=
      ∑ x : containedStarts N (movingLength N d),
        ExactMarkedModel.signedMarkValue (infiniteValueBit omega) x.val (movingLength N d) e s := by
  rw [signedMovingAggregateSource_apply]
  exact MacroAggregateUnsigned.aggregateSigned_apply _ _ _

/-- The actual total number of sites multiplies the literal centered single-site mean. -/
theorem signed_target_level_mean {N d : ℕ} (hd : d≤criticalBase N) (r : MovingLevel d) :
    (containedRate N (movingLength N d) : ℝ)/(2 : ℝ)^((levelEquiv d).symm r+2)=
      ((N-movingLength N d : ℕ) : ℝ)*(2 : ℝ)^(-(criticalBase N : ℝ)-(r.val : ℝ)-2) := by
  rw [containedRate_coe]
  have h := signed_site_mean hd ((levelEquiv d).symm r)
  simp only [Equiv.apply_symm_apply] at h
  calc
    _ = ((N-movingLength N d : ℕ) : ℝ)*(1/(2 : ℝ)^(movingLength N d+(levelEquiv d).symm r+2)) := by
      rw [show movingLength N d+(levelEquiv d).symm r+2=movingLength N d+((levelEquiv d).symm r+2) by omega,pow_add]
      ring
    _ = _ := by rw [h]

theorem unsigned_target_level_mean {N d : ℕ} (hd : d≤criticalBase N) (r : MovingLevel d) :
    (containedRate N (movingLength N d) : ℝ)/(2 : ℝ)^((levelEquiv d).symm r+1)=
      ((N-movingLength N d : ℕ) : ℝ)*(2 : ℝ)^(-(criticalBase N : ℝ)-(r.val : ℝ)-1) := by
  rw [containedRate_coe]
  have h := exact_site_mean hd ((levelEquiv d).symm r)
  simp only [Equiv.apply_symm_apply] at h
  calc
    _ = ((N-movingLength N d : ℕ) : ℝ)*(1/(2 : ℝ)^(movingLength N d+(levelEquiv d).symm r+1)) := by
      rw [show movingLength N d+(levelEquiv d).symm r+1=movingLength N d+((levelEquiv d).symm r+1) by omega,pow_add]
      ring
    _ = _ := by rw [h]

/-- The path retains the same base-contained sites at every centered threshold. -/
theorem conditional_moving_path_distance_eq (N d : ℕ) (A : Set InfiniteSample) :
    massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure A
      (fun omega r => startCount (containedStarts N (movingLength N d))
        (movingLength N d+(levelEquiv d).symm r) omega))
      (pushforwardMass (levelPathEquiv d)
        (pushforwardMass thresholdFunction (geometricConfigurationLaw (containedRate N (movingLength N d)))))=
      unsignedMovingAggregateDistance N d A := by
  change massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure A
    (levelPathEquiv d ∘ (fun omega m => startCount (containedStarts N (movingLength N d)) (movingLength N d+m) omega))) _=_
  rw [conditionalObservableLaw_equiv_eq,massTotalVariation_equiv]
  exact (conditional_start_path_distance_eq (containedStarts N (movingLength N d))
    (movingLength N d) (fun x hx => (mem_containedStarts.mp hx).1) A).trans
      (unsignedMovingAggregateDistance_eq N d A).symm

/-- Both centered exact laws converge under the same single-intensity budget. -/
theorem moving_aggregate_comparison_tendsto_zero (hStein : DirectionalSteinFactorsStatement)
    (hPNT : PrimeNumberTheoremRemainder) (hLS : UniformPrimeDivisorStatement)
    (hShorey : ShoreySquareProductStatement) (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (c : ℝ) (hc : 0<c) (sizes depths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop)
    (hdepths : Tendsto (fun n => (depths n : ℝ)/Real.log (sizes n)) atTop (𝓝 0))
    (A : ℕ→Set InfiniteSample)
    (hA : ∀ᶠ n in atTop,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff (sizes n))) inferInstance] (A n))
    (hpos : ∀ᶠ n in atTop, 0 < infiniteRademacherMeasure.real (A n))
    (hbudget : ∀ᶠ n in atTop,
      aggregateLogCost (eventInformation (A n)) (fullRate (sizes n) (movingLength (sizes n) (depths n)))≤
        saddleCutoff 1 (Real.log (sizes n))-c*saddleNu 1 (Real.log (sizes n))) :
    Tendsto (fun n => signedMovingAggregateDistance (sizes n) (depths n) (A n)) atTop (𝓝 0) ∧
    Tendsto (fun n => unsignedMovingAggregateDistance (sizes n) (depths n) (A n)) atTop (𝓝 0) := by
  have h := moving_aggregate_sequence_tendsto_zero hStein hPNT hLS hShorey hNR c hc sizes depths hsizes hdepths A hA hpos hbudget
  have hs : Tendsto (fun n => signedMovingAggregateDistance (sizes n) (depths n) (A n)) atTop (𝓝 0) := by
    simpa only [signedMovingAggregateDistance_eq] using h
  refine ⟨hs,?_⟩
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => massTotalVariation_nonneg _ _)) _ hs
  filter_upwards [hpos] with n hn
  exact (unsignedMovingAggregateDistance_eq (sizes n) (depths n) (A n)).le.trans
    ((conditional_unsigned_le_signed _ _ _ hn).trans
      (signedMovingAggregateDistance_eq (sizes n) (depths n) (A n)).symm.le)

/-- The whole actual centered threshold path inherits the same convergence, with no finite-level restriction. -/
theorem moving_path_comparison_tendsto_zero (hStein : DirectionalSteinFactorsStatement)
    (hPNT : PrimeNumberTheoremRemainder) (hLS : UniformPrimeDivisorStatement)
    (hShorey : ShoreySquareProductStatement) (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (c : ℝ) (hc : 0<c) (sizes depths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop)
    (hdepths : Tendsto (fun n => (depths n : ℝ)/Real.log (sizes n)) atTop (𝓝 0))
    (A : ℕ→Set InfiniteSample)
    (hA : ∀ᶠ n in atTop,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff (sizes n))) inferInstance] (A n))
    (hpos : ∀ᶠ n in atTop, 0 < infiniteRademacherMeasure.real (A n))
    (hbudget : ∀ᶠ n in atTop,
      aggregateLogCost (eventInformation (A n)) (fullRate (sizes n) (movingLength (sizes n) (depths n)))≤
        saddleCutoff 1 (Real.log (sizes n))-c*saddleNu 1 (Real.log (sizes n))) :
    Tendsto (fun n => massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure (A n)
      (fun omega r => startCount (containedStarts (sizes n) (movingLength (sizes n) (depths n)))
        (movingLength (sizes n) (depths n)+(levelEquiv (depths n)).symm r) omega))
      (pushforwardMass (levelPathEquiv (depths n))
        (pushforwardMass thresholdFunction (geometricConfigurationLaw
          (containedRate (sizes n) (movingLength (sizes n) (depths n))))))) atTop (𝓝 0) := by
  have h := (moving_aggregate_comparison_tendsto_zero hStein hPNT hLS hShorey hNR
    c hc sizes depths hsizes hdepths A hA hpos hbudget).2
  simpa only [conditional_moving_path_distance_eq] using h

end
end PaperC.V282.MacroAggregateCoordinates
