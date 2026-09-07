import PaperCV282.AffineCrossoverErrors
import PaperCV282.AffineCrossoverStableClock
import PaperCV282.AffineCrossoverModel

/-! # Actual conditional errors at the affine rare scale

Only the elementary border marginal and its domination of the unconditioned
border are supplied here. All limiting errors are proved from the information
budget and the genuine full-field comparison.
-/
namespace PaperC.V282.AffineCrossoverErrorsNormalized

open MeasureTheory ProbabilityTheory Filter Topology InfiniteRademacher InfiniteCylinderTransfer
open AffineCrossoverErrors AffineCrossoverStable AffineCrossoverStableClock
open AffineCrossoverModel CrossoverRareScale CrossoverBulkAtoms BulkMarkedGeometry
open RareConditioningRates HardPoissonRates AllStartSoftPoisson PrimeEulerPNT ProcessAGGInput
open SaddleParameters SaddleScales MicroscopicNonvacancy MicroscopicBorderEvents RarePrefixEvents
open LaishramUniformInput PostQuadraticLiterature
open scoped NNReal

noncomputable section
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

theorem jointDistance_conditioned_eq (M L K : ℕ) (delta : ℝ) (A : Set InfiniteSample) :
    jointDistance (conditionedMeasure A) M L K delta =
      conditionedTruncatedJointDistance M L K delta A := rfl

/-- The three true conditional exceptional probabilities at the enlarged affine scale. -/
theorem conditional_exceptions_affine_scale
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeNumberTheoremRemainder) (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (sizes lengths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop) (hlengths : Tendsto lengths atTop atTop)
    (beta delta c : ℝ) (hbeta : 0<beta) (hdelta : 0<delta) (hdeltaOne : delta<1) (hc : 0<c)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hrare : Tendsto (fun n => (fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0))
    (A : ℕ→Set InfiniteSample) (hA : ∀ᶠ n in atTop,MeasurableSet (A n))
    (hpos : ∀ᶠ n in atTop,0 < infiniteRademacherMeasure.real (A n))
    (hbudget : ∀ᶠ n in atTop,eventInformation (A n)≤saddleCutoff 1 (Real.log (sizes n))-
      c*saddleNu 1 (Real.log (sizes n)))
    (alpha : ℕ→ℝ≥0)
    (heq : ∀ᶠ n in atTop,(conditionedMeasure (A n)).real (borderEvent (lengths n))=(alpha n : ℝ))
    (hdom : ∀ᶠ n in atTop,(CrossoverMarkedTarget.borderRate (lengths n) : ℝ)≤(alpha n : ℝ)) :
    Tendsto (fun n => (alpha n : ℝ)) atTop (𝓝 0) ∧
    Tendsto (fun n => (conditionedMeasure (A n)).real (interiorEvent (lengths n))/(alpha n : ℝ)) atTop (𝓝 0) ∧
    Tendsto (fun n => (conditionedMeasure (A n)).real (interiorEvent (lengths n))/
      ((alpha n : ℝ)+(totalRate (bulkStarts (sizes n) (lengths n) delta) (lengths n) : ℝ))) atTop (𝓝 0) ∧
    Tendsto (fun n => (conditionedMeasure (A n)).real (middleEvent (sizes n) (lengths n) delta)/
      ((alpha n : ℝ)+(totalRate (bulkStarts (sizes n) (lengths n) delta) (lengths n) : ℝ))) atTop (𝓝 0) := by
  obtain ⟨hi,hm,hb⟩ := conditional_errors_under_budget hLS hShorey hPNT hNR sizes lengths hsizes hlengths
    beta delta c hbeta hdelta hdeltaOne hc hupper hrare A hA hpos hbudget
  refine ⟨hb.congr' heq,?_,?_,?_⟩
  · apply relative_zero_of_half_le (Eventually.of_forall fun _ => measureReal_nonneg)
      (Eventually.of_forall fun n => by exact_mod_cast CrossoverMarkedTarget.borderRate_pos (lengths n)) ?_ hi
    filter_upwards [hdom] with n hn
    have ha : 0≤(CrossoverMarkedTarget.borderRate (lengths n) : ℝ) := by positivity
    linarith
  · apply relative_zero_of_half_le (Eventually.of_forall fun _ => measureReal_nonneg)
      (Eventually.of_forall fun n => by exact_mod_cast CrossoverMarkedTarget.borderRate_pos (lengths n)) ?_ hi
    filter_upwards [hdom] with n hn
    have hp : 0≤(totalRate (bulkStarts (sizes n) (lengths n) delta) (lengths n) : ℝ) := by positivity
    have ha : 0≤(CrossoverMarkedTarget.borderRate (lengths n) : ℝ) := by positivity
    linarith
  · apply relative_zero_of_half_le (Eventually.of_forall fun _ => measureReal_nonneg)
      (Eventually.of_forall fun n => rareScale_pos (sizes n) (lengths n) delta) ?_ hm
    filter_upwards [hdom] with n hn
    have hp : 0≤(totalRate (bulkStarts (sizes n) (lengths n) delta) (lengths n) : ℝ) := by positivity
    have ha : 0≤(CrossoverMarkedTarget.borderRate (lengths n) : ℝ) := by positivity
    unfold rareScale
    linarith

/-- The actual conditioned clock/field joint has relative error zero at the affine scale. -/
theorem conditional_joint_affine_scale
    (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (sizes lengths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop) (hlengths : Tendsto lengths atTop atTop)
    (K : ℕ) (beta delta c : ℝ) (hbeta : 0<beta) (hdelta : 0<delta) (hdeltaOne : delta<1) (hc : 0<c)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hrare : Tendsto (fun n => (fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0))
    (A : ℕ→Set InfiniteSample)
    (hA : ∀ᶠ n in atTop,MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff (sizes n))) inferInstance] (A n))
    (hpos : ∀ᶠ n in atTop,0 < infiniteRademacherMeasure.real (A n))
    (hbudget : ∀ᶠ n in atTop,eventInformation (A n)≤saddleCutoff 1 (Real.log (sizes n))-
      c*saddleNu 1 (Real.log (sizes n)))
    (alpha : ℕ→ℝ≥0)
    (hdom : ∀ᶠ n in atTop,(CrossoverMarkedTarget.borderRate (lengths n) : ℝ)≤(alpha n : ℝ)) :
    Tendsto (fun n => jointDistance (conditionedMeasure (A n)) (sizes n) (lengths n) K delta/
      ((alpha n : ℝ)+(totalRate (bulkStarts (sizes n) (lengths n) delta) (lengths n) : ℝ))) atTop (𝓝 0) := by
  have ht := conditioned_truncated_joint_relative_tendsto_zero hAGG hPNT sizes lengths hsizes hlengths
    K beta delta c hbeta hdelta hc hupper hrare A hA hpos hbudget
  simp only [← jointDistance_conditioned_eq] at ht
  apply relative_zero_of_half_le ?_ ?_ ?_ ht
  · filter_upwards [hpos] with n hn
    exact conditionedJointDistance_nonneg _ _ _ _
      (CrossoverPrimeClockStable.measurable_actualClockRecord _ _) _ hn
  · filter_upwards [hsizes.eventually (eventually_ge_atTop 1)] with n hn
    change 0<(sizes n : ℝ)/(2 : ℝ)^lengths n
    positivity
  · have hh := full_rate_half_le_eventually sizes lengths hsizes beta delta hdelta hdeltaOne hupper
      (hlengths.eventually (eventually_ge_atTop 1))
    filter_upwards [hh,hdom] with n hn ha
    exact hn.trans (add_le_add ha le_rfl)

end
end PaperC.V282.AffineCrossoverErrorsNormalized
