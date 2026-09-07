import PaperCV282.AffineCrossoverErrorsNormalized
import PaperCV282.AffineCrossoverCylinderInformation

/-! # The strong information budget for actual varying affine cylinders

The codomains, matrices and right-hand sides may all vary. Compatibility is
required only eventually, and the true conditional border probability is used
at every index, so no artificial choice of a cutoff proof is part of the rate.
-/
namespace PaperC.V282.AffineCrossoverErrorsAffine

open MeasureTheory ProbabilityTheory Filter Topology InfiniteRademacher InfiniteCylinderTransfer Affine
open AffineCrossoverErrorsNormalized AffineCrossoverModel AffineCrossoverCylinder AffineCrossoverCylinderInformation
open AffineBorderCylinders CrossoverBulkAtoms BulkMarkedGeometry
open RareConditioningRates HardPoissonRates AllStartSoftPoisson PrimeEulerPNT ProcessAGGInput
open SaddleParameters SaddleScales MicroscopicNonvacancy MicroscopicBorderEvents RarePrefixEvents
open LaishramUniformInput PostQuadraticLiterature
open scoped NNReal

noncomputable section
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- A genuine marginal, defined even at the finitely many indices preceding admissibility. -/
def conditionalBorderRate (A : Set InfiniteSample) (L : ℕ) : ℝ≥0 :=
  ⟨(conditionedMeasure A).real (borderEvent L),measureReal_nonneg⟩

theorem conditionalBorderRate_eq {Y L : ℕ} {W : Type*} [AddCommGroup W] [Module F₂ W]
    (G : SampleSpace Y→ₗ[F₂]W) (b : W) (hLY : L≤Y)
    (hstack : Compatible (G.prod (borderProjection hLY)) (b,0)) :
    conditionalBorderRate (affineCylinder G b) L=borderRate G hLY := by
  apply NNReal.eq
  exact conditional_border_probability G b hLY hstack

/-- Every input to the conditioned comparison is derived from the actual affine equations. -/
theorem affine_event_inputs
    (sizes lengths : ℕ→ℕ) (W : ℕ→Type*) [∀ n,AddCommGroup (W n)] [∀ n,Module F₂ (W n)]
    (G : ∀ n,SampleSpace (hardCutoff (sizes n))→ₗ[F₂]W n) (b : ∀ n,W n)
    (hstack : ∀ᶠ n in atTop,∃ hLY : lengths n≤hardCutoff (sizes n),
      Compatible ((G n).prod (borderProjection hLY)) (b n,0)) (c : ℝ)
    (hbudget : ∀ᶠ n in atTop,cylinderInformation (G n)≤saddleCutoff 1 (Real.log (sizes n))-
      c*saddleNu 1 (Real.log (sizes n))) :
    (∀ᶠ n in atTop,MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff (sizes n))) inferInstance]
      (affineCylinder (G n) (b n))) ∧
    (∀ᶠ n in atTop,0 < infiniteRademacherMeasure.real (affineCylinder (G n) (b n))) ∧
    (∀ᶠ n in atTop,eventInformation (affineCylinder (G n) (b n))≤saddleCutoff 1 (Real.log (sizes n))-
      c*saddleNu 1 (Real.log (sizes n))) ∧
    (∀ᶠ n in atTop,(CrossoverMarkedTarget.borderRate (lengths n) : ℝ)≤
      (conditionalBorderRate (affineCylinder (G n) (b n)) (lengths n) : ℝ)) := by
  refine ⟨Eventually.of_forall fun n => measurableSet_affineCylinder_fullFY (G n) (b n),?_,?_,?_⟩
  · filter_upwards [hstack] with n hn
    obtain ⟨hLY,hs⟩ := hn
    exact affineCylinder_probability_pos _ _ (stacked_compatible_implies_compatible _ _ hLY hs)
  · filter_upwards [hstack,hbudget] with n hn hb
    obtain ⟨hLY,hs⟩ := hn
    rwa [eventInformation_eq_cylinderInformation _ _ (stacked_compatible_implies_compatible _ _ hLY hs)]
  · filter_upwards [hstack] with n hn
    obtain ⟨hLY,hs⟩ := hn
    rw [conditionalBorderRate_eq _ _ hLY hs]
    have h := raw_border_probability_le_rate (G n) hLY
    simpa only [CrossoverRareScale.borderRate_coe,equation_seven_one] using h

/-- The five actual limits needed by the affine crossover theorem, with no assumed error limits. -/
theorem affine_errors_under_rank_budget
    (hAGG : ProcessAGGStatement) (hLS : UniformPrimeDivisorStatement)
    (hShorey : ShoreySquareProductStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (sizes lengths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop) (hlengths : Tendsto lengths atTop atTop)
    (K : ℕ) (beta delta c : ℝ) (hbeta : 0<beta) (hdelta : 0<delta) (hdeltaOne : delta<1) (hc : 0<c)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hrare : Tendsto (fun n => (fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0))
    (W : ℕ→Type*) [∀ n,AddCommGroup (W n)] [∀ n,Module F₂ (W n)]
    (G : ∀ n,SampleSpace (hardCutoff (sizes n))→ₗ[F₂]W n) (b : ∀ n,W n)
    (hstack : ∀ᶠ n in atTop,∃ hLY : lengths n≤hardCutoff (sizes n),
      Compatible ((G n).prod (borderProjection hLY)) (b n,0))
    (hbudget : ∀ᶠ n in atTop,cylinderInformation (G n)≤saddleCutoff 1 (Real.log (sizes n))-
      c*saddleNu 1 (Real.log (sizes n))) :
    let A := fun n => affineCylinder (G n) (b n)
    let alpha := fun n => conditionalBorderRate (A n) (lengths n)
    Tendsto (fun n => (alpha n : ℝ)) atTop (𝓝 0) ∧
    Tendsto (fun n => (conditionedMeasure (A n)).real (interiorEvent (lengths n))/(alpha n : ℝ)) atTop (𝓝 0) ∧
    Tendsto (fun n => (conditionedMeasure (A n)).real (interiorEvent (lengths n))/
      ((alpha n : ℝ)+(totalRate (bulkStarts (sizes n) (lengths n) delta) (lengths n) : ℝ))) atTop (𝓝 0) ∧
    Tendsto (fun n => (conditionedMeasure (A n)).real (middleEvent (sizes n) (lengths n) delta)/
      ((alpha n : ℝ)+(totalRate (bulkStarts (sizes n) (lengths n) delta) (lengths n) : ℝ))) atTop (𝓝 0) ∧
    Tendsto (fun n => jointDistance (conditionedMeasure (A n)) (sizes n) (lengths n) K delta/
      ((alpha n : ℝ)+(totalRate (bulkStarts (sizes n) (lengths n) delta) (lengths n) : ℝ))) atTop (𝓝 0) := by
  dsimp only
  obtain ⟨hFY,hpos,hI,hdom⟩ := affine_event_inputs sizes lengths W G b hstack c hbudget
  have hA : ∀ᶠ n in atTop,MeasurableSet (affineCylinder (G n) (b n)) :=
    Eventually.of_forall fun n => measurableSet_affineCylinder (G n) (b n)
  have heq : ∀ᶠ n in atTop,(conditionedMeasure (affineCylinder (G n) (b n))).real (borderEvent (lengths n))=
      (conditionalBorderRate (affineCylinder (G n) (b n)) (lengths n) : ℝ) := Eventually.of_forall fun _ => rfl
  obtain ⟨ha,hia,hi,hm⟩ := conditional_exceptions_affine_scale hLS hShorey hPNT hNR sizes lengths hsizes hlengths
    beta delta c hbeta hdelta hdeltaOne hc hupper hrare _ hA hpos hI _ heq hdom
  exact ⟨ha,hia,hi,hm,conditional_joint_affine_scale hAGG hPNT sizes lengths hsizes hlengths K beta delta c
    hbeta hdelta hdeltaOne hc hupper hrare _ hFY hpos hI _ hdom⟩

end
end PaperC.V282.AffineCrossoverErrorsAffine
