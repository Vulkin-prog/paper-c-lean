import PaperCV282.BulkMarkedRates
import PaperCV282.PrimeEnvironmentStableLift

/-! # Stable product lifting for the genuine signed bulk kernel -/
namespace PaperC.V282.BulkMarkedStable

open MeasureTheory ProbabilityTheory InfiniteRademacher InfiniteCylinderTransfer
open BulkMarkedTypes BulkMarkedSource BulkMarkedTarget BulkMarkedComparison BulkMarkedRates BulkMarkedGeometry
open PrimeEnvironmentStableLift StableConditionalKernel StableProductLift SharpConditioning
open HardPoissonRates PrimeEulerPNT ProcessAGGInput AllStartSoftPoisson

noncomputable section
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- The atom average equals the actual regular conditional total-variation integral. -/
theorem bulkConditionalDistance_eq_kernel_integral (M L : ℕ) (delta : ℝ) :
    bulkConditionalDistance M L delta = ∫ omega,
      conditionalTV infiniteRademacherMeasure
        (MeasurableSpace.comap (restrictToFinite (hardCutoff M)) inferInstance)
        (spatialMarkedSource (bulkStarts M L delta) L)
        (spatialTargetMeasure (bulkStarts M L delta) L) omega ∂infiniteRademacherMeasure := by
  rw [← InfiniteConditionalWords.smallPrimeSigmaAlgebra_eq_primeCylinder (le_refl (hardCutoff M))]
  exact (mean_conditionalTV_eq_meanAtomDistance _ _ _ (measurable_spatialMarkedSource _ _) _).symm

/-- Any recorded full-F_Y variable can be kept in the actual joint comparison. -/
theorem recorded_joint_le_conditional {γ : Type*} [MeasurableSpace γ]
    (M L : ℕ) (delta : ℝ) (V : InfiniteSample → γ)
    (hV : Measurable[MeasurableSpace.comap (restrictToFinite (hardCutoff M)) inferInstance] V) :
    measureTotalVariation
      (infiniteRademacherMeasure.map (fun omega => (V omega,spatialMarkedSource (bulkStarts M L delta) L omega)))
      ((infiniteRademacherMeasure.map V).prod (spatialTargetMeasure (bulkStarts M L delta) L)) ≤
      bulkConditionalDistance M L delta := by
  exact fullFY_stable_product_lift (le_refl (hardCutoff M)) _ (measurable_spatialMarkedSource _ _) _ _ (le_refl _) V hV

/-- A quantitative form of stable factorization, with a threshold preceding the recorded variable. -/
theorem recorded_joint_rate_eventually {γ : Type*} [MeasurableSpace γ]
    (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax delta epsilon eta : ℝ) (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax)
    (hdelta : 0<delta) (hepsilon : 0<epsilon) (heta : 0<eta) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ,
      betaMin*Real.log M≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log M → (fullRate M L : ℝ)≤1 →
      ∀ V : InfiniteSample → γ,
      Measurable[MeasurableSpace.comap (restrictToFinite (hardCutoff M)) inferInstance] V →
      measureTotalVariation
        (infiniteRademacherMeasure.map (fun omega => (V omega,spatialMarkedSource (bulkStarts M L delta) L omega)))
        ((infiniteRademacherMeasure.map V).prod (spatialTargetMeasure (bulkStarts M L delta) L)) ≤
        67*bulkRelativeRate M L epsilon eta := by
  obtain ⟨Mzero,hzero⟩ := theorem_seven_seven hAGG hPNT betaMin betaMax delta epsilon eta
    hbetaMin hbeta hdelta hepsilon heta
  refine ⟨Mzero,?_⟩
  intro M hM L hlo hhi hrate V hV
  exact (recorded_joint_le_conditional M L delta V hV).trans (hzero M hM L hlo hhi hrate)

end
end PaperC.V282.BulkMarkedStable
