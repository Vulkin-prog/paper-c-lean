import PaperCV282.FiniteConditionalKernel
import PaperCV282.FinitePrimeEnvironment

/-! # Stable product lift for the actual small-prime environment

The general regular conditional kernel is identified with the observed prime
atom, and its true expected TV equals the finite atom average used by the
arithmetic bounds. Arbitrary measurable recorded variables are retained.
-/
namespace PaperC.V282.PrimeEnvironmentStableLift

open MeasureTheory ProbabilityTheory Filter InfiniteRademacher InfiniteCylinderTransfer
open InfiniteConditionalWords ConditionalStartProbability FinitePrimeEnvironment
open StableConditionalKernel StableProductLift FiniteConditionalKernel
open InfiniteMassCoupling CountablePrimeEventTransfer SharpConditioning

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

variable {β γ : Type*} [MeasurableSpace β] [StandardBorelSpace β] [Nonempty β]
  [MeasurableSpace γ]

/-- The actual regular conditional law equals conditioning on the observed finite prime atom. -/
theorem conditionalKernel_ae_eq_observedAtom (C Y : ℕ)
    (f : InfiniteSample → β) (hf : Measurable f) :
    (fun ω => conditionalKernel infiniteRademacherMeasure (smallPrimeSigmaAlgebra C Y) f ω) =ᵐ[infiniteRademacherMeasure]
      (fun ω => (cond infiniteRademacherMeasure
        (infiniteSmallPrimeAtom C Y (smallPrimeRestriction C Y ω))).map f) := by
  simpa only [smallPrimeSigmaAlgebra, infiniteSmallPrimeAtom, Set.preimage, Set.mem_singleton_iff] using
    conditionalKernel_comap_ae_eq_atom infiniteRademacherMeasure
      (smallPrimeRestriction C Y) (measurable_smallPrimeRestriction C Y) f hf

theorem conditionalTV_ae_eq_environmentDistance [Countable β] [MeasurableSingletonClass β]
    (C Y : ℕ) (f : InfiniteSample → β) (hf : Measurable f)
    (ν : Measure β) [IsProbabilityMeasure ν] :
    conditionalTV infiniteRademacherMeasure (smallPrimeSigmaAlgebra C Y) f ν =ᵐ[infiniteRademacherMeasure]
      environmentDistance C Y f (observableLaw ν id) := by
  unfold environmentDistance
  simpa only [smallPrimeSigmaAlgebra, environmentDistance, infiniteSmallPrimeAtom,
    Set.preimage, Set.mem_singleton_iff] using
    conditionalTV_comap_ae_eq_atom_mass infiniteRademacherMeasure
      (smallPrimeRestriction C Y) (measurable_smallPrimeRestriction C Y) f hf ν

/-- The expected conditional TV in Lemma 6.1 is exactly the checked arithmetic atom average. -/
theorem mean_conditionalTV_eq_meanAtomDistance [Countable β] [MeasurableSingletonClass β]
    (C Y : ℕ) (f : InfiniteSample → β) (hf : Measurable f)
    (ν : Measure β) [IsProbabilityMeasure ν] :
    (∫ ω, conditionalTV infiniteRademacherMeasure (smallPrimeSigmaAlgebra C Y) f ν ω
      ∂infiniteRademacherMeasure) = meanAtomDistance C Y f (observableLaw ν id) := by
  rw [integral_congr_ae (conditionalTV_ae_eq_environmentDistance C Y f hf ν),
    integral_environmentDistance]

theorem conditionalTV_primeCylinder_ae_eq_environmentDistance
    [Countable β] [MeasurableSingletonClass β] {C Y : ℕ} (hYC : Y ≤ C)
    (f : InfiniteSample → β) (hf : Measurable f) (ν : Measure β) [IsProbabilityMeasure ν] :
    conditionalTV infiniteRademacherMeasure
      (MeasurableSpace.comap (restrictToFinite Y) inferInstance) f ν =ᵐ[infiniteRademacherMeasure]
      environmentDistance C Y f (observableLaw ν id) := by
  rw [← smallPrimeSigmaAlgebra_eq_primeCylinder hYC]
  exact conditionalTV_ae_eq_environmentDistance C Y f hf ν

/-- Every variable recorded in the full F_Y can be retained in the Poisson comparison. -/
theorem fullFY_stable_product_lift [Countable β] [MeasurableSingletonClass β]
    {C Y : ℕ} (hYC : Y ≤ C) (f : InfiniteSample → β) (hf : Measurable f)
    (ν : Measure β) [IsProbabilityMeasure ν] (ε : ℝ)
    (hmean : meanAtomDistance C Y f (observableLaw ν id) ≤ ε)
    (V : InfiniteSample → γ)
    (hV : Measurable[MeasurableSpace.comap (restrictToFinite Y) inferInstance] V) :
    measureTotalVariation (infiniteRademacherMeasure.map (fun ω => (V ω,f ω)))
      ((infiniteRademacherMeasure.map V).prod ν) ≤ ε := by
  have hVm : Measurable[smallPrimeSigmaAlgebra C Y] V := by
    rwa [smallPrimeSigmaAlgebra_eq_primeCylinder hYC]
  apply lemma_six_one infiniteRademacherMeasure (smallPrimeSigmaAlgebra_le C Y) f hf ν ε _ V hVm
  rwa [mean_conditionalTV_eq_meanAtomDistance C Y f hf ν]

/-- Positive full-F_Y conditioning preserves the recorded variable with one inverse probability. -/
theorem fullFY_conditioned_stable_product_lift [Countable β] [MeasurableSingletonClass β]
    {C Y : ℕ} (hYC : Y ≤ C) (f : InfiniteSample → β) (hf : Measurable f)
    (ν : Measure β) [IsProbabilityMeasure ν] (ε : ℝ)
    (hmean : meanAtomDistance C Y f (observableLaw ν id) ≤ ε)
    (V : InfiniteSample → γ)
    (hV : Measurable[MeasurableSpace.comap (restrictToFinite Y) inferInstance] V)
    (D : Set InfiniteSample)
    (hD : MeasurableSet[MeasurableSpace.comap (restrictToFinite Y) inferInstance] D)
    (hpos : 0 < infiniteRademacherMeasure.real D) :
    measureTotalVariation ((cond infiniteRademacherMeasure D).map f) ν ≤
      ε / infiniteRademacherMeasure.real D ∧
    measureTotalVariation ((cond infiniteRademacherMeasure D).map (fun ω => (V ω,f ω)))
      (((cond infiniteRademacherMeasure D).map V).prod ν) ≤ ε / infiniteRademacherMeasure.real D := by
  have hVm : Measurable[smallPrimeSigmaAlgebra C Y] V := by
    rwa [smallPrimeSigmaAlgebra_eq_primeCylinder hYC]
  have hDm : MeasurableSet[smallPrimeSigmaAlgebra C Y] D := by
    rwa [smallPrimeSigmaAlgebra_eq_primeCylinder hYC]
  apply lemma_six_one_conditioned infiniteRademacherMeasure (smallPrimeSigmaAlgebra_le C Y)
    f hf ν ε _ V hVm D hDm hpos
  rwa [mean_conditionalTV_eq_meanAtomDistance C Y f hf ν]

end
end PaperC.V282.PrimeEnvironmentStableLift
