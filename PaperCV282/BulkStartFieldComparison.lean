import PaperCV282.BulkMarkedAggregation
import PaperCV282.BulkMarkedStable

/-! # The genuine bulk start field after summing all exact marks and signs -/
namespace PaperC.V282.BulkStartFieldComparison

open MeasureTheory ProbabilityTheory InfiniteRademacher InfiniteCylinderTransfer InfiniteConditionalWords
open BulkMarkedTypes BulkMarkedSource BulkMarkedTarget BulkMarkedComparison BulkMarkedRates BulkMarkedGeometry
open BulkMarkedAggregation ConditionedCountableLaw CountablePrimeEventTransfer CountableLawTransfer
open InfiniteMassCoupling FiniteFieldTotalVariation FiniteFieldPoissonCoupling PoissonFieldMeasure
open ConditionalStartProbability ConditionalAGGInstantiation ConditionalAGGAverage SectionThirteenFiniteBound
open PrimeEnvironmentStableLift StableProductLift SharpConditioning
open HardPoissonRates PrimeEulerPNT ProcessAGGInput AllStartSoftPoisson

noncomputable section
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

def startConditionalDistance (C Y : ℕ) (sites : Finset ℕ) (L : ℕ) : ℝ :=
  meanAtomDistance C Y (startField sites L) (poissonFieldMass (startFieldRates sites L))

def bulkStartConditionalDistance (M L : ℕ) (delta : ℝ) : ℝ :=
  startConditionalDistance (hardCutoff M) (hardCutoff M) (bulkStarts M L delta) L

/-- Erasing excesses and signs contracts the true conditional comparison on each prime atom. -/
theorem startConditionalDistance_le_signed (C Y : ℕ) (sites : Finset ℕ) (L : ℕ)
    (hsite : ∀x∈sites,2≤x) :
    startConditionalDistance C Y sites L ≤ spatialConditionalDistance C Y sites L := by
  apply finiteUniformAverage_mono
  intro sigma
  let A := infiniteSmallPrimeAtom C Y sigma
  letI instProbabilityConditionalAtom : IsProbabilityMeasure (cond infiniteRademacherMeasure A) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _
      (ExactMarkedInfinite.signed_conditioning_atom_real_pos C Y sigma))
  have h := observableLaw_statistic_tv_le (cond infiniteRademacherMeasure A) (spatialTargetMeasure sites L)
    (measurable_spatialMarkedSource sites L) measurable_id (siteCounts sites)
  have habs : cond infiniteRademacherMeasure A ≪ infiniteRademacherMeasure := cond_absolutelyContinuous
  have hae : (fun omega => siteCounts sites (spatialMarkedSource sites L omega)) =ᵐ[cond infiniteRademacherMeasure A]
      startField sites L := habs.ae_eq (ae_siteCounts_source_eq sites L hsite)
  have hs : observableLaw (cond infiniteRademacherMeasure A) ((siteCounts sites) ∘ (spatialMarkedSource sites L)) =
      conditionalObservableLaw infiniteRademacherMeasure A (startField sites L) := by
    funext k
    unfold conditionalObservableLaw
    rw [observableLaw_eq_map _ ((measurable_of_countable _).comp (measurable_spatialMarkedSource sites L)),
      observableLaw_eq_map _ (measurable_startField sites L)]
    exact congrArg (fun mu : Measure ({x // x∈sites} → ℕ) => mu.real {k}) (Measure.map_congr hae)
  have ht : observableLaw (spatialTargetMeasure sites L) ((siteCounts sites) ∘ id) =
      poissonFieldMass (startFieldRates sites L) := by
    have hh := observableLaw_of_hasLaw _ _ (hasLaw_siteCounts sites L)
    exact hh.trans (funext (fieldMeasure_real_singleton _))
  rw [hs,ht] at h
  exact h

/-- Uniform quantitative form of (7.16), at the exact same integer sites and Poisson rates. -/
theorem bulk_start_rate_eventually (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax delta epsilon eta : ℝ) (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax)
    (hdelta : 0<delta) (hepsilon : 0<epsilon) (heta : 0<eta) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ,
      betaMin*Real.log M≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log M → (fullRate M L : ℝ)≤1 →
      bulkStartConditionalDistance M L delta ≤ 67*bulkRelativeRate M L epsilon eta := by
  obtain ⟨Mr,hr⟩ := theorem_seven_seven hAGG hPNT betaMin betaMax delta epsilon eta
    hbetaMin hbeta hdelta hepsilon heta
  obtain ⟨Ml,hl⟩ := TouchingPairMass.length_pos_eventually betaMin hbetaMin
  refine ⟨max 2 (max Mr Ml),?_⟩
  intro M hM L hlo hhi hrate
  have hL := hl M (by omega) L hlo
  exact (startConditionalDistance_le_signed (hardCutoff M) (hardCutoff M) (bulkStarts M L delta) L
    (fun x hx => (Finset.mem_Icc.mp (bulkStarts_subset_Icc (by omega) hL hdelta hx)).1)).trans
    (hr M (by omega) L hlo hhi hrate)

/-- The start-field atom average is literally the conditional kernel TV integral. -/
theorem startConditionalDistance_eq_kernel_integral (M L : ℕ) (delta : ℝ) :
    bulkStartConditionalDistance M L delta = ∫ omega,
      conditionalTV infiniteRademacherMeasure
        (MeasurableSpace.comap (restrictToFinite (hardCutoff M)) inferInstance)
        (startField (bulkStarts M L delta) L)
        (fieldMeasure (startFieldRates (bulkStarts M L delta) L)) omega ∂infiniteRademacherMeasure := by
  rw [← smallPrimeSigmaAlgebra_eq_primeCylinder (le_refl (hardCutoff M))]
  have ht : observableLaw (fieldMeasure (startFieldRates (bulkStarts M L delta) L)) id =
      poissonFieldMass (startFieldRates (bulkStarts M L delta) L) := funext (fieldMeasure_real_singleton _)
  rw [mean_conditionalTV_eq_meanAtomDistance _ _ _ (measurable_startField _ _) _,ht]
  rfl

/-- Stable product factorization also holds for every recorded variable and the actual start field. -/
theorem recorded_start_joint_le_conditional {γ : Type*} [MeasurableSpace γ]
    (M L : ℕ) (delta : ℝ) (V : InfiniteSample → γ)
    (hV : Measurable[MeasurableSpace.comap (restrictToFinite (hardCutoff M)) inferInstance] V) :
    measureTotalVariation
      (infiniteRademacherMeasure.map (fun omega => (V omega,startField (bulkStarts M L delta) L omega)))
      ((infiniteRademacherMeasure.map V).prod (fieldMeasure (startFieldRates (bulkStarts M L delta) L))) ≤
      bulkStartConditionalDistance M L delta := by
  have ht : observableLaw (fieldMeasure (startFieldRates (bulkStarts M L delta) L)) id =
      poissonFieldMass (startFieldRates (bulkStarts M L delta) L) := funext (fieldMeasure_real_singleton _)
  apply fullFY_stable_product_lift (le_refl (hardCutoff M)) _ (measurable_startField _ _) _ _ ?_ V hV
  rw [ht]
  exact le_refl _

end
end PaperC.V282.BulkStartFieldComparison
