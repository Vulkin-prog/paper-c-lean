import PaperCV282.SpatialMarkedFieldComparison
import PaperCV282.CountablePrimeEventTransfer

/-!
# Actual all-mark spatial laws after positive arithmetic conditioning

The conditioning event is measurable in the full small-prime sigma-algebra.
The comparison charges the actual source tail and the mean finite-field
error by the exact inverse probability of that event.
-/
namespace PaperC.V282.SpatialMarkedEventComparison

open MeasureTheory ProbabilityTheory InfiniteRademacher InfiniteConditionalWords InfiniteCylinderTransfer
open ConditionalStartProbability SpatialMarkedTypes SpatialMarkedSource SpatialMarkedTarget
open SpatialMarkedTargetProjection SpatialMarkedFieldComparison ExactMarkedFieldBounds ExactMarkedRates
open ExactMarkedInfinite ExactMarkedFieldTransfer ConditionedCountableLaw CountablePrimeEventTransfer
open InfiniteMassCoupling FiniteFieldTotalVariation CountableLawTransfer FiniteFieldPoissonCoupling
open PrimeEulerPNT ProcessAGGInput AllStartSoftPoisson MarkedDetruncation ExactMarkedSourceTail

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

def spatialEventDistance (N L : ℕ) (A : Set InfiniteSample) : ℝ :=
  massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure A (spatialMarkedSource N L))
    (spatialTargetLaw N L)

theorem spatialEventDistance_nonneg (N L : ℕ) (A : Set InfiniteSample) :
    0 ≤ spatialEventDistance N L A := massTotalVariation_nonneg _ _

theorem spatialEventDistance_le_one (N L : ℕ) (A : Set InfiniteSample)
    (hpos : 0 < infiniteRademacherMeasure.real A) : spatialEventDistance N L A ≤ 1 :=
  massTotalVariation_le_one (hasSum_conditionalObservableLaw _ _ hpos (measurable_spatialMarkedSource N L))
    (hasSum_spatialTargetLaw N L) (conditionalObservableLaw_nonneg _ _ _) (spatialTargetLaw_nonneg N L)

/-- The finite conditional laws are the same literal atom ratios as in Theorem 5.6. -/
theorem finite_meanAtomDistance_eq (C N L E Y : ℕ) :
    meanAtomDistance C Y (infiniteSignedField N L E (dyadicBlock N))
      (poissonFieldMass (allSignedRates N L E (dyadicBlock N))) =
        exactSignedConditionalDistance C N L E Y (dyadicBlock N) := by
  have h (sigma : SmallSample C Y) :
      conditionalObservableLaw infiniteRademacherMeasure (infiniteSmallPrimeAtom C Y sigma)
        (infiniteSignedField N L E (dyadicBlock N)) = sourceConditionalSignedLaw C N L E Y (dyadicBlock N) sigma := by
    funext k
    exact conditionalObservableLaw_eq_ratio _ _ (measurableSet_infiniteSmallPrimeAtom C Y sigma) _ k
  unfold meanAtomDistance exactSignedConditionalDistance
  simp_rw [h]
  rfl

/-- Every positive full-F_Y event receives the same exact finite comparison cost. -/
theorem finite_event_tv_le {C Y : ℕ} (hYC : Y ≤ C) (N L E : ℕ)
    (A : Set InfiniteSample)
    (hA : MeasurableSet[MeasurableSpace.comap (restrictToFinite Y) inferInstance] A)
    (hpos : 0 < infiniteRademacherMeasure.real A) :
    massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure A
      (infiniteSignedField N L E (dyadicBlock N)))
      (poissonFieldMass (allSignedRates N L E (dyadicBlock N))) ≤
        exactSignedConditionalDistance C N L E Y (dyadicBlock N)/infiniteRademacherMeasure.real A := by
  have h := field_event_tv_le_mean_div_probability hYC A hA hpos
    (measurable_infiniteSignedField_full N L E)
    (hasSum_poissonFieldMass (allSignedRates N L E (dyadicBlock N)))
    (poissonFieldMass_nonneg (allSignedRates N L E (dyadicBlock N)))
  rw [finite_meanAtomDistance_eq] at h
  exact h

/-- The common countable spatial comparison, with no truncation left in either law. -/
theorem spatial_event_tv_le_finite_and_tails {C Y : ℕ} (hYC : Y ≤ C) (N L E : ℕ)
    (A : Set InfiniteSample)
    (hA : MeasurableSet[MeasurableSpace.comap (restrictToFinite Y) inferInstance] A)
    (hpos : 0 < infiniteRademacherMeasure.real A) :
    spatialEventDistance N L A ≤
      (infiniteMarkTailProbability N L E+exactSignedConditionalDistance C N L E Y (dyadicBlock N))/
        infiniteRademacherMeasure.real A+(fullRate N L : ℝ)/(2 : ℝ)^(E+1) := by
  have hAm : MeasurableSet A := by
    have hm := hA
    rw [← smallPrimeSigmaAlgebra_eq_primeCylinder hYC] at hm
    exact smallPrimeSigmaAlgebra_le C Y A hm
  letI : IsProbabilityMeasure (cond infiniteRademacherMeasure A) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hpos)
  have hs : (cond infiniteRademacherMeasure A).real {ω | spatialMarkedSource N L ω ≠
      embedConfiguration N E (infiniteSignedField N L E (dyadicBlock N) ω)} ≤
      infiniteMarkTailProbability N L E/infiniteRademacherMeasure.real A :=
    (conditional_event_le_div_probability _ A hAm _).trans
      (div_le_div_of_nonneg_right (source_embedding_disagreement_le N L E) hpos.le)
  have hm := finite_event_tv_le hYC N L E A hA hpos
  have htarget : observableLaw (spatialTargetMeasure N L) (projectConfiguration N E) =
      poissonFieldMass (allSignedRates N L E (dyadicBlock N)) := funext (spatial_project_mass_eq N L E)
  rw [← htarget] at hm
  have h := truncation_tv_le_of_bounds (cond infiniteRademacherMeasure A) (spatialTargetMeasure N L)
    (measurable_spatialMarkedSource N L) measurable_id (measurable_infiniteSignedField_full N L E)
    (measurable_of_countable (projectConfiguration N E)) (embedConfiguration N E) hs hm
    (target_embedding_disagreement_le N L E)
  simpa only [spatialEventDistance,conditionalObservableLaw,spatialTargetLaw,add_div] using h

/-- Uniform hard-cutoff field rates retain the exact information cost of conditioning. -/
theorem spatial_event_full_band (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax epsilon eta : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L E : ℕ,
      betaMin*Real.log N ≤ (L+1 : ℝ) → (L+E+2 : ℝ) ≤ betaMax*Real.log N →
      ∀ A : Set InfiniteSample,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (HardPoissonRates.hardCutoff N)) inferInstance] A →
      0 < infiniteRademacherMeasure.real A →
      spatialEventDistance N L A ≤
        (32*exactMarkedRate N L epsilon eta+
          ((fullRate N L : ℝ)/(2 : ℝ)^(E+1))*(1+(N : ℝ)^(-(1/(2 : ℝ))+epsilon)))/
            infiniteRademacherMeasure.real A+(fullRate N L : ℝ)/(2 : ℝ)^(E+1) := by
  obtain ⟨Nf,hf⟩ := theorem_five_six_signed_full_band hAGG hPNT betaMin betaMax epsilon eta
    hbetaMin hbeta hepsilon heta
  obtain ⟨Nt,ht⟩ := source_mark_tail_le_eventually betaMin betaMax epsilon hbetaMin hbeta hepsilon
  refine ⟨max Nf Nt,?_⟩
  intro N hN L E hlo hhi A hA hpos
  have hlo' : betaMin*Real.log N ≤ (L+E+2 : ℝ) := by
    have he : (0 : ℝ)≤E := by positivity
    linarith
  have hfin := (hf N (by omega) L E hlo hhi).2.1
  have htail := ht N (by omega) L E hlo' hhi
  have h := spatial_event_tv_le_finite_and_tails
    (C := max (HardPoissonRates.hardCutoff N) (dyadicCutoff N (L+E+1)))
    (Y := HardPoissonRates.hardCutoff N) (le_max_left _ _) N L E A hA hpos
  apply h.trans
  refine add_le_add ?_ le_rfl
  apply div_le_div_of_nonneg_right _ hpos.le
  linarith

end
end PaperC.V282.SpatialMarkedEventComparison
