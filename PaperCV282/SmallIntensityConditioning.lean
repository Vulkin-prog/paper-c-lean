import PaperCV282.PoissonRareProbabilities
import PaperCV282.HardRelativeMargin
import PaperCV282.PoissonGaussianSource

/-! # Equation (6.3): actual relative probabilities at small intensity

The normalization uses the true intensity and the source is conditioned on
the actual positive event in the full hard small-prime field.
-/
namespace PaperC.V282.SmallIntensityConditioning

open MeasureTheory ProbabilityTheory Filter Topology
open InfiniteRademacher InfiniteCylinderTransfer InfiniteConditionalWords
open InfiniteStartProbabilityTransfer InfiniteMaskedScalarTransfer
open RestrictedPoissonTransfer RareConditioningRates HardPoissonRates HardRelativeMargin
open AllStartSoftPoisson ScalarSteinInput PrimeEulerPNT SaddleParameters SaddleScales
open PoissonRareProbabilities PoissonGaussianSource SharpConditioning SharpConditioningDiscrete
open InfiniteMassCoupling ConditionedCountableLaw FiniteFieldTotalVariation SectionThirteenFiniteBound

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

def conditionalStartMeasure (N L : ℕ) (C : Set InfiniteSample) : Measure ℕ :=
  (cond infiniteRademacherMeasure C).map (infiniteDyadicStartCount N L)

theorem conditionalStartMeasure_singleton (N L : ℕ) (C : Set InfiniteSample)
    (hC : MeasurableSet C) (k : ℕ) :
    (conditionalStartMeasure N L C).real {k} = restrictedCountLaw N L C k := by
  rw [conditionalStartMeasure, ← observableLaw_eq_map _ (measurable_source_startCount N L) k]
  change conditionalObservableLaw infiniteRademacherMeasure C (infiniteDyadicStartCount N L) k = _
  rw [conditionalObservableLaw_eq_ratio _ _ hC]
  rfl

theorem conditionalStartMeasure_tv_eq (N L : ℕ) (C : Set InfiniteSample)
    (hC : MeasurableSet C) (hpos : 0 < infiniteRademacherMeasure.real C) :
    measureTotalVariation (conditionalStartMeasure N L C) (poissonMeasure (fullRate N L)) =
      natTotalVariation (restrictedCountLaw N L C) (poissonMass (fullRate N L)) := by
  letI instProbabilityConditionalSource : IsProbabilityMeasure (cond infiniteRademacherMeasure C) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hpos)
  letI instProbabilityConditionalCount : IsProbabilityMeasure (conditionalStartMeasure N L C) :=
    Measure.isProbabilityMeasure_map (measurable_source_startCount N L).aemeasurable
  rw [measureTotalVariation_eq_mass]
  change massTotalVariation (fun k => (conditionalStartMeasure N L C).real {k})
    (poissonMass (fullRate N L)) = _
  simp_rw [conditionalStartMeasure_singleton N L C hC]
  rfl

theorem conditionalStartMeasure_event (N L : ℕ) (C : Set InfiniteSample) (A : Set ℕ) :
    (conditionalStartMeasure N L C).real A =
      (cond infiniteRademacherMeasure C).real {omega | infiniteDyadicStartCount N L omega ∈ A} := by
  rw [conditionalStartMeasure, Measure.real, Measure.map_apply (measurable_source_startCount N L)
    (Set.to_countable A).measurableSet]
  rfl

/-- Both true conditional rare-event probabilities admit the same explicit relative error. -/
theorem small_intensity_relative_bound (hStein : ScalarSteinFactorsStatement)
    (hPNT : PrimeNumberTheoremRemainder) (betaMin betaMax c : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax) (hc : 0 < c) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L+1 : ℝ) → (L+1 : ℝ) ≤ betaMax * Real.log N →
      ∀ C : Set InfiniteSample,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff N)) inferInstance] C →
      0 < infiniteRademacherMeasure.real C →
      eventInformation C ≤ saddleCutoff 1 (Real.log N)-c*saddleNu 1 (Real.log N) →
      |(cond infiniteRademacherMeasure C).real {omega | 0 < infiniteDyadicStartCount N L omega}/
          (fullRate N L : ℝ)-1| ≤ hardRelativeMargin N c + (fullRate N L : ℝ) ∧
      |(cond infiniteRademacherMeasure C).real {omega | infiniteDyadicStartCount N L omega=1}/
          (fullRate N L : ℝ)-1| ≤ hardRelativeMargin N c + (fullRate N L : ℝ) := by
  obtain ⟨Nr,hr⟩ := hard_relative_margin_eventually hStein hPNT betaMin betaMax c hbetaMin hbeta hc
  refine ⟨max Nr 2, ?_⟩
  intro N hN L hlo hhi C hC hpos hb
  have hCm : MeasurableSet C := by
    have hm := hC
    rw [← smallPrimeSigmaAlgebra_eq_primeCylinder (M := hardCutoff N) le_rfl] at hm
    exact smallPrimeSigmaAlgebra_le (hardCutoff N) (hardCutoff N) C hm
  letI instProbabilityConditionalSource : IsProbabilityMeasure (cond infiniteRademacherMeasure C) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hpos)
  letI instProbabilityConditionalCount : IsProbabilityMeasure (conditionalStartMeasure N L C) :=
    Measure.isProbabilityMeasure_map (measurable_source_startCount N L).aemeasurable
  have hrpos : 0 < fullRate N L := by
    change (0 : ℝ) < (N : ℝ)/2^L
    have hn : 0 < N := by omega
    positivity
  have h := rare_probabilities_relative_bound (conditionalStartMeasure N L C) (fullRate N L) hrpos
  rw [conditionalStartMeasure_tv_eq N L C hCm hpos,
    conditionalStartMeasure_event, conditionalStartMeasure_event] at h
  have hbound := add_le_add (hr N (by omega) L hlo hhi C hC hpos hb) (le_refl (fullRate N L : ℝ))
  exact ⟨h.1.trans hbound,h.2.trans hbound⟩

/-- Equation (6.3), including arbitrary size subsequences and moving conditioning events. -/
theorem equation_six_three (hStein : ScalarSteinFactorsStatement)
    (hPNT : PrimeNumberTheoremRemainder) (betaMin betaMax c : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax) (hc : 0 < c)
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop)
    (C : ℕ → Set InfiniteSample)
    (hband : ∀ᶠ k in atTop, betaMin * Real.log (sizes k) ≤ (lengths k+1 : ℝ) ∧
      (lengths k+1 : ℝ) ≤ betaMax * Real.log (sizes k))
    (hC : ∀ᶠ k in atTop,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff (sizes k))) inferInstance] (C k))
    (hpos : ∀ᶠ k in atTop, 0 < infiniteRademacherMeasure.real (C k))
    (hbudget : ∀ᶠ k in atTop, eventInformation (C k) ≤
      saddleCutoff 1 (Real.log (sizes k))-c*saddleNu 1 (Real.log (sizes k)))
    (hrate : Tendsto (fun k => (fullRate (sizes k) (lengths k) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun k => (cond infiniteRademacherMeasure (C k)).real
      {omega | 0 < infiniteDyadicStartCount (sizes k) (lengths k) omega}/
        (fullRate (sizes k) (lengths k) : ℝ)) atTop (𝓝 1) ∧
    Tendsto (fun k => (cond infiniteRademacherMeasure (C k)).real
      {omega | infiniteDyadicStartCount (sizes k) (lengths k) omega=1}/
        (fullRate (sizes k) (lengths k) : ℝ)) atTop (𝓝 1) := by
  obtain ⟨Nzero,hzero⟩ := small_intensity_relative_bound hStein hPNT betaMin betaMax c hbetaMin hbeta hc
  have hbounds := hsizes.eventually (eventually_ge_atTop Nzero)
  have hlim : Tendsto (fun k => hardRelativeMargin (sizes k) c + (fullRate (sizes k) (lengths k) : ℝ))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, add_zero] using
      ((hardRelativeMargin_tendsto_zero hc).comp hsizes).add hrate
  have hh : ∀ᶠ k in atTop,
      |(cond infiniteRademacherMeasure (C k)).real
        {omega | 0 < infiniteDyadicStartCount (sizes k) (lengths k) omega}/
          (fullRate (sizes k) (lengths k) : ℝ)-1| ≤
          hardRelativeMargin (sizes k) c + (fullRate (sizes k) (lengths k) : ℝ) ∧
      |(cond infiniteRademacherMeasure (C k)).real
        {omega | infiniteDyadicStartCount (sizes k) (lengths k) omega=1}/
          (fullRate (sizes k) (lengths k) : ℝ)-1| ≤
          hardRelativeMargin (sizes k) c + (fullRate (sizes k) (lengths k) : ℝ) := by
    filter_upwards [hbounds,hband,hC,hpos,hbudget] with k hN hb hm hp hi
    exact hzero (sizes k) hN (lengths k) hb.1 hb.2 (C k) hm hp hi
  constructor
  · apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [Real.norm_eq_abs] using squeeze_zero'
      (Eventually.of_forall (fun _ => abs_nonneg _)) (hh.mono fun _ h => h.1) hlim
  · apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [Real.norm_eq_abs] using squeeze_zero'
      (Eventually.of_forall (fun _ => abs_nonneg _)) (hh.mono fun _ h => h.2) hlim

end
end PaperC.V282.SmallIntensityConditioning
