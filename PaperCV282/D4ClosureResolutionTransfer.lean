import PaperCV282.D4ClosureSpatialResolution
import PaperCV282.SpatialBoundedInformation

/-! # Resolution of the genuine arithmetic spatial configuration

The input to sharp conditioning is the proved full-field estimate. No
local probability or resolved-law approximation is assumed.
-/
namespace PaperC.V282.D4ClosureResolutionTransfer

open MeasureTheory ProbabilityTheory Filter
open D4ClosureSpatialResolution SpatialMarkedTypes SpatialMarkedTarget SpatialMarkedSource
open SpatialMarkedTargetAggregation SpatialMarkedEventComparison SpatialMarkedFieldComparison
open SpatialBoundedInformation SharpConditioning SharpConditioningDiscrete
open InfiniteRademacher InfiniteCylinderTransfer InfiniteMassCoupling ConditionedCountableLaw
open AllStartSoftPoisson PrimeEulerPNT ProcessAGGInput RareConditioningRates
open HardPoissonRates SaddleParameters SaddleScales
open scoped Topology NNReal

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

def arithmeticSpatialMeasure (N L : ℕ) (A : Set InfiniteSample) : Measure (SpatialMarkedConfig N) :=
  (cond infiniteRademacherMeasure A).map (spatialMarkedSource N L)

def resolvedArithmeticSpatialMeasure (N L n : ℕ) (A : Set InfiniteSample) : Measure (SpatialMarkedConfig N) :=
  cond (arithmeticSpatialMeasure N L A) {c | totalSpatialCount N c = n}

theorem resolvedArithmeticSpatialMeasure_eq (N L n : ℕ) (A : Set InfiniteSample) :
    resolvedArithmeticSpatialMeasure N L n A =
      (cond (cond infiniteRademacherMeasure A)
        {omega | totalSpatialCount N (spatialMarkedSource N L omega) = n}).map
          (spatialMarkedSource N L) := by
  exact (map_cond_eq _ (measurable_spatialMarkedSource N L) _
    ((Set.to_countable _).measurableSet)).symm

theorem arithmetic_spatial_tv_eq (N L : ℕ) (A : Set InfiniteSample)
    (hpos : 0 < infiniteRademacherMeasure.real A) :
    measureTotalVariation (arithmeticSpatialMeasure N L A) (spatialTargetMeasure N L) =
      spatialEventDistance N L A := by
  letI instProbabilityConditioned : IsProbabilityMeasure (cond infiniteRademacherMeasure A) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hpos)
  letI instProbabilitySpatial : IsProbabilityMeasure (arithmeticSpatialMeasure N L A) :=
    Measure.isProbabilityMeasure_map (measurable_spatialMarkedSource N L).aemeasurable
  rw [measureTotalVariation_eq_mass]
  unfold spatialEventDistance spatialTargetLaw
  congr 1
  funext c
  change (arithmeticSpatialMeasure N L A).real {c} = _
  exact (observableLaw_eq_map _ (measurable_spatialMarkedSource N L) c).symm

theorem resolved_spatial_bound (N L n : ℕ) (A : Set InfiniteSample)
    (hpos : 0 < infiniteRademacherMeasure.real A)
    (herr : spatialEventDistance N L A <
      (poissonMeasure (fullRate N L)).real {n}) :
    0 < (arithmeticSpatialMeasure N L A).real {c | totalSpatialCount N c = n} ∧
    measureTotalVariation (resolvedArithmeticSpatialMeasure N L n A)
      (cond (spatialTargetMeasure N L) {c | totalSpatialCount N c = n}) ≤
        spatialEventDistance N L A / (poissonMeasure (fullRate N L)).real {n} := by
  letI instProbabilityConditioned : IsProbabilityMeasure (cond infiniteRademacherMeasure A) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hpos)
  letI instProbabilitySpatial : IsProbabilityMeasure (arithmeticSpatialMeasure N L A) :=
    Measure.isProbabilityMeasure_map (measurable_spatialMarkedSource N L).aemeasurable
  have hprob : (spatialTargetMeasure N L).real {v | totalSpatialCount N v = n} =
      (poissonMeasure (fullRate N L)).real {n} :=
    (hasLaw_totalSpatialCount N L).measureReal_eq (measurableSet_singleton n)
  obtain ⟨hp, ht, ht'⟩ := lemma_six_two (arithmeticSpatialMeasure N L A) (spatialTargetMeasure N L)
    {c | totalSpatialCount N c = n} ((Set.to_countable _).measurableSet)
    (le_of_eq (arithmetic_spatial_tv_eq N L A hpos)) (by simpa only [hprob] using herr)
  refine ⟨hp, ?_⟩
  have hfinal := ht.trans ht'
  rw [hprob] at hfinal
  convert hfinal using 1 <;> congr! 3

/-- Fixed-count spatial resolution under the printed critical information margin. -/
theorem arithmetic_spatial_resolution_tendsto_zero
    (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop)
    (lo hi K c : ℝ) (hlo : 0 < lo) (hhi : lo < hi) (hc : 0 < c)
    (A : ℕ → Set InfiniteSample) (rate : ℝ≥0) (hrate : 0 < rate) (n : ℕ)
    (hrates : Tendsto (fun k => (fullRate (sizes k) (lengths k) : ℝ)) atTop (𝓝 (rate : ℝ)))
    (hband : ∀ᶠ k in atTop, lo*Real.log (sizes k) ≤ (lengths k+1 : ℝ) ∧
      (lengths k+1 : ℝ) ≤ hi*Real.log (sizes k))
    (hK : ∀ᶠ k in atTop, (fullRate (sizes k) (lengths k) : ℝ) ≤ K)
    (hA : ∀ᶠ k in atTop,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff (sizes k))) inferInstance] (A k))
    (hpos : ∀ᶠ k in atTop, 0 < infiniteRademacherMeasure.real (A k))
    (hbudget : ∀ᶠ k in atTop, eventInformation (A k) ≤
      saddleCutoff 1 (Real.log (sizes k))-c*saddleNu 1 (Real.log (sizes k))) :
    (∀ᶠ k in atTop, 0 < (arithmeticSpatialMeasure (sizes k) (lengths k) (A k)).real
      {v | totalSpatialCount (sizes k) v = n}) ∧
    Tendsto (fun k => measureTotalVariation
      (resolvedArithmeticSpatialMeasure (sizes k) (lengths k) n (A k))
      (cond (spatialTargetMeasure (sizes k) (lengths k))
        {v | totalSpatialCount (sizes k) v = n})) atTop (𝓝 0) := by
  have htv := spatial_event_tendsto_zero hAGG hPNT sizes lengths hsizes lo hi K c
    hlo hhi hc A hband hK hA hpos hbudget
  have hprob : Tendsto (fun k => (poissonMeasure (fullRate (sizes k) (lengths k))).real {n})
      atTop (𝓝 ((poissonMeasure rate).real {n})) := by
    simp_rw [poissonMeasure_real_singleton]
    exact ((Real.continuous_exp.continuousAt.tendsto.comp hrates.neg).mul (hrates.pow n)).div_const n.factorial
  have hp : 0 < (poissonMeasure rate).real {n} := by
    rw [poissonMeasure_real_singleton]
    have hr : 0 < (rate : ℝ) := hrate
    positivity
  have herr := Filter.Tendsto.eventually_lt htv hprob hp
  have hb : ∀ᶠ k in atTop,
      0 < (arithmeticSpatialMeasure (sizes k) (lengths k) (A k)).real
        {v | totalSpatialCount (sizes k) v = n} ∧
      measureTotalVariation (resolvedArithmeticSpatialMeasure (sizes k) (lengths k) n (A k))
        (cond (spatialTargetMeasure (sizes k) (lengths k)) {v | totalSpatialCount (sizes k) v = n}) ≤
        spatialEventDistance (sizes k) (lengths k) (A k) /
          (poissonMeasure (fullRate (sizes k) (lengths k))).real {n} := by
    filter_upwards [hpos, herr] with k ha he
    exact resolved_spatial_bound _ _ _ _ ha he
  refine ⟨hb.mono fun _ h => h.1, ?_⟩
  apply squeeze_zero' ?_ (hb.mono fun _ h => h.2)
    (by
      have hquot := htv.div hprob hp.ne'
      simp only [zero_div] at hquot
      convert hquot using 1; congr! 3)
  filter_upwards [hb, hpos, herr] with k hb ha he
  letI instProbabilityConditioned : IsProbabilityMeasure (cond infiniteRademacherMeasure (A k)) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ ha)
  letI instProbabilitySpatial : IsProbabilityMeasure (arithmeticSpatialMeasure (sizes k) (lengths k) (A k)) :=
    Measure.isProbabilityMeasure_map (measurable_spatialMarkedSource _ _).aemeasurable
  letI instProbabilityResolved : IsProbabilityMeasure (resolvedArithmeticSpatialMeasure (sizes k) (lengths k) n (A k)) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hb.1)
  have hp' : 0 < (spatialTargetMeasure (sizes k) (lengths k)).real
      {v | totalSpatialCount (sizes k) v = n} := by
    have hid : (spatialTargetMeasure (sizes k) (lengths k)).real
        {v | totalSpatialCount (sizes k) v = n} =
        (poissonMeasure (fullRate (sizes k) (lengths k))).real {n} :=
      (hasLaw_totalSpatialCount _ _).measureReal_eq (measurableSet_singleton n)
    rw [hid]
    exact lt_of_le_of_lt (spatialEventDistance_nonneg _ _ _) he
  letI instProbabilityTargetResolved : IsProbabilityMeasure
      (cond (spatialTargetMeasure (sizes k) (lengths k)) {v | totalSpatialCount (sizes k) v = n}) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hp')
  exact measureTotalVariation_nonneg _ _

end
end PaperC.V282.D4ClosureResolutionTransfer
