import PaperCV282.PoissonResolvedPast

/-! # Actual finite reverse segments resolved jointly with the full future -/
namespace PaperC.V282.PoissonResolvedLowerComparison

open MeasureTheory ProbabilityTheory SharpConditioning SharpConditioningDiscrete
open PoissonResolvedTarget PoissonResolvedPast PoissonResolvedComparison PoissonConfigurationSplit
open GeometricMarkedConfiguration GeometricConfigurationCounts ThresholdPathEquivalence
open UnsignedAggregateComparison InfiniteMassCoupling ConditionedCountableLaw
open InfiniteRademacher InfiniteCylinderTransfer InfiniteStartProbabilityTransfer MovingMarkedSource
open PoissonGaussianSource AllStartSoftPoisson
open scoped NNReal

noncomputable section

local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

theorem fullRate_add (N L k : ℕ) : fullRate N L / 2^k = fullRate N (L+k) := by
  apply NNReal.coe_injective
  change (N : ℝ) / 2^L / 2^k = (N : ℝ) / 2^(L+k)
  rw [div_div, pow_add]

theorem hasLaw_shiftedConfiguration (rate : ℝ≥0) (k : ℕ) :
    HasLaw (shiftedConfiguration k) (configurationMeasure (rate/2^k)) (configurationMeasure rate) := by
  refine ⟨(measurable_of_countable _).aemeasurable, ?_⟩
  have h := congrArg (fun μ : Measure ((Fin k → ℕ) × (ℕ →₀ ℕ)) => μ.map Prod.snd)
    (hasLaw_split_configuration rate k).map_eq
  rw [Measure.map_map measurable_snd (measurable_of_countable _), Measure.map_snd_prod,
    measure_univ, one_smul] at h
  exact h

theorem hasLaw_tailCount (rate : ℝ≥0) (k : ℕ) :
    HasLaw (fun c => tailCount c k) (poissonMeasure (rate/2^k)) (configurationMeasure rate) := by
  have h := (hasLaw_configurationSize (rate/2^k)).fun_comp (hasLaw_shiftedConfiguration rate k)
  simpa only [Function.comp_def, size_shifted_eq_tail] using h

theorem target_resolution_probability (N L k n : ℕ) :
    (configurationMeasure (fullRate N L)).real {c | tailCount c k=n} =
      resolutionProbability N (L+k) n := by
  have h := (hasLaw_tailCount (fullRate N L) k).measureReal_eq (measurableSet_singleton n)
  change (configurationMeasure (fullRate N L)).real {c | tailCount c k=n} =
    (poissonMeasure (fullRate N L / 2^k)).real {n} at h
  rw [fullRate_add, poissonMeasure_real_singleton] at h
  exact h

def resolvedRetainedLaw (N L k n : ℕ) (C : Set InfiniteSample) : Measure (ℕ → ℕ) :=
  (cond infiniteRademacherMeasure (C ∩ {omega | infiniteDyadicStartCount N (L+k) omega=n})).map
    (actualFuturePath N L)

theorem resolvedRetainedLaw_eq_configuration {N L : ℕ} (hN : 2≤N)
    (k n : ℕ) (C : Set InfiniteSample) (hC : MeasurableSet C) :
    resolvedRetainedLaw N L k n C =
      (cond ((cond infiniteRademacherMeasure C).map (unsignedAggregateSource N L))
        {c | tailCount c k=n}).map thresholdFunction := by
  have hcount : MeasurableSet {omega | infiniteDyadicStartCount N (L+k) omega=n} :=
    (measurable_source_startCount N (L+k)) (measurableSet_singleton n)
  have hpred : {omega | infiniteDyadicStartCount N (L+k) omega=n} =ᵐ[
      cond infiniteRademacherMeasure C]
      unsignedAggregateSource N L ⁻¹' {c | tailCount c k=n} := by
    filter_upwards [ae_future_eq_configuration hN
      (μ := cond infiniteRademacherMeasure C) cond_absolutelyContinuous] with omega h
    have hk := congrFun h k
    change (infiniteDyadicStartCount N (L+k) omega=n) = (tailCount (unsignedAggregateSource N L omega) k=n)
    rw [show infiniteDyadicStartCount N (L+k) omega=tailCount (unsignedAggregateSource N L omega) k from hk]
  unfold resolvedRetainedLaw
  rw [← cond_cond_eq_cond_inter hC hcount]
  rw [Measure.map_congr (ae_future_eq_configuration hN
    (cond_absolutelyContinuous.trans cond_absolutelyContinuous))]
  rw [cond_congr_ae _ hpred,
    ← Measure.map_map (measurable_of_countable _) (measurable_unsignedAggregateSource N L),
    map_cond_eq _ (measurable_unsignedAggregateSource N L) _ ((Set.to_countable _).measurableSet)]

/-- The reverse segment is retained jointly with the unlimited future; its error is based at the lowest level L. -/
theorem theorem_six_three_lower_segment {N L : ℕ} (hN : 2≤N)
    (k n : ℕ) (C : Set InfiniteSample) (hC : MeasurableSet C)
    (hpos : 0 < infiniteRademacherMeasure.real C) {ε : ℝ}
    (htv : conditionalUnsignedAggregateDistance N L C ≤ ε)
    (hε : ε < resolutionProbability N (L+k) n) :
    0 < infiniteRademacherMeasure.real (C ∩ {omega | infiniteDyadicStartCount N (L+k) omega=n}) ∧
    measureTotalVariation (resolvedRetainedLaw N L k n C)
      (resolvedPastFutureMeasure (fullRate N L) k n) ≤ ε / resolutionProbability N (L+k) n := by
  let μ := (cond infiniteRademacherMeasure C).map (unsignedAggregateSource N L)
  let ν := configurationMeasure (fullRate N L)
  let B : Set (ℕ →₀ ℕ) := {c | tailCount c k=n}
  letI instProbabilityLocal1 : IsProbabilityMeasure (cond infiniteRademacherMeasure C) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hpos)
  letI instProbabilityLocal2 : IsProbabilityMeasure μ :=
    Measure.isProbabilityMeasure_map (measurable_unsignedAggregateSource N L).aemeasurable
  have hprob : ν.real B = resolutionProbability N (L+k) n := target_resolution_probability _ _ _ _
  have hε' : ε < ν.real B := by rwa [hprob]
  obtain ⟨hq, hb, hb'⟩ := lemma_six_two μ ν B ((Set.to_countable _).measurableSet)
    (by simpa only [μ,ν,conditioned_configuration_distance N L C hpos] using htv) hε'
  have hevent : μ.real B = (cond infiniteRademacherMeasure C).real
      {omega | infiniteDyadicStartCount N (L+k) omega=n} := by
    dsimp only [μ]
    rw [Measure.real, Measure.map_apply (measurable_unsignedAggregateSource N L)
      ((Set.to_countable _).measurableSet)]
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [ae_future_eq_configuration hN
      (μ := cond infiniteRademacherMeasure C) cond_absolutelyContinuous] with omega h
    have hk := congrFun h k
    change (tailCount (unsignedAggregateSource N L omega) k=n) = (infiniteDyadicStartCount N (L+k) omega=n)
    rw [show infiniteDyadicStartCount N (L+k) omega=tailCount (unsignedAggregateSource N L omega) k from hk]
  have hresolved : 0 < infiniteRademacherMeasure.real
      (C ∩ {omega | infiniteDyadicStartCount N (L+k) omega=n}) := by
    rw [hevent, SharpConditioning.cond_real_apply _ C hC] at hq
    exact (div_pos_iff.mp hq).resolve_right (by intro h; linarith [hpos]) |>.1
  refine ⟨hresolved, ?_⟩
  have hp : 0 < ν.real B := by rw [hprob]; exact resolutionProbability_pos (by omega) (L+k) n
  letI instProbabilityLocal3 : IsProbabilityMeasure (cond μ B) := cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hq)
  letI instProbabilityLocal4 : IsProbabilityMeasure (cond ν B) := cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hp)
  have hm := (measureTotalVariation_map_le (cond μ B) (cond ν B)
    (measurable_of_countable thresholdFunction)).trans (hb.trans hb')
  have hn : (poissonMeasure (fullRate N L / 2^k)) {n} ≠ 0 := by
    rw [fullRate_add]
    apply measure_ne_zero_of_real_pos _ (poissonMeasure_real_singleton_pos n _)
    change 0 < (N : ℝ)/2^(L+k)
    exact div_pos (Nat.cast_pos.mpr (by omega)) (by positivity)
  rw [← resolvedRetainedLaw_eq_configuration hN k n C hC,
    conditional_retained_path_eq _ k n hn, hprob] at hm
  exact hm

end
end PaperC.V282.PoissonResolvedLowerComparison
