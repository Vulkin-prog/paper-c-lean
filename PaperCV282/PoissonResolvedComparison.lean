import PaperCV282.PoissonResolvedTarget
import PaperCV282.UnsignedAggregateComparison
import PaperCV282.PoissonGaussianSource

/-! # Resolving the actual present count controls the entire future at once -/
namespace PaperC.V282.PoissonResolvedComparison

open MeasureTheory ProbabilityTheory SharpConditioning SharpConditioningDiscrete
open PoissonResolvedTarget GeometricMarkedConfiguration GeometricConfigurationCounts
open UnsignedAggregateComparison InfiniteMassCoupling ConditionedCountableLaw
open FiniteFieldTotalVariation InfiniteRademacher InfiniteCylinderTransfer
open InfiniteStartProbabilityTransfer MovingMarkedSource ThresholdPathEquivalence
open PoissonGaussianSource AllStartSoftPoisson
open scoped NNReal

noncomputable section

local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

def actualFuturePath (N L : ℕ) (omega : InfiniteSample) (j : ℕ) : ℕ :=
  infiniteDyadicStartCount N (L+j) omega

theorem measurable_actualFuturePath (N L : ℕ) : Measurable (actualFuturePath N L) :=
  measurable_pi_lambda _ (fun j => measurable_source_startCount N (L+j))

theorem ae_future_eq_configuration {N L : ℕ} (hN : 2 ≤ N)
    {μ : Measure InfiniteSample} (hμ : μ ≪ infiniteRademacherMeasure) :
    actualFuturePath N L =ᵐ[μ] thresholdFunction ∘ unsignedAggregateSource N L := by
  filter_upwards [ae_source_thresholds_eq_startCounts_of_ac hN hμ] with omega h
  exact funext (fun j => (h j).symm)

theorem configurationSize_eq_threshold_zero (c : ℕ →₀ ℕ) :
    configurationSize c = thresholdFunction c 0 := by
  simp [configurationSize, thresholdFunction, tailCount, Finsupp.sum]

theorem ae_present_eq_configuration {N L : ℕ} (hN : 2 ≤ N)
    {μ : Measure InfiniteSample} (hμ : μ ≪ infiniteRademacherMeasure) :
    infiniteDyadicStartCount N L =ᵐ[μ] configurationSize ∘ unsignedAggregateSource N L := by
  filter_upwards [ae_future_eq_configuration hN hμ] with omega h
  have h0 := congrFun h 0
  simpa [actualFuturePath, configurationSize_eq_threshold_zero] using h0

/-- The source condition is the genuine intersection with the observed present count. -/
def resolvedFutureLaw (N L n : ℕ) (C : Set InfiniteSample) : Measure (ℕ → ℕ) :=
  (cond infiniteRademacherMeasure (C ∩ {omega | infiniteDyadicStartCount N L omega=n})).map
    (actualFuturePath N L)

def resolutionProbability (N L n : ℕ) : ℝ :=
  Real.exp (-(fullRate N L : ℝ)) * (fullRate N L : ℝ)^n / n.factorial

theorem resolutionProbability_pos {N : ℕ} (hN : 0 < N) (L n : ℕ) :
    0 < resolutionProbability N L n := by
  have hr : 0 < (fullRate N L : ℝ) := by exact div_pos (Nat.cast_pos.mpr hN) (by positivity)
  unfold resolutionProbability
  positivity

theorem conditioned_configuration_distance (N L : ℕ) (C : Set InfiniteSample)
    (hC : 0 < infiniteRademacherMeasure.real C) :
    measureTotalVariation ((cond infiniteRademacherMeasure C).map (unsignedAggregateSource N L))
      (configurationMeasure (fullRate N L)) = conditionalUnsignedAggregateDistance N L C := by
  letI instProbabilityLocal1 : IsProbabilityMeasure (cond infiniteRademacherMeasure C) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hC)
  letI instProbabilityLocal2 : IsProbabilityMeasure ((cond infiniteRademacherMeasure C).map (unsignedAggregateSource N L)) :=
    Measure.isProbabilityMeasure_map (measurable_unsignedAggregateSource N L).aemeasurable
  rw [measureTotalVariation_eq_mass]
  congr 1
  funext c
  change ((cond infiniteRademacherMeasure C).map (unsignedAggregateSource N L)).real {c} = _
  exact (observableLaw_eq_map _ (measurable_unsignedAggregateSource N L) c).symm

theorem resolvedFutureLaw_eq_configuration {N L : ℕ} (hN : 2 ≤ N)
    (n : ℕ) (C : Set InfiniteSample) (hC : MeasurableSet C) :
    resolvedFutureLaw N L n C =
      (cond ((cond infiniteRademacherMeasure C).map (unsignedAggregateSource N L))
        {c | configurationSize c=n}).map thresholdFunction := by
  have hcount : MeasurableSet {omega | infiniteDyadicStartCount N L omega=n} :=
    (measurable_source_startCount N L) (measurableSet_singleton n)
  have hpred : {omega | infiniteDyadicStartCount N L omega=n} =ᵐ[
      cond infiniteRademacherMeasure C]
      unsignedAggregateSource N L ⁻¹' {c | configurationSize c=n} := by
    filter_upwards [ae_present_eq_configuration hN (μ := cond infiniteRademacherMeasure C) cond_absolutelyContinuous] with omega h
    change (infiniteDyadicStartCount N L omega=n) = (configurationSize (unsignedAggregateSource N L omega)=n)
    rw [h]
    rfl
  unfold resolvedFutureLaw
  rw [← cond_cond_eq_cond_inter hC hcount]
  rw [Measure.map_congr (ae_future_eq_configuration hN
    (cond_absolutelyContinuous.trans cond_absolutelyContinuous))]
  rw [cond_congr_ae _ hpred,
    ← Measure.map_map (measurable_of_countable _) (measurable_unsignedAggregateSource N L),
    map_cond_eq _ (measurable_unsignedAggregateSource N L) _ ((Set.to_countable _).measurableSet)]

/-- Theorem 6.3: the actual full future under C and Z=n, with its exact resolution cost. -/
theorem theorem_six_three_future {N L : ℕ} (hN : 2 ≤ N)
    (n : ℕ) (C : Set InfiniteSample) (hC : MeasurableSet C)
    (hpos : 0 < infiniteRademacherMeasure.real C) {ε : ℝ}
    (htv : conditionalUnsignedAggregateDistance N L C ≤ ε)
    (hε : ε < resolutionProbability N L n) :
    0 < infiniteRademacherMeasure.real (C ∩ {omega | infiniteDyadicStartCount N L omega=n}) ∧
    measureTotalVariation (resolvedFutureLaw N L n C) (thinningPathMeasure n) ≤
      ε / resolutionProbability N L n := by
  let μ := (cond infiniteRademacherMeasure C).map (unsignedAggregateSource N L)
  let ν := configurationMeasure (fullRate N L)
  let B : Set (ℕ →₀ ℕ) := {c | configurationSize c=n}
  letI instProbabilityLocal3 : IsProbabilityMeasure (cond infiniteRademacherMeasure C) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hpos)
  letI instProbabilityLocal4 : IsProbabilityMeasure μ :=
    Measure.isProbabilityMeasure_map (measurable_unsignedAggregateSource N L).aemeasurable
  have hprob : ν.real B = resolutionProbability N L n := configuration_size_probability _ _
  have hε' : ε < ν.real B := by rwa [hprob]
  obtain ⟨hq, hb, hb'⟩ := lemma_six_two μ ν B ((Set.to_countable _).measurableSet)
    (by simpa only [μ,ν,conditioned_configuration_distance N L C hpos] using htv) hε'
  have hevent : μ.real B = (cond infiniteRademacherMeasure C).real
      {omega | infiniteDyadicStartCount N L omega=n} := by
    dsimp only [μ]
    rw [Measure.real, Measure.map_apply (measurable_unsignedAggregateSource N L)
      ((Set.to_countable _).measurableSet)]
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [ae_present_eq_configuration hN cond_absolutelyContinuous] with omega h
    change (configurationSize (unsignedAggregateSource N L omega)=n) = (infiniteDyadicStartCount N L omega=n)
    rw [h]
    rfl
  have hresolved : 0 < infiniteRademacherMeasure.real
      (C ∩ {omega | infiniteDyadicStartCount N L omega=n}) := by
    rw [hevent, SharpConditioning.cond_real_apply _ C hC] at hq
    exact (div_pos_iff.mp hq).resolve_right (by intro h; linarith [hpos]) |>.1
  refine ⟨hresolved, ?_⟩
  have hp : 0 < ν.real B := by rw [hprob]; exact resolutionProbability_pos (by omega) L n
  letI instProbabilityLocal5 : IsProbabilityMeasure (cond μ B) := cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hq)
  letI instProbabilityLocal6 : IsProbabilityMeasure (cond ν B) := cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hp)
  have hm := (measureTotalVariation_map_le (cond μ B) (cond ν B)
    (measurable_of_countable thresholdFunction)).trans (hb.trans hb')
  have hn : (poissonMeasure (fullRate N L)) {n} ≠ 0 :=
    measure_ne_zero_of_real_pos _ (poissonMeasure_real_singleton_pos n (by
      change 0 < (⟨(N : ℝ) / 2^L, _⟩ : ℝ≥0)
      change 0 < (N : ℝ) / 2^L
      positivity))
  rw [← resolvedFutureLaw_eq_configuration hN n C hC,
    conditional_future_path_eq _ n hn, hprob] at hm
  exact hm

end
end PaperC.V282.PoissonResolvedComparison
