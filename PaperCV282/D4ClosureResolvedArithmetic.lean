import PaperCV282.D4ClosureResolutionTransfer
import PaperCV282.D4ClosureResolvedGrid
import PaperCV282.CountableExpectationTransfer

/-! # The actual fixed-count arithmetic law converges to iid spatial marks

Only the last grid-to-continuum step is weak. The preceding conditioning
comparison is total variation, with the actual positive Poisson atom.
-/
namespace PaperC.V282.D4ClosureResolvedArithmetic

open MeasureTheory ProbabilityTheory Filter
open D4ClosureResolutionTransfer D4ClosureSpatialResolution D4ClosureResolvedGrid
open CountableExpectationTransfer SharpConditioning SharpConditioningDiscrete
open SpatialMarkedTypes SpatialMarkedSource SpatialMarkedTarget SpatialMarkedTargetAggregation
open SpatialPointEmbedding PointMeasureSpace AllStartSoftPoisson
open InfiniteRademacher InfiniteCylinderTransfer ProcessAGGInput PrimeEulerPNT
open HardPoissonRates RareConditioningRates SaddleParameters SaddleScales
open ConditionedCountableLaw
open scoped Topology BoundedContinuousFunction NNReal

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

theorem resolved_integral_error_le (N L n : ℕ) (hN : 0 < N) (A : Set InfiniteSample)
    (hA : 0 < infiniteRademacherMeasure.real A)
    (hp : 0 < (arithmeticSpatialMeasure N L A).real {v | totalSpatialCount N v=n})
    (F : PointMeasure (ℝ × (ℕ × F₂)) →ᵇ ℝ) :
    |(∫ v, F (spatialPointEmbedding N v) ∂resolvedArithmeticSpatialMeasure N L n A)-
      (∫ x, F x ∂(resolvedPointLaw N hN n : Measure _))| ≤
      2*‖F‖*measureTotalVariation (resolvedArithmeticSpatialMeasure N L n A)
        (cond (spatialTargetMeasure N L) {v | totalSpatialCount N v=n}) := by
  letI instProbabilityConditional : IsProbabilityMeasure (cond infiniteRademacherMeasure A) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hA)
  letI instProbabilitySpatial : IsProbabilityMeasure (arithmeticSpatialMeasure N L A) :=
    Measure.isProbabilityMeasure_map (measurable_spatialMarkedSource _ _).aemeasurable
  letI instProbabilityResolved : IsProbabilityMeasure (resolvedArithmeticSpatialMeasure N L n A) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hp)
  have hn : (poissonMeasure (fullRate N L)) {n}≠0 := by
    apply measure_ne_zero_of_real_pos
    rw [poissonMeasure_real_singleton]
    have hr : 0 < (fullRate N L : ℝ) := by
      change 0 < (N : ℝ)/(2 : ℝ)^L
      positivity
    positivity
  rw [conditional_spatial_eq_resolved N L hN n hn,measureTotalVariation_eq_mass]
  have he : (∫ x, F x ∂(resolvedPointLaw N hN n : Measure _))=
      ∫ v, F (spatialPointEmbedding N v) ∂resolvedSpatialMeasure N hN n :=
    integral_map (measurable_spatialPointEmbedding N).aemeasurable
      F.continuous.measurable.aestronglyMeasurable
  rw [he]
  exact integral_difference_le_tv (resolvedArithmeticSpatialMeasure N L n A)
    (resolvedSpatialMeasure N hN n) measurable_id measurable_id
    (fun v => F (spatialPointEmbedding N v)) ‖F‖
    (fun v => by simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm (spatialPointEmbedding N v))

/-- The genuine arithmetic configuration, conditioned by its complete count n,
converges weakly to exactly n independent uniform/geometric/sign marks.
The conclusion is the defining bounded-continuous-test form of weak convergence. -/
theorem companion_D4_resolved_arithmetic_weak
    (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop)
    (lo hi K c : ℝ) (hlo : 0 < lo) (hhi : lo < hi) (hc : 0 < c)
    (A : ℕ → Set InfiniteSample) (rate : ℝ≥0) (hrate : 0 < rate) (n : ℕ)
    (hrates : Tendsto (fun k => (fullRate (sizes k) (lengths k) : ℝ)) atTop (𝓝 (rate : ℝ)))
    (hband : ∀ᶠ k in atTop, lo*Real.log (sizes k)≤(lengths k+1 : ℝ) ∧
      (lengths k+1 : ℝ)≤hi*Real.log (sizes k))
    (hK : ∀ᶠ k in atTop, (fullRate (sizes k) (lengths k) : ℝ)≤K)
    (hA : ∀ᶠ k in atTop, MeasurableSet[MeasurableSpace.comap
      (restrictToFinite (hardCutoff (sizes k))) inferInstance] (A k))
    (hpos : ∀ᶠ k in atTop, 0 < infiniteRademacherMeasure.real (A k))
    (hbudget : ∀ᶠ k in atTop, eventInformation (A k)≤
      saddleCutoff 1 (Real.log (sizes k))-c*saddleNu 1 (Real.log (sizes k)))
    (F : PointMeasure (ℝ × (ℕ × F₂)) →ᵇ ℝ) :
    Tendsto (fun k => ∫ v, F (spatialPointEmbedding (sizes k) v)
      ∂resolvedArithmeticSpatialMeasure (sizes k) (lengths k) n (A k)) atTop
      (𝓝 (∫ x, F x ∂(resolvedDiffuseLaw n : Measure _))) := by
  obtain ⟨hp,htv⟩ := arithmetic_spatial_resolution_tendsto_zero hAGG hPNT sizes lengths hsizes
    lo hi K c hlo hhi hc A rate hrate n hrates hband hK hA hpos hbudget
  let sizes' : ℕ → ℕ := fun k => max 1 (sizes k)
  have hN : ∀ k, 0 < sizes' k := fun k => lt_of_lt_of_le (by omega) (le_max_left _ _)
  have hs : Tendsto sizes' atTop atTop := tendsto_atTop_mono (fun k => le_max_right _ _) hsizes
  have htarget := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (resolvedPointLaw_tendsto sizes' hN hs n) F
  have hdiff : Tendsto (fun k =>
      (∫ v, F (spatialPointEmbedding (sizes k) v)
        ∂resolvedArithmeticSpatialMeasure (sizes k) (lengths k) n (A k))-
      (∫ x, F x ∂(resolvedPointLaw (sizes' k) (hN k) n : Measure _))) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (by simpa only [mul_zero] using htv.const_mul (2*‖F‖))
    filter_upwards [hsizes.eventually_ge_atTop 1,hpos,hp] with k hk ha hn
    have hnN : 0 < sizes k := by omega
    have he : resolvedPointLaw (sizes' k) (hN k) n=resolvedPointLaw (sizes k) hnN n := by
      congr 1
      exact max_eq_right hk
    rw [he]
    exact resolved_integral_error_le _ _ n hnN _ ha hn F
  simpa only [sub_add_cancel,zero_add] using hdiff.add htarget

end
end PaperC.V282.D4ClosureResolvedArithmetic
