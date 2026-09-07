import PaperCV282.D4GridIdentificationConfiguration
import PaperCV282.D4GridIdentificationTarget

/-! # Equality of the complete grid laws from the integer rows and a single marked Poisson sample -/
namespace PaperC.V282.D4GridIdentificationTheorem

open MeasureTheory ProbabilityTheory GeneralPoissonMarking UniformSpatialGrid
open D4ClosurePointMeasure D4ClosurePointLaws D4ClosureIntegerLevels PoissonFieldMeasure
open D4GridIdentificationRows D4GridIdentificationConfiguration D4GridIdentificationTarget
open SpatialMarkedTypes ExactMarkedModel SpatialMarkedLawExt ConditionalStartProbability
open SpatialMarkedPoissonIdentification SpatialMarkedTargetAggregation GeometricConfigurationCounts
open D4ClosureSpatialResolution SharpConditioningDiscrete PoissonResolvedTarget D4ClosureHalfLines
open scoped BigOperators NNReal ENNReal

noncomputable section

theorem hasLaw_gridHalfConfiguration_projection (N : ℕ) (hN : 0<N) (theta : ℝ) (m : ℤ) (E : ℕ) :
    HasLaw (fun sample : IntegerSpatialSample => projectConfiguration N E (gridHalfConfiguration N hN m sample))
      (fieldMeasure (fun i : SignedMarkIndex N E => rowRates N hN
        (integerLevelRate theta (m+(i.2.1.val : ℤ))) ((dyadicSiteEquiv N).symm i.1,i.2.2)))
      (integerSpatialSampleMeasure theta) := by
  apply (hasLaw_finiteSpatialCells N hN theta m E).congr
  filter_upwards [ae_gridHalfConfiguration_coordinates N hN theta m] with sample hs
  funext i
  exact hs (finiteMarkedEmbedding N E i)

/-- The full spatial and exact-level law is identified, including every excess simultaneously. -/
theorem hasLaw_gridHalfConfiguration (N : ℕ) (hN : 0<N) (theta : ℝ) (m : ℤ) :
    HasLaw (gridHalfConfiguration N hN m) (halfGridTarget N hN (integerHalfRate theta m))
      (integerSpatialSampleMeasure theta) := by
  apply hasLaw_of_matching_projection_laws
    (integerSpatialSampleMeasure theta) (halfGridTarget N hN (integerHalfRate theta m))
    (gridHalfConfiguration N hN m) (measurable_gridHalfConfiguration N hN m)
    (fun E => fieldMeasure (fun i : SignedMarkIndex N E => rowRates N hN
      (integerLevelRate theta (m+(i.2.1.val : ℤ))) ((dyadicSiteEquiv N).symm i.1,i.2.2)))
  · exact hasLaw_gridHalfConfiguration_projection N hN theta m
  · exact hasLaw_halfGridTarget_projection N hN theta m

def fixedHalfGridTarget (N : ℕ) (hN : 0<N) (n : ℕ) : Measure (SpatialMarkedConfig N) :=
  (markSequenceMeasure halfMarkMeasure).map
    (fun marks => sampledConfiguration N (halfGridMark N hN) (n,marks))

theorem measurable_fixedHalfGrid (N : ℕ) (hN : 0<N) (n : ℕ) :
    Measurable (fun marks => sampledConfiguration N (halfGridMark N hN) (n,marks)) :=
  (measurable_sampledConfiguration N _ (measurable_halfGridMark N hN)).comp measurable_prodMk_left

instance instProbabilityFixedHalfGrid (N : ℕ) (hN : 0<N) (n : ℕ) :
    IsProbabilityMeasure (fixedHalfGridTarget N hN n) :=
  Measure.isProbabilityMeasure_map (measurable_fixedHalfGrid N hN n).aemeasurable

theorem conditional_halfGridTarget (N : ℕ) (hN : 0<N) (rate : ℝ≥0) (n : ℕ)
    (hn : (poissonMeasure rate) {n}≠0) :
    cond (halfGridTarget N hN rate) {c | totalSpatialCount N c=n}=fixedHalfGridTarget N hN n := by
  rw [halfGridTarget,← map_cond_eq _
    (measurable_sampledConfiguration N _ (measurable_halfGridMark N hN)) _
    ((Set.to_countable _).measurableSet)]
  have he : (sampledConfiguration N (halfGridMark N hN)) ⁻¹'
      {c | totalSpatialCount N c=n}=Prod.fst ⁻¹' {n} := by
    ext sample
    simp only [Set.mem_preimage,Set.mem_setOf_eq,totalSpatialCount_sampledConfiguration,Set.mem_singleton_iff]
  rw [he,markSampleMeasure,cond_prod_first_eq _ _ n hn,Measure.dirac_prod,
    Measure.map_map (measurable_sampledConfiguration N _ (measurable_halfGridMark N hN)) measurable_prodMk_left]
  rfl

/-- Conditioning the true integer-level construction on its complete upper-tail count
leaves exactly n iid grid positions and geometric excesses. -/
theorem conditional_gridHalfConfiguration (N : ℕ) (hN : 0<N) (theta : ℝ) (m : ℤ) (n : ℕ)
    (hn : (poissonMeasure (integerHalfRate theta m)) {n}≠0) :
    (cond (integerSpatialSampleMeasure theta)
      {sample | configurationSize (spatialHalfCounts m sample)=n}).map
      (gridHalfConfiguration N hN m)=fixedHalfGridTarget N hN n := by
  have he : {sample | configurationSize (spatialHalfCounts m sample)=n}=
      (gridHalfConfiguration N hN m) ⁻¹' {c | totalSpatialCount N c=n} := by
    ext sample
    simp only [Set.mem_preimage,Set.mem_setOf_eq,totalSpatialCount_gridHalfConfiguration]
  rw [he,map_cond_eq _ (measurable_gridHalfConfiguration N hN m) _
    ((Set.to_countable _).measurableSet),(hasLaw_gridHalfConfiguration N hN theta m).map_eq,
    conditional_halfGridTarget N hN _ n hn]

theorem hasLaw_spatialHalfCount (theta : ℝ) (m : ℤ) :
    HasLaw (fun sample : IntegerSpatialSample => configurationSize (spatialHalfCounts m sample))
      (poissonMeasure (integerHalfRate theta m)) (integerSpatialSampleMeasure theta) :=
  (hasLaw_integerThreshold theta m).fun_comp (hasLaw_integerSpatialCounts theta)

end
end PaperC.V282.D4GridIdentificationTheorem
