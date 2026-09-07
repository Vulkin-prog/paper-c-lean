import PaperCV282.PoissonResolvedTarget
import PaperCV282.SpatialDiffuseMarks
import PaperCV282.SpatialMarkedTargetAggregation

/-! # Fixed-count resolution of the complete spatial target

The conditional configuration is constructed from exactly n independent
marks. Each mark has a uniform grid position, an independent geometric
excess, and an independent fair sign. All excesses are retained.
-/
namespace PaperC.V282.D4ClosureSpatialResolution

open MeasureTheory ProbabilityTheory
open SpatialMarkedTypes SpatialMarkedTarget SpatialMarkedTargetAggregation
open SpatialMarkedPoissonIdentification SpatialDiffuseMarks GeneralPoissonMarking
open PoissonResolvedTarget ConditionalStartProbability AllStartSoftPoisson ConditionedCountableLaw SharpConditioningDiscrete
open scoped BigOperators NNReal ENNReal

noncomputable section

theorem totalSpatialCount_sampledConfiguration {X : Type*} (N : ℕ)
    (mark : X → SpatialMarkedIndex N) (sample : ℕ × (ℕ → X)) :
    totalSpatialCount N (sampledConfiguration N mark sample) = sample.1 := by
  classical
  unfold totalSpatialCount sampledConfiguration
  rw [← Finsupp.sum_finsetSum_index]
  · simp [Finsupp.sum_single_index]
  · intro j
    rfl
  · intro j n k
    rfl

def resolvedSpatialMeasure (N : ℕ) (hN : 0 < N) (n : ℕ) : Measure (SpatialMarkedConfig N) :=
  (markSequenceMeasure spatialMarkMeasure).map
    (fun marks => sampledConfiguration N (gridMark N hN) (n, marks))

theorem measurable_fixedSpatialConfiguration (N : ℕ) (hN : 0 < N) (n : ℕ) :
    Measurable (fun marks => sampledConfiguration N (gridMark N hN) (n, marks)) :=
  (measurable_sampledConfiguration N _ (measurable_gridMark N hN)).comp measurable_prodMk_left

instance instProbabilityResolvedSpatial (N : ℕ) (hN : 0 < N) (n : ℕ) :
    IsProbabilityMeasure (resolvedSpatialMeasure N hN n) :=
  Measure.isProbabilityMeasure_map (measurable_fixedSpatialConfiguration N hN n).aemeasurable

/-- Spatial resolution, with iid marks proved by the actual product construction. -/
theorem conditional_spatial_eq_resolved (N L : ℕ) (hN : 0 < N) (n : ℕ)
    (hn : (poissonMeasure (fullRate N L)) {n} ≠ 0) :
    cond (spatialTargetMeasure N L) {c | totalSpatialCount N c = n} =
      resolvedSpatialMeasure N hN n := by
  have hlaw := hasLaw_grid_configuration N L hN
  rw [← hlaw.map_eq, ← map_cond_eq _
    (measurable_sampledConfiguration N _ (measurable_gridMark N hN)) _
      ((Set.to_countable _).measurableSet)]
  have heq : (sampledConfiguration N (gridMark N hN)) ⁻¹'
      {c | totalSpatialCount N c = n} = Prod.fst ⁻¹' {n} := by
    ext sample
    simp only [Set.mem_preimage, Set.mem_setOf_eq, totalSpatialCount_sampledConfiguration,
      Set.mem_singleton_iff]
  rw [heq, markSampleMeasure, cond_prod_first_eq _ _ n hn, Measure.dirac_prod,
    Measure.map_map (measurable_sampledConfiguration N _ (measurable_gridMark N hN))
      measurable_prodMk_left]
  rfl

theorem spatial_resolution_probability (N L n : ℕ) :
    (spatialTargetMeasure N L).real {c | totalSpatialCount N c = n} =
      Real.exp (-(fullRate N L : ℝ)) * (fullRate N L : ℝ)^n / n.factorial :=
  ((hasLaw_totalSpatialCount N L).measureReal_eq (measurableSet_singleton n)).trans
    (poissonMeasure_real_singleton (fullRate N L) n)

/-- The fixed-count target has exactly n points, including multiplicities. -/
theorem resolvedSpatial_count (N : ℕ) (hN : 0 < N) (n : ℕ) :
    ∀ᵐ c ∂resolvedSpatialMeasure N hN n, totalSpatialCount N c = n := by
  rw [resolvedSpatialMeasure]
  apply (ae_map_iff (measurable_fixedSpatialConfiguration N hN n).aemeasurable
    ((Set.to_countable _).measurableSet)).2
  exact Filter.Eventually.of_forall fun marks => totalSpatialCount_sampledConfiguration _ _ _

end
end PaperC.V282.D4ClosureSpatialResolution
