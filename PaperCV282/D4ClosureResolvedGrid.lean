import PaperCV282.D4ClosureSpatialResolution
import PaperCV282.SpatialPointConvergence

/-! # Fixed-count grid positions converge weakly to iid uniform positions

The discrete spatial resolution is exact. Only this subsequent replacement
of its grid by the unit interval uses weak convergence.
-/
namespace PaperC.V282.D4ClosureResolvedGrid

open MeasureTheory ProbabilityTheory Filter
open D4ClosureSpatialResolution SpatialMarkedTypes SpatialDiffuseMarks
open SpatialPointEmbedding PointMeasureSpace PoissonPointProcess GeneralPoissonMarking
open UniformSpatialGrid
open scoped Topology BoundedContinuousFunction

noncomputable section

def resolvedPointLaw (N : ℕ) (hN : 0 < N) (n : ℕ) :
    ProbabilityMeasure (PointMeasure (ℝ × (ℕ × F₂))) :=
  ⟨(resolvedSpatialMeasure N hN n).map (spatialPointEmbedding N),
    Measure.isProbabilityMeasure_map (measurable_spatialPointEmbedding N).aemeasurable⟩

theorem measurable_fixedContinuous (n : ℕ) :
    Measurable (fun marks : ℕ → unitInterval × (ℕ × F₂) =>
      fixedPointMeasure n (fun i => continuousMark (marks i))) :=
  (continuous_fixedPointMeasure n).measurable.comp
    (measurable_pi_lambda _ (fun i => measurable_continuousMark.comp (measurable_pi_apply i)))

theorem measurable_fixedGrid (N : ℕ) (hN : 0<N) (n : ℕ) :
    Measurable (fun marks : ℕ → unitInterval × (ℕ × F₂) =>
      fixedPointMeasure n (fun i => gridPhysicalMark N hN (marks i))) :=
  (continuous_fixedPointMeasure n).measurable.comp
    (measurable_pi_lambda _ (fun i => (measurable_gridPhysicalMark N hN).comp (measurable_pi_apply i)))

set_option maxHeartbeats 1000000 in
def resolvedDiffuseLaw (n : ℕ) : ProbabilityMeasure (PointMeasure (ℝ × (ℕ × F₂))) :=
  ⟨(markSequenceMeasure spatialMarkMeasure).map
    (fun marks : ℕ → unitInterval × (ℕ × F₂) => fixedPointMeasure n (fun i => continuousMark (marks i))),
    Measure.isProbabilityMeasure_map (measurable_fixedContinuous n).aemeasurable⟩

theorem resolvedPointLaw_eq (N : ℕ) (hN : 0 < N) (n : ℕ) :
    (resolvedPointLaw N hN n : Measure (PointMeasure (ℝ × (ℕ × F₂)))) =
      (markSequenceMeasure spatialMarkMeasure).map
        (fun marks => fixedPointMeasure n (fun i => gridPhysicalMark N hN (marks i))) := by
  change ((markSequenceMeasure spatialMarkMeasure).map
    (fun marks => SpatialMarkedPoissonIdentification.sampledConfiguration N (gridMark N hN) (n, marks))).map
      (spatialPointEmbedding N) = _
  rw [Measure.map_map (measurable_spatialPointEmbedding N)
    (measurable_fixedSpatialConfiguration N hN n)]
  congr 1
  funext marks
  exact spatialPointEmbedding_sampledConfiguration N (gridMark N hN) (n, marks)

/-- n fixed iid grid positions, carrying all geometric excesses and signs,
converge to their n fixed iid continuum counterparts. -/
theorem resolvedPointLaw_tendsto (sizes : ℕ → ℕ) (hN : ∀ k, 0 < sizes k)
    (hsizes : Tendsto sizes atTop atTop) (n : ℕ) :
    Tendsto (fun k => resolvedPointLaw (sizes k) (hN k) n) atTop (𝓝 (resolvedDiffuseLaw n)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have hmarks (x : unitInterval × (ℕ × F₂)) :
      Tendsto (fun k => gridPhysicalMark (sizes k) (hN k) x) atTop (𝓝 (continuousMark x)) := by
    exact (physical_grid_position_tendsto sizes hN hsizes x.1).prodMk_nhds tendsto_const_nhds
  have h := fixed_point_integral_tendsto spatialMarkMeasure
    (fun k => gridPhysicalMark (sizes k) (hN k)) continuousMark
    (fun k => measurable_gridPhysicalMark (sizes k) (hN k)) hmarks f n
  have hg (k : ℕ) :
      (∫ x, f x ∂(resolvedPointLaw (sizes k) (hN k) n : Measure _)) =
      ∫ marks, f (fixedPointMeasure n (fun i => gridPhysicalMark (sizes k) (hN k) (marks i)))
        ∂markSequenceMeasure spatialMarkMeasure := by
    rw [resolvedPointLaw_eq, integral_map (measurable_fixedGrid _ _ _).aemeasurable
      f.continuous.measurable.aestronglyMeasurable]
  have hd : (∫ x, f x ∂(resolvedDiffuseLaw n : Measure _)) =
      ∫ marks, f (fixedPointMeasure n (fun i => continuousMark (marks i)))
        ∂markSequenceMeasure spatialMarkMeasure := by
    exact integral_map (measurable_fixedContinuous n).aemeasurable
      f.continuous.measurable.aestronglyMeasurable
  simp_rw [hg, hd]
  exact h

end
end PaperC.V282.D4ClosureResolvedGrid
