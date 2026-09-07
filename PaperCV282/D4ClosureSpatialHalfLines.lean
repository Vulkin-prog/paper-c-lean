import PaperCV282.D4ClosurePointLaws
import PaperCV282.SpatialPointEmbedding

/-! # Finite point configurations on every upper half-line

The coordinates are the genuine rows of the two-sided process, recovered
as a finite-support count configuration on its probability-one domain.
-/
namespace PaperC.V282.D4ClosureSpatialHalfLines

open MeasureTheory ProbabilityTheory Filter
open D4ClosurePointMeasure D4ClosurePointLaws D4ClosureIntegerLevels D4ClosureHalfLines
open PointMeasureSpace SpatialDiffuseMarks UniformSpatialGrid
open scoped BigOperators Topology

noncomputable section

def spatialHalfCounts (m : ℤ) (sample : IntegerSpatialSample) : ℕ →₀ ℕ :=
  halfLineConfiguration m (fun r => (sample r).1)

theorem measurable_spatialHalfCounts (m : ℤ) : Measurable (spatialHalfCounts m) :=
  (measurable_halfLineConfiguration m).comp
    (measurable_pi_lambda _ (fun r => measurable_fst.comp (measurable_pi_apply r)))

def pointsFromCounts (m : ℤ) (c : ℕ →₀ ℕ) (sample : IntegerSpatialSample) :
    PointMeasure (ℝ × (ℕ × F₂)) :=
  c.sum (fun e n => fixedPointMeasure n
    (fun i => (1+((sample (m+e)).2 i : ℝ), (e, (0 : F₂)))))

theorem continuous_pointsArray (c : ℕ →₀ ℕ) :
    Continuous (fun p : ℕ → ℕ → ℝ =>
      c.sum (fun e n => fixedPointMeasure n (fun i => (p e i, (e, (0 : F₂)))))) := by
  classical
  apply continuous_finsetSum
  intro e he
  apply (continuous_fixedPointMeasure (c e)).comp
  apply continuous_pi
  intro i
  exact ((continuous_apply i).comp (continuous_apply e)).prodMk continuous_const

theorem measurable_pointsArray (c : ℕ →₀ ℕ) :
    Measurable (fun p : ℕ → ℕ → ℝ =>
      c.sum (fun e n => fixedPointMeasure n (fun i => (p e i, (e, (0 : F₂)))))) :=
  (continuous_pointsArray c).measurable

theorem measurable_pointsFromCounts (m : ℤ) (c : ℕ →₀ ℕ) : Measurable (pointsFromCounts m c) := by
  apply (measurable_pointsArray c).comp
  apply measurable_pi_lambda
  intro e
  apply measurable_pi_lambda
  intro i
  exact measurable_const.add (measurable_subtype_coe.comp
    ((measurable_pi_apply i).comp (measurable_snd.comp (measurable_pi_apply (m+e)))))

def halfLinePointConfiguration (m : ℤ) (sample : IntegerSpatialSample) :
    PointMeasure (ℝ × (ℕ × F₂)) := pointsFromCounts m (spatialHalfCounts m sample) sample

theorem measurable_halfLinePointConfiguration (m : ℤ) : Measurable (halfLinePointConfiguration m) := by
  have hf : Measurable (fun p : (ℕ →₀ ℕ) × IntegerSpatialSample => pointsFromCounts m p.1 p.2) :=
    measurable_from_prod_countable_right (fun c => measurable_pointsFromCounts m c)
  have hh := hf.comp ((measurable_spatialHalfCounts m).prodMk measurable_id)
  change Measurable (halfLinePointConfiguration m) at hh
  exact hh

def halfLinePointLaw (theta : ℝ) (m : ℤ) : ProbabilityMeasure (PointMeasure (ℝ × (ℕ × F₂))) :=
  ⟨(integerSpatialSampleMeasure theta).map (halfLinePointConfiguration m),
    Measure.isProbabilityMeasure_map (measurable_halfLinePointConfiguration m).aemeasurable⟩

def gridPointsFromCounts (N : ℕ) (hN : 0<N) (m : ℤ) (c : ℕ →₀ ℕ)
    (sample : IntegerSpatialSample) : PointMeasure (ℝ × (ℕ × F₂)) :=
  c.sum (fun e n => fixedPointMeasure n
    (fun i => (1+(gridSite N hN ((sample (m+e)).2 i)).val / (N : ℝ), (e, (0 : F₂)))))

def halfLineGridPoints (N : ℕ) (hN : 0<N) (m : ℤ) (sample : IntegerSpatialSample) :
    PointMeasure (ℝ × (ℕ × F₂)) := gridPointsFromCounts N hN m (spatialHalfCounts m sample) sample

theorem measurable_gridPointsFromCounts (N : ℕ) (hN : 0<N) (m : ℤ) (c : ℕ →₀ ℕ) :
    Measurable (gridPointsFromCounts N hN m c) := by
  apply (measurable_pointsArray c).comp
  apply measurable_pi_lambda
  intro e
  apply measurable_pi_lambda
  intro i
  apply (measurable_of_countable (fun site : Fin N =>
    1+(site.val : ℝ)/(N : ℝ))).comp
  exact (measurable_gridSite N hN).comp
    ((measurable_pi_apply i).comp (measurable_snd.comp (measurable_pi_apply (m+e))))

theorem measurable_halfLineGridPoints (N : ℕ) (hN : 0<N) (m : ℤ) :
    Measurable (halfLineGridPoints N hN m) := by
  have hf : Measurable (fun p : (ℕ →₀ ℕ) × IntegerSpatialSample => gridPointsFromCounts N hN m p.1 p.2) :=
    measurable_from_prod_countable_right (fun c => measurable_gridPointsFromCounts N hN m c)
  have hh := hf.comp ((measurable_spatialHalfCounts m).prodMk measurable_id)
  change Measurable (halfLineGridPoints N hN m) at hh
  exact hh

/-- Every configuration in this construction consists of finitely many points,
so simultaneous convergence of their quantized positions suffices. -/
theorem halfLineGridPoints_tendsto (sizes : ℕ → ℕ) (hN : ∀ k, 0<sizes k)
    (hsizes : Tendsto sizes atTop atTop) (m : ℤ) (sample : IntegerSpatialSample) :
    Tendsto (fun k => halfLineGridPoints (sizes k) (hN k) m sample) atTop
      (𝓝 (halfLinePointConfiguration m sample)) := by
  classical
  unfold halfLineGridPoints halfLinePointConfiguration gridPointsFromCounts pointsFromCounts Finsupp.sum
  apply tendsto_finsetSum
  intro e he
  apply (continuous_fixedPointMeasure _).continuousAt.tendsto.comp
  apply tendsto_pi_nhds.mpr
  intro i
  exact (physical_grid_position_tendsto sizes hN hsizes ((sample (m+e)).2 i)).prodMk_nhds tendsto_const_nhds

end
end PaperC.V282.D4ClosureSpatialHalfLines
