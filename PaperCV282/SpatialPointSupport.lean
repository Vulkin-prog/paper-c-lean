import PaperCV282.SpatialPointConvergence

/-! # The actual point measures put zero mass outside [1,2]

These are equalities of measures evaluated on the complement of the spatial
strip, for every discrete configuration and every diffuse Poisson sample.
They are stronger than merely locating a typical individual mark.
-/
namespace PaperC.V282.SpatialPointSupport

open MeasureTheory ProbabilityTheory PointMeasureSpace SpatialPointEmbedding
open SpatialDiffuseMarks PoissonPointProcess SpatialMarkedTypes
open scoped BigOperators

noncomputable section

def underlyingMeasure {X : Type*} [MeasurableSpace X] : PointMeasure X →+ Measure X :=
  FiniteMeasure.toMeasureAddMonoidHom

theorem underlying_pointDirac {X : Type*} [MeasurableSpace X] (x : X) :
    underlyingMeasure (pointDirac x) = Measure.dirac x := rfl

theorem underlying_fixedPointMeasure_apply_zero {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (n : ℕ) (marks : ℕ → X) (S : Set X) (h : ∀ i, marks i ∉ S) :
    underlyingMeasure (fixedPointMeasure n marks) S = 0 := by
  classical
  simp only [fixedPointMeasure, map_sum, underlying_pointDirac,
    Measure.coe_finsetSum, Finset.sum_apply]
  exact Finset.sum_eq_zero (fun i hi => by simp only [Measure.dirac_apply, Set.indicator_of_notMem (h i)])

def spatialStrip : Set (ℝ × (ℕ × F₂)) := Prod.fst ⁻¹' Set.Icc (1 : ℝ) 2

theorem spatialPointEmbedding_outside_strip_zero (N : ℕ) (config : SpatialMarkedConfig N) :
    underlyingMeasure (spatialPointEmbedding N config) spatialStripᶜ = 0 := by
  classical
  unfold spatialPointEmbedding Finsupp.sum
  simp only [map_sum, map_nsmul, underlying_pointDirac,
    Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  have hjnot : spatialPosition N j ∉ spatialStripᶜ := fun h => h (spatialPosition_mem_interval N j)
  rw [Measure.smul_apply, Measure.dirac_apply, Set.indicator_of_notMem hjnot]
  simp only [smul_zero]

theorem diffuse_sample_outside_strip_zero (sample : ℕ × (ℕ → unitInterval × (ℕ × F₂))) :
    underlyingMeasure (mappedPointMeasure continuousMark sample) spatialStripᶜ = 0 := by
  apply underlying_fixedPointMeasure_apply_zero
  intro i hi
  exact hi (continuousMark_position_mem (sample.2 i))

end
end PaperC.V282.SpatialPointSupport
