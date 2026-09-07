import PaperCV282.D4GridIdentificationRows
import PaperCV282.D4ClosureSpatialResolution

/-! # A genuine finite-support spatial grid for each upper integer half-line -/
namespace PaperC.V282.D4GridIdentificationConfiguration

open MeasureTheory ProbabilityTheory GeneralPoissonMarking UniformSpatialGrid
open D4ClosurePointMeasure D4ClosurePointLaws D4ClosureIntegerLevels D4ClosureHalfLines
open D4GridIdentificationRows SpatialMarkedTypes SpatialMarkedPoissonIdentification
open SpatialMarkedTargetAggregation GeometricConfigurationCounts D4ClosureSpatialResolution
open scoped BigOperators NNReal ENNReal

noncomputable section

def gridRowsConfiguration (N : ℕ) (hN : 0<N) (c : ℕ→₀ℕ)
    (marks : ℕ→ℕ→unitInterval) : SpatialMarkedConfig N :=
  c.sum (fun e n => sampledConfiguration N (fun u => (gridSite N hN u,(e,0))) (n,marks e))

theorem gridRowsConfiguration_apply (N : ℕ) (hN : 0<N) (c : ℕ→₀ℕ)
    (marks : ℕ→ℕ→unitInterval) (j : SpatialMarkedIndex N) :
    gridRowsConfiguration N hN c marks j=rowCounts N hN (c j.2.1,marks j.2.1) (j.1,j.2.2) := by
  classical
  unfold gridRowsConfiguration
  rw [Finsupp.sum_apply,Finsupp.sum_eq_single j.2.1]
  · simp only [sampledConfiguration,Finsupp.finsetSum_apply,Finsupp.single_apply,
      rowCounts,categoryCounts,rowCategory,Option.some.injEq,Prod.mk.injEq]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    simp only [Prod.ext_iff,true_and]
  · intro e he hne
    simp only [sampledConfiguration,Finsupp.finsetSum_apply,Finsupp.single_apply]
    apply Finset.sum_eq_zero
    intro i hi
    exact if_neg (fun h => hne (congrArg (fun p => p.2.1) h))
  · intro he
    simp [sampledConfiguration]

theorem measurable_gridRowsConfiguration (N : ℕ) (hN : 0<N) :
    Measurable (fun p : (ℕ→₀ℕ) × (ℕ→ℕ→unitInterval) => gridRowsConfiguration N hN p.1 p.2) := by
  apply measurable_from_prod_countable_right
  intro c
  change Measurable (fun marks : ℕ→ℕ→unitInterval => ∑ e ∈ c.support,
    sampledConfiguration N (fun u => (gridSite N hN u,(e,0))) (c e,marks e))
  apply Finset.measurable_sum
  intro e he
  exact (measurable_sampledConfiguration N _
    ((measurable_gridSite N hN).prodMk measurable_const)).comp
      (measurable_const.prodMk (measurable_pi_apply e))

def spatialHalfCounts (m : ℤ) (sample : IntegerSpatialSample) : ℕ→₀ℕ :=
  halfLineConfiguration m (fun r => (sample r).1)

theorem measurable_spatialHalfCounts (m : ℤ) : Measurable (spatialHalfCounts m) :=
  (measurable_halfLineConfiguration m).comp
    (measurable_pi_lambda _ (fun r => measurable_fst.comp (measurable_pi_apply r)))

def gridHalfConfiguration (N : ℕ) (hN : 0<N) (m : ℤ) (sample : IntegerSpatialSample) :
    SpatialMarkedConfig N :=
  gridRowsConfiguration N hN (spatialHalfCounts m sample) (fun e => (sample (m+e)).2)

theorem measurable_gridHalfConfiguration (N : ℕ) (hN : 0<N) (m : ℤ) :
    Measurable (gridHalfConfiguration N hN m) := by
  have hm : Measurable (fun sample : IntegerSpatialSample => fun e : ℕ => (sample (m+e)).2) :=
    measurable_pi_lambda _ (fun e => measurable_snd.comp (measurable_pi_apply (m+e)))
  have hp := (measurable_spatialHalfCounts m).prodMk hm
  have hh := (measurable_gridRowsConfiguration N hN).comp hp
  change Measurable (gridHalfConfiguration N hN m) at hh
  exact hh

theorem ae_spatialHalfCounts_coordinates (theta : ℝ) (m : ℤ) :
    ∀ᵐ sample ∂integerSpatialSampleMeasure theta,
      ∀ e : ℕ, spatialHalfCounts m sample e=(sample (m+e)).1 := by
  have h := ae_halfLineConfiguration_coordinates theta m
  have hm : MeasurableSet {counts : ℤ→ℕ | ∀ e : ℕ, halfLineConfiguration m counts e=counts (m+e)} := by
    rw [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro e
    exact measurableSet_eq_fun
      ((measurable_of_countable (fun c : ℕ→₀ℕ => c e)).comp (measurable_halfLineConfiguration m))
      (measurable_pi_apply (m+e))
  rw [← (hasLaw_integerSpatialCounts theta).map_eq] at h
  exact (ae_map_iff (hasLaw_integerSpatialCounts theta).aemeasurable hm).1 h

theorem ae_gridHalfConfiguration_coordinates (N : ℕ) (hN : 0<N) (theta : ℝ) (m : ℤ) :
    ∀ᵐ sample ∂integerSpatialSampleMeasure theta,
      ∀ j : SpatialMarkedIndex N,
        gridHalfConfiguration N hN m sample j=rowCounts N hN (sample (m+j.2.1)) (j.1,j.2.2) := by
  filter_upwards [ae_spatialHalfCounts_coordinates theta m] with sample hs
  intro j
  rw [gridHalfConfiguration,gridRowsConfiguration_apply,hs]

/-- The complete spatial grid has the same total count as the complete upper-level configuration. -/
theorem totalSpatialCount_gridRowsConfiguration (N : ℕ) (hN : 0<N) (c : ℕ→₀ℕ)
    (marks : ℕ→ℕ→unitInterval) :
    totalSpatialCount N (gridRowsConfiguration N hN c marks)=configurationSize c := by
  classical
  unfold totalSpatialCount gridRowsConfiguration
  rw [Finsupp.sum_sum_index]
  · unfold configurationSize
    apply Finsupp.sum_congr
    intro e he
    exact totalSpatialCount_sampledConfiguration N _ _
  · intro j
    rfl
  · intro j a b
    rfl

theorem totalSpatialCount_gridHalfConfiguration (N : ℕ) (hN : 0<N) (m : ℤ) (sample : IntegerSpatialSample) :
    totalSpatialCount N (gridHalfConfiguration N hN m sample)=configurationSize (spatialHalfCounts m sample) :=
  totalSpatialCount_gridRowsConfiguration N hN _ _

end
end PaperC.V282.D4GridIdentificationConfiguration
