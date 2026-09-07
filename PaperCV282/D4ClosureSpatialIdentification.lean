import PaperCV282.PointMeasureWeakUniqueness
import PaperCV282.D4ClosureSpatialWeak
import PaperCV282.D4GridIdentificationTheorem

/-! # The complete upper-half spatial law is a geometric marked Poisson law

The row construction and the iid-mark construction have identical grid laws
at every resolution. Both grids converge pointwise to their actual spatial
point measures, hence their continuum laws agree. The same argument after
conditioning proves the full fixed-count spatial resolution.
-/
namespace PaperC.V282.D4ClosureSpatialIdentification

open MeasureTheory ProbabilityTheory Filter
open D4ClosurePointMeasure D4ClosureSpatialHalfLines D4ClosureSpatialWeak
open D4GridIdentificationConfiguration D4GridIdentificationTarget D4GridIdentificationTheorem
open D4ClosureIntegerLevels PointMeasureSpace PoissonPointProcess GeneralPoissonMarking
open SpatialPointEmbedding SpatialMarkedPoissonIdentification UniformSpatialGrid
open GeometricConfigurationCounts
open scoped BigOperators Topology BoundedContinuousFunction

noncomputable section

theorem embedding_gridHalfConfiguration (N : ℕ) (hN : 0<N) (m : ℤ)
    (sample : IntegerSpatialSample) :
    spatialPointEmbedding N (gridHalfConfiguration N hN m sample)=halfLineGridPoints N hN m sample := by
  classical
  unfold gridHalfConfiguration gridRowsConfiguration spatialPointEmbedding
  rw [Finsupp.sum_sum_index]
  · change (D4ClosureSpatialHalfLines.spatialHalfCounts m sample).sum _ = _
    unfold halfLineGridPoints gridPointsFromCounts
    apply Finsupp.sum_congr
    intro e he
    exact spatialPointEmbedding_sampledConfiguration N _ _
  · intro j
    exact zero_nsmul _
  · intro j a b
    exact add_nsmul _ _ _

def halfContinuousMark (x : unitInterval × ℕ) : ℝ × (ℕ × F₂) :=
  (1+(x.1 : ℝ),(x.2,0))

theorem measurable_halfContinuousMark : Measurable halfContinuousMark :=
  (measurable_const.add (measurable_subtype_coe.comp measurable_fst)).prodMk
    (measurable_snd.prodMk measurable_const)

def halfPhysicalMark (N : ℕ) (hN : 0<N) (x : unitInterval × ℕ) : ℝ × (ℕ × F₂) :=
  spatialPosition N (halfGridMark N hN x)

theorem measurable_halfPhysicalMark (N : ℕ) (hN : 0<N) : Measurable (halfPhysicalMark N hN) :=
  (measurable_of_countable _).comp (measurable_halfGridMark N hN)

theorem halfPhysicalMark_tendsto (sizes : ℕ → ℕ) (hN : ∀ n, 0<sizes n)
    (hsizes : Tendsto sizes atTop atTop) (x : unitInterval × ℕ) :
    Tendsto (fun n => halfPhysicalMark (sizes n) (hN n) x) atTop (𝓝 (halfContinuousMark x)) :=
  (physical_grid_position_tendsto sizes hN hsizes x.1).prodMk_nhds tendsto_const_nhds

theorem gridPointLaw_eq (N : ℕ) (hN : 0<N) (theta : ℝ) (m : ℤ) :
    gridPointLaw (integerSpatialSampleMeasure theta) N hN m =
      poissonPointLaw (integerHalfRate theta m) halfMarkMeasure
        (halfPhysicalMark N hN) (measurable_halfPhysicalMark N hN) := by
  apply Subtype.ext
  have he : halfLineGridPoints N hN m=spatialPointEmbedding N ∘ gridHalfConfiguration N hN m := by
    funext sample
    exact (embedding_gridHalfConfiguration N hN m sample).symm
  change (integerSpatialSampleMeasure theta).map (halfLineGridPoints N hN m)=_
  rw [he,← Measure.map_map (measurable_spatialPointEmbedding N) (measurable_gridHalfConfiguration N hN m),
    (hasLaw_gridHalfConfiguration N hN theta m).map_eq]
  change ((markSampleMeasure _ halfMarkMeasure).map (sampledConfiguration N (halfGridMark N hN))).map _ = _
  rw [Measure.map_map (measurable_spatialPointEmbedding N)
    (measurable_sampledConfiguration N _ (measurable_halfGridMark N hN))]
  congr 1
  funext sample
  exact spatialPointEmbedding_sampledConfiguration N _ _

/-- The true complete upper half-line is exactly a Poisson number of independent
uniform positions with independent geometric excesses, not merely a family of
matching one-coordinate marginals. -/
theorem halfLinePointLaw_eq_poisson (theta : ℝ) (m : ℤ) :
    halfLinePointLaw theta m = poissonPointLaw (integerHalfRate theta m) halfMarkMeasure
      halfContinuousMark measurable_halfContinuousMark := by
  have hpos : ∀ n : ℕ, 0<n+1 := fun _ => by omega
  have hs : Tendsto (fun n : ℕ => n+1) atTop atTop := tendsto_add_atTop_nat 1
  have hleft := gridPointLaw_tendsto (integerSpatialSampleMeasure theta) _ hpos hs m
  have hright := poissonPointLaw_tendsto halfMarkMeasure
    (fun _ => integerHalfRate theta m) (integerHalfRate theta m) tendsto_const_nhds
    (fun n => halfPhysicalMark (n+1) (hpos n)) halfContinuousMark
    (fun n => measurable_halfPhysicalMark _ _) measurable_halfContinuousMark
    (halfPhysicalMark_tendsto _ hpos hs)
  simp_rw [gridPointLaw_eq] at hleft
  exact tendsto_nhds_unique hleft hright

set_option maxHeartbeats 1000000 in
def fixedHalfPointLaw (n : ℕ) (f : unitInterval × ℕ → ℝ × (ℕ × F₂)) (hf : Measurable f) :
    ProbabilityMeasure (PointMeasure (ℝ × (ℕ × F₂))) :=
  ⟨(markSequenceMeasure halfMarkMeasure).map
    (fun marks : ℕ → unitInterval × ℕ => fixedPointMeasure n (fun i => f (marks i))),
    Measure.isProbabilityMeasure_map
      ((continuous_fixedPointMeasure n).measurable.comp
        (measurable_pi_lambda _ (fun i => hf.comp (measurable_pi_apply i)))).aemeasurable⟩

theorem fixedHalfPointLaw_tendsto (sizes : ℕ → ℕ) (hN : ∀ k, 0<sizes k)
    (hsizes : Tendsto sizes atTop atTop) (n : ℕ) :
    Tendsto (fun k => fixedHalfPointLaw n (halfPhysicalMark (sizes k) (hN k))
      (measurable_halfPhysicalMark _ _)) atTop
      (𝓝 (fixedHalfPointLaw n halfContinuousMark measurable_halfContinuousMark)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have hi (g : unitInterval × ℕ → ℝ × (ℕ × F₂)) (hg : Measurable g) :
      (∫ x, f x ∂(fixedHalfPointLaw n g hg : Measure _))=
      ∫ marks, f (fixedPointMeasure n (fun i => g (marks i))) ∂markSequenceMeasure halfMarkMeasure :=
    integral_map ((continuous_fixedPointMeasure n).measurable.comp
      (measurable_pi_lambda _ (fun i => hg.comp (measurable_pi_apply i)))).aemeasurable
      f.continuous.measurable.aestronglyMeasurable
  simp_rw [hi]
  exact fixed_point_integral_tendsto halfMarkMeasure _ _
    (fun k => measurable_halfPhysicalMark _ _) (halfPhysicalMark_tendsto sizes hN hsizes) f n

/-- Given the complete upper-tail count n, all n positions and geometric
overshoots are iid, with no finite excess truncation. -/
theorem conditional_halfLinePointConfiguration (theta : ℝ) (m : ℤ) (n : ℕ)
    (hn : (poissonMeasure (integerHalfRate theta m)) {n}≠0) :
    (cond (integerSpatialSampleMeasure theta)
      {sample | configurationSize (D4GridIdentificationConfiguration.spatialHalfCounts m sample)=n}).map
      (halfLinePointConfiguration m)=
      (fixedHalfPointLaw n halfContinuousMark measurable_halfContinuousMark : Measure _) := by
  let mu := cond (integerSpatialSampleMeasure theta)
    {sample | configurationSize (D4GridIdentificationConfiguration.spatialHalfCounts m sample)=n}
  have hm : MeasurableSet {sample : IntegerSpatialSample |
      configurationSize (D4GridIdentificationConfiguration.spatialHalfCounts m sample)=n} :=
    ((measurable_of_countable configurationSize).comp
      (D4GridIdentificationConfiguration.measurable_spatialHalfCounts m)) (measurableSet_singleton n)
  have hp : (integerSpatialSampleMeasure theta)
      {sample | configurationSize (D4GridIdentificationConfiguration.spatialHalfCounts m sample)=n}≠0 := by
    rw [← (hasLaw_spatialHalfCount theta m).map_eq] at hn
    rwa [Measure.map_apply_of_aemeasurable (hasLaw_spatialHalfCount theta m).aemeasurable (measurableSet_singleton n)] at hn
  letI instProbabilityConditionalHalf : IsProbabilityMeasure mu := cond_isProbabilityMeasure hp
  have hgrid (N : ℕ) (hN : 0<N) : gridPointLaw mu N hN m=
      fixedHalfPointLaw n (halfPhysicalMark N hN) (measurable_halfPhysicalMark N hN) := by
    apply Subtype.ext
    have he : halfLineGridPoints N hN m=spatialPointEmbedding N ∘ gridHalfConfiguration N hN m := by
      funext sample
      exact (embedding_gridHalfConfiguration N hN m sample).symm
    change mu.map (halfLineGridPoints N hN m)=_
    rw [he,← Measure.map_map (measurable_spatialPointEmbedding N) (measurable_gridHalfConfiguration N hN m)]
    change ((ProbabilityTheory.cond _ _).map _).map _=_
    rw [conditional_gridHalfConfiguration N hN theta m n hn]
    change ((markSequenceMeasure halfMarkMeasure).map
      (fun marks => sampledConfiguration N (halfGridMark N hN) (n,marks))).map _=_
    rw [Measure.map_map (measurable_spatialPointEmbedding N) (measurable_fixedHalfGrid N hN n)]
    congr 1
    funext marks
    exact spatialPointEmbedding_sampledConfiguration N _ _
  have hpos : ∀ k : ℕ, 0<k+1 := fun _ => by omega
  have hs : Tendsto (fun k : ℕ => k+1) atTop atTop := tendsto_add_atTop_nat 1
  have hleft := gridPointLaw_tendsto mu _ hpos hs m
  simp_rw [hgrid] at hleft
  have he := tendsto_nhds_unique hleft (fixedHalfPointLaw_tendsto _ hpos hs n)
  exact congrArg Subtype.val he

end
end PaperC.V282.D4ClosureSpatialIdentification
