import PaperCV282.D4GridIdentificationRows

/-! # The matching compound-Poisson spatial grid with independent geometric excesses -/
namespace PaperC.V282.D4GridIdentificationTarget

open MeasureTheory ProbabilityTheory GeneralPoissonMarking UniformSpatialGrid
open D4ClosurePointMeasure D4ClosurePointLaws D4ClosureIntegerLevels PoissonFieldMeasure
open D4GridIdentificationRows SpatialMarkedTypes ExactMarkedModel SpatialMarkedPoissonIdentification
open ConditionalStartProbability SpatialDiffuseMarks GeometricClusterTarget
open scoped BigOperators NNReal ENNReal

noncomputable section

def halfMarkMeasure : Measure (unitInterval × ℕ) :=
  unitIntervalUniformMeasure.prod (geometricMeasure halfSuccess)

instance instProbabilityHalfMark : IsProbabilityMeasure halfMarkMeasure := by
  unfold halfMarkMeasure
  infer_instance

def halfGridMark (N : ℕ) (hN : 0<N) (x : unitInterval × ℕ) : SpatialMarkedIndex N :=
  (gridSite N hN x.1,(x.2,0))

theorem measurable_halfGridMark (N : ℕ) (hN : 0<N) : Measurable (halfGridMark N hN) :=
  ((measurable_gridSite N hN).comp measurable_fst).prodMk (measurable_snd.prodMk measurable_const)

def halfGridTarget (N : ℕ) (hN : 0<N) (rate : ℝ≥0) : Measure (SpatialMarkedConfig N) :=
  (markSampleMeasure rate halfMarkMeasure).map (sampledConfiguration N (halfGridMark N hN))

instance instProbabilityHalfGridTarget (N : ℕ) (hN : 0<N) (rate : ℝ≥0) :
    IsProbabilityMeasure (halfGridTarget N hN rate) :=
  Measure.isProbabilityMeasure_map (measurable_sampledConfiguration N _ (measurable_halfGridMark N hN)).aemeasurable

theorem halfGridMark_atom_real (N : ℕ) (hN : 0<N) (j : SpatialMarkedIndex N) :
    halfMarkMeasure.real {x | halfGridMark N hN x=j}=
      if j.2.2=0 then (1/(N : ℝ))*(1/(2 : ℝ)^(j.2.1+1)) else 0 := by
  classical
  by_cases hs : j.2.2=0
  · rw [if_pos hs]
    have he : {x | halfGridMark N hN x=j}=
        {u | gridSite N hN u=j.1} ×ˢ {j.2.1} := by
      ext x
      simp only [halfGridMark,Set.mem_setOf_eq,Set.mem_prod,Set.mem_singleton_iff,Prod.ext_iff,hs,and_true]
    rw [he,halfMarkMeasure,measureReal_prod_prod,geometric_excess_real,
      measureReal_def,grid_cell_probability,ENNReal.toReal_inv,ENNReal.toReal_natCast,one_div]
    simp only [one_div]
  · rw [if_neg hs]
    have he : {x | halfGridMark N hN x=j}=∅ := by
      ext x
      simp [halfGridMark,Prod.ext_iff,Ne.symm hs]
    rw [he,measureReal_empty]

theorem halfGridCategoryRates (N : ℕ) (hN : 0<N) (theta : ℝ) (m : ℤ) (E : ℕ) :
    categoryRates (integerHalfRate theta m) halfMarkMeasure (finiteCategory N E ∘ halfGridMark N hN)=
      fun i : SignedMarkIndex N E => rowRates N hN
        (integerLevelRate theta (m+(i.2.1.val : ℤ))) ((dyadicSiteEquiv N).symm i.1,i.2.2) := by
  funext i
  apply NNReal.coe_injective
  rw [categoryRates_coe,rowRates_coe,integerLevelRate_shift]
  have he : {x | (finiteCategory N E ∘ halfGridMark N hN) x=some i}=
      {x | halfGridMark N hN x=finiteMarkedEmbedding N E i} := by
    ext x
    exact finiteCategory_eq_some_iff N E _ i
  rw [he,halfGridMark_atom_real]
  change (integerHalfRate theta m : ℝ)*(if i.2.2=0 then (1/(N : ℝ))*(1/(2 : ℝ)^(i.2.1.val+1)) else 0)=_
  push_cast
  split_ifs <;> ring

theorem hasLaw_halfGridTarget_projection (N : ℕ) (hN : 0<N) (theta : ℝ) (m : ℤ) (E : ℕ) :
    HasLaw (projectConfiguration N E)
      (fieldMeasure (fun i : SignedMarkIndex N E => rowRates N hN
        (integerLevelRate theta (m+(i.2.1.val : ℤ))) ((dyadicSiteEquiv N).symm i.1,i.2.2)))
      (halfGridTarget N hN (integerHalfRate theta m)) := by
  refine ⟨(measurable_of_countable _).aemeasurable,?_⟩
  rw [halfGridTarget,Measure.map_map (measurable_of_countable _)
    (measurable_sampledConfiguration N _ (measurable_halfGridMark N hN))]
  have h := hasLaw_project_sampledConfiguration N E (integerHalfRate theta m)
    halfMarkMeasure (halfGridMark N hN) (measurable_halfGridMark N hN)
  rw [halfGridCategoryRates] at h
  exact h.map_eq

end
end PaperC.V282.D4GridIdentificationTarget
