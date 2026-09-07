import PaperCV282.CrossoverMovingTarget

/-! # Quantitative rare-event comparison for the actual marked first departure -/
namespace PaperC.V282.CrossoverMarkedComparison

open MeasureTheory ProbabilityTheory InfiniteRademacher BulkMarkedGeometry
open CrossoverMarkedModel CrossoverMarkedCandidate CrossoverSparseTarget CrossoverSparseWeights
open CrossoverSparseSource CrossoverSourceCoupling CrossoverConditioningTools CrossoverMovingTarget
open CrossoverPrimeClockStable CrossoverBulkAtoms CrossoverMarkedTarget RarePrefixGeometry RarePrefixEvents
open MicroscopicNonvacancy SharpConditioning ConditionedCountableLaw

noncomputable section
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

theorem sourceSparse_positive_of_distance {M L K : ℕ} {delta : ℝ}
    (herror : truncatedJointDistance M L K delta <
      (productJoint (bulkStarts M L delta) L K).real (sparseEvent (bulkStarts M L delta))) :
    0 < infiniteRademacherMeasure.real (sourceSparseEvent M L K delta) := by
  rw [sourceSparse_mass]
  exact (lemma_six_two (sourceJoint M L K delta) (productJoint (bulkStarts M L delta) L K)
    (sparseEvent _) (Set.to_countable _).measurableSet le_rfl herror).1

theorem sparse_candidate_comparison {M L K : ℕ} {delta : ℝ}
    (hs : (bulkStarts M L delta).Nonempty)
    (herror : truncatedJointDistance M L K delta <
      (productJoint (bulkStarts M L delta) L K).real (sparseEvent (bulkStarts M L delta))) :
    measureTotalVariation
      ((cond infiniteRademacherMeasure (sourceSparseEvent M L K delta)).map (candidateSource M L K delta))
      ((cond (productJoint (bulkStarts M L delta) L K) (sparseEvent (bulkStarts M L delta))).map
        (candidate (bulkStarts M L delta))) ≤
      truncatedJointDistance M L K delta /
        (productJoint (bulkStarts M L delta) L K).real (sparseEvent (bulkStarts M L delta)) := by
  obtain ⟨hp,hc,hd⟩ := lemma_six_two (sourceJoint M L K delta) (productJoint (bulkStarts M L delta) L K)
    (sparseEvent _) (Set.to_countable _).measurableSet le_rfl herror
  letI instProbabilitySourceSparse : IsProbabilityMeasure
      (cond (sourceJoint M L K delta) (sparseEvent (bulkStarts M L delta))) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hp)
  letI instProbabilityProductSparse : IsProbabilityMeasure
      (cond (productJoint (bulkStarts M L delta) L K) (sparseEvent (bulkStarts M L delta))) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ (sparse_mass_pos _ hs L K))
  rw [conditional_candidate_source]
  exact (measureTotalVariation_map_le _ _ (measurable_of_countable _)).trans (hc.trans hd)

/-- All denominators are probabilities of actual events. The stable error is divided only after
the full prime-record comparison has been proved. -/
theorem capped_comparison_bound {M L K : ℕ} {delta : ℝ}
    (hM : 2≤M) (hL : 1≤L) (hLM : L≤M) (hdelta : 0<delta)
    (hs : (bulkStarts M L delta).Nonempty)
    (herror : truncatedJointDistance M L K delta <
      (productJoint (bulkStarts M L delta) L K).real (sparseEvent (bulkStarts M L delta))) :
    cappedDistance M L K delta ≤
      (infiniteRademacherMeasure.real (hitEvent M L)-infiniteRademacherMeasure.real (sourceSparseEvent M L K delta)) /
        infiniteRademacherMeasure.real (hitEvent M L) +
      (infiniteRademacherMeasure.real (interiorEvent L)+infiniteRademacherMeasure.real (middleEvent M L delta)) /
        infiniteRademacherMeasure.real (sourceSparseEvent M L K delta) +
      truncatedJointDistance M L K delta /
        (productJoint (bulkStarts M L delta) L K).real (sparseEvent (bulkStarts M L delta)) +
      (totalRate (bulkStarts M L delta) L : ℝ) := by
  have hp := sourceSparse_positive_of_distance herror
  have hsubset := sourceSparse_subset_hit (K := K) hM hL hLM hdelta
  have hh := hp.trans_le (measureReal_mono hsubset)
  letI instProbabilityConditionalSparse : IsProbabilityMeasure
      (cond infiniteRademacherMeasure (sourceSparseEvent M L K delta)) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hp)
  letI instProbabilityConditionalHit : IsProbabilityMeasure (cond infiniteRademacherMeasure (hitEvent M L)) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hh)
  letI instProbabilityProductSparse : IsProbabilityMeasure
      (cond (productJoint (bulkStarts M L delta) L K) (sparseEvent (bulkStarts M L delta))) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ (sparse_mass_pos _ hs L K))
  let f := fun omega => capBorder K (gamma M L delta omega)
  let A := (cond infiniteRademacherMeasure (hitEvent M L)).map f
  let B := (cond infiniteRademacherMeasure (sourceSparseEvent M L K delta)).map f
  let C := (cond infiniteRademacherMeasure (sourceSparseEvent M L K delta)).map (candidateSource M L K delta)
  let D := (cond (productJoint (bulkStarts M L delta) L K) (sparseEvent (bulkStarts M L delta))).map
    (candidate (bulkStarts M L delta))
  let Q := (mixedLaw (bulkStarts M L delta) hs L).map (capBorder K)
  letI instProbabilityA : IsProbabilityMeasure A :=
    Measure.isProbabilityMeasure_map (measurable_capGamma M L K delta).aemeasurable
  letI instProbabilityB : IsProbabilityMeasure B :=
    Measure.isProbabilityMeasure_map (measurable_capGamma M L K delta).aemeasurable
  letI instProbabilityC : IsProbabilityMeasure C :=
    Measure.isProbabilityMeasure_map (measurable_candidateSource M L K delta).aemeasurable
  letI instProbabilityD : IsProbabilityMeasure D :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  letI instProbabilityQ : IsProbabilityMeasure Q :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  have hAB := nested_mapped_difference infiniteRademacherMeasure (sourceSparseEvent M L K delta) (hitEvent M L)
    (measurableSet_sourceSparseEvent M L K delta) (measurableSet_hitEvent M L) hsubset hp f
    (measurable_capGamma M L K delta)
  have hBC := conditional_capGamma_candidate_le (K := K) hM hL hLM hdelta (sourceSparseEvent M L K delta)
    (measurableSet_sourceSparseEvent M L K delta) hp (fun _ ho => sourceSparse_size_le_one ho)
  have hCD := sparse_candidate_comparison hs herror
  have hDQ := conditional_candidate_tv_le (bulkStarts M L delta) hs L K
  have hAQ := variation_triangle A B Q
  have hBQ := variation_triangle B C Q
  have hCQ := variation_triangle C D Q
  have he : cappedDistance M L K delta=measureTotalVariation A Q := by
    rw [cappedDistance,targetLaw_eq hs,conditionalGammaLaw,
      Measure.map_map (measurable_of_countable _) (measurable_gamma M L delta)]
    rfl
  rw [he]
  change measureTotalVariation A B≤_ at hAB
  change measureTotalVariation B C≤_ at hBC
  change measureTotalVariation C D≤_ at hCD
  change measureTotalVariation D Q≤_ at hDQ
  linarith

end
end PaperC.V282.CrossoverMarkedComparison
