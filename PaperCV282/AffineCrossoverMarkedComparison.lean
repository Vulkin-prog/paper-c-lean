import PaperCV282.AffineCrossoverSparseTarget
import PaperCV282.AffineCrossoverSourceCoupling

/-! # Quantitative rare-event comparison for the actual marked first departure -/
namespace PaperC.V282.AffineCrossoverMarkedComparison

open MeasureTheory ProbabilityTheory InfiniteRademacher BulkMarkedGeometry
open CrossoverMarkedModel CrossoverMarkedCandidate CrossoverSparseTarget CrossoverSparseWeights
open CrossoverSparseSource CrossoverSourceCoupling CrossoverConditioningTools
open AffineCrossoverModel AffineCrossoverTarget AffineCrossoverSparseTarget AffineCrossoverSourceCoupling
open CrossoverPrimeClockStable CrossoverBulkAtoms CrossoverMarkedTarget RarePrefixGeometry RarePrefixEvents
open MicroscopicNonvacancy SharpConditioning ConditionedCountableLaw

noncomputable section
open scoped NNReal ENNReal

variable (mu : Measure InfiniteSample) [IsProbabilityMeasure mu]

theorem sourceSparse_positive_of_distance {M L K : ℕ} {delta : ℝ}
    (herror : jointDistance mu M L K delta <
      (AffineCrossoverModel.productJoint mu (bulkStarts M L delta) L K).real (sparseEvent (bulkStarts M L delta))) :
    0 < mu.real (sourceSparseEvent M L K delta) := by
  rw [AffineCrossoverModel.sourceSparse_mass]
  exact (lemma_six_two (AffineCrossoverModel.sourceJoint mu M L K delta) (AffineCrossoverModel.productJoint mu (bulkStarts M L delta) L K)
    (sparseEvent _) (Set.to_countable _).measurableSet le_rfl herror).1

theorem sparse_candidate_comparison {M L K : ℕ} {delta : ℝ}
    (alpha : ℝ≥0) (halpha : mu.real (MicroscopicBorderEvents.borderEvent L)=(alpha : ℝ))
    (hpos : 0<alpha)
    (herror : jointDistance mu M L K delta <
      (AffineCrossoverModel.productJoint mu (bulkStarts M L delta) L K).real (sparseEvent (bulkStarts M L delta))) :
    measureTotalVariation
      ((cond mu (sourceSparseEvent M L K delta)).map (candidateSource M L K delta))
      ((cond (AffineCrossoverModel.productJoint mu (bulkStarts M L delta) L K) (sparseEvent (bulkStarts M L delta))).map
        (candidate (bulkStarts M L delta))) ≤
      jointDistance mu M L K delta /
        (AffineCrossoverModel.productJoint mu (bulkStarts M L delta) L K).real (sparseEvent (bulkStarts M L delta)) := by
  obtain ⟨hp,hc,hd⟩ := lemma_six_two (AffineCrossoverModel.sourceJoint mu M L K delta) (AffineCrossoverModel.productJoint mu (bulkStarts M L delta) L K)
    (sparseEvent _) (Set.to_countable _).measurableSet le_rfl herror
  letI instProbabilitySourceSparse : IsProbabilityMeasure
      (cond (AffineCrossoverModel.sourceJoint mu M L K delta) (sparseEvent (bulkStarts M L delta))) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hp)
  letI instProbabilityProductSparse : IsProbabilityMeasure
      (cond (AffineCrossoverModel.productJoint mu (bulkStarts M L delta) L K) (sparseEvent (bulkStarts M L delta))) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ (AffineCrossoverSparseTarget.sparse_mass_pos mu _ L K alpha halpha hpos))
  rw [AffineCrossoverModel.conditional_candidate_source]
  exact (measureTotalVariation_map_le _ _ (measurable_of_countable _)).trans (hc.trans hd)

/-- All denominators are probabilities of actual events. The stable error is divided only after
the full prime-record comparison has been proved. -/
theorem capped_comparison_bound (habs : mu ≪ infiniteRademacherMeasure) {M L K : ℕ} {delta : ℝ}
    (hM : 2≤M) (hL : 1≤L) (hLM : L≤M) (hdelta : 0<delta)
    (hs : (bulkStarts M L delta).Nonempty)
    (alpha : ℝ≥0) (halpha : mu.real (MicroscopicBorderEvents.borderEvent L)=(alpha : ℝ))
    (hpos : 0<alpha)
    (hclock : (cond mu (MicroscopicBorderEvents.borderEvent L)).map (actualClockRecord L K)=
      (geometricMeasure GeometricClusterTarget.halfSuccess).map (fun j => (true,min j K)))
    (herror : jointDistance mu M L K delta <
      (AffineCrossoverModel.productJoint mu (bulkStarts M L delta) L K).real (sparseEvent (bulkStarts M L delta))) :
    cappedDistance mu M L K delta alpha ≤
      (mu.real (hitEvent M L)-mu.real (sourceSparseEvent M L K delta)) /
        mu.real (hitEvent M L) +
      (mu.real (interiorEvent L)+mu.real (middleEvent M L delta)) /
        mu.real (sourceSparseEvent M L K delta) +
      jointDistance mu M L K delta /
        (AffineCrossoverModel.productJoint mu (bulkStarts M L delta) L K).real (sparseEvent (bulkStarts M L delta)) +
      (totalRate (bulkStarts M L delta) L : ℝ) := by
  have hp := sourceSparse_positive_of_distance mu herror
  have hsubset := sourceSparse_subset_hit (K := K) hM hL hLM hdelta
  have hh := hp.trans_le (measureReal_mono hsubset)
  letI instProbabilityConditionalSparse : IsProbabilityMeasure
      (cond mu (sourceSparseEvent M L K delta)) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hp)
  letI instProbabilityConditionalHit : IsProbabilityMeasure (cond mu (hitEvent M L)) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hh)
  letI instProbabilityProductSparse : IsProbabilityMeasure
      (cond (AffineCrossoverModel.productJoint mu (bulkStarts M L delta) L K) (sparseEvent (bulkStarts M L delta))) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ (AffineCrossoverSparseTarget.sparse_mass_pos mu _ L K alpha halpha hpos))
  let f := fun omega => capBorder K (gamma M L delta omega)
  let A := (cond mu (hitEvent M L)).map f
  let B := (cond mu (sourceSparseEvent M L K delta)).map f
  let C := (cond mu (sourceSparseEvent M L K delta)).map (candidateSource M L K delta)
  let D := (cond (AffineCrossoverModel.productJoint mu (bulkStarts M L delta) L K) (sparseEvent (bulkStarts M L delta))).map
    (candidate (bulkStarts M L delta))
  let Q := (AffineCrossoverTarget.mixedLaw (bulkStarts M L delta) hs L alpha).map (capBorder K)
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
  have hAB := nested_mapped_difference mu (sourceSparseEvent M L K delta) (hitEvent M L)
    (measurableSet_sourceSparseEvent M L K delta) (measurableSet_hitEvent M L) hsubset hp f
    (measurable_capGamma M L K delta)
  have hBC := AffineCrossoverSourceCoupling.conditional_capGamma_candidate_le mu habs (K := K) hM hL hLM hdelta (sourceSparseEvent M L K delta)
    (measurableSet_sourceSparseEvent M L K delta) hp (fun _ ho => sourceSparse_size_le_one ho)
  have hCD := sparse_candidate_comparison mu alpha halpha hpos herror
  have hDQ := AffineCrossoverSparseTarget.conditional_candidate_tv_le mu (bulkStarts M L delta) hs L K alpha halpha hpos hclock
  have hAQ := variation_triangle A B Q
  have hBQ := variation_triangle B C Q
  have hCQ := variation_triangle C D Q
  have he : cappedDistance mu M L K delta alpha=measureTotalVariation A Q := by
    rw [AffineCrossoverModel.cappedDistance,AffineCrossoverTarget.targetLaw_eq alpha hs,sourceLaw,
      Measure.map_map (measurable_of_countable _) (measurable_gamma M L delta)]
    rfl
  rw [he]
  change measureTotalVariation A B≤_ at hAB
  change measureTotalVariation B C≤_ at hBC
  change measureTotalVariation C D≤_ at hCD
  change measureTotalVariation D Q≤_ at hDQ
  linarith

end
end PaperC.V282.AffineCrossoverMarkedComparison
