import PaperCV282.CrossoverSourceSigns

/-! # Transfer of the crossover sign bias to the true least departure -/
namespace PaperC.V282.CrossoverSignComparison

open MeasureTheory ProbabilityTheory InfiniteRademacher CrossoverMarkedModel CrossoverMarkedTarget
open CrossoverMovingTarget CrossoverSparseSource CrossoverSourceSigns BulkMarkedGeometry
open RarePrefixGeometry CrossoverBulkAtoms SharpConditioning InfiniteMassCoupling

noncomputable section
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

theorem targetLaw_cemetery_zero (M L : ℕ) (delta : ℝ) : (targetLaw M L delta).real {none}=0 := by
  unfold targetLaw
  split_ifs with hs
  · exact mixedLaw_cemetery_zero _ hs L
  · rw [borderLaw,map_measureReal_apply (measurable_of_countable _) (measurableSet_singleton _)]
    have he : borderLabel ⁻¹' {none}=∅ := by ext k; simp [borderLabel]
    simp [he]

theorem conditional_cemetery_probability_le {M L : ℕ} (delta : ℝ) (hLM : L≤M) :
    (conditionalGammaLaw M L delta).real {none} ≤ actualDistance M L delta := by
  letI instProbabilityGamma : IsProbabilityMeasure (conditionalGammaLaw M L delta) :=
    conditionalGammaLaw_probability delta hLM
  have h := discrepancy_le (conditionalGammaLaw M L delta) (targetLaw M L delta) {none} (measurableSet_singleton _)
  simpa only [targetLaw_cemetery_zero,sub_zero,abs_of_nonneg measureReal_nonneg,actualDistance] using h

/-- The actual sign at X* differs from the recorded sign only on the cemetery event. -/
theorem positive_source_probability_error_le {M L : ℕ} {delta : ℝ} (hLM : L≤M)
    (hs : (bulkStarts M L delta).Nonempty) :
    |(cond infiniteRademacherMeasure (hitEvent M L)).real {omega | positiveSource M L omega=true}-
      ((borderRate L : ℝ)+(totalRate (bulkStarts M L delta) L : ℝ)/2)/
        ((borderRate L : ℝ)+(totalRate (bulkStarts M L delta) L : ℝ))| ≤ 2*actualDistance M L delta := by
  have hpos : 0 < infiniteRademacherMeasure.real (hitEvent M L) := by
    apply (MicroscopicBorderEvents.borderEvent_probability_pos L).trans_le
    apply measureReal_mono (h₂ := measure_ne_top _ _)
    rw [hitEvent_eq_union hLM]
    exact Set.subset_union_left
  letI instProbabilityConditional : IsProbabilityMeasure (cond infiniteRademacherMeasure (hitEvent M L)) :=
    cond_isProbabilityMeasure (ConditionedCountableLaw.measure_ne_zero_of_real_pos _ hpos)
  letI instProbabilityGamma : IsProbabilityMeasure (conditionalGammaLaw M L delta) :=
    conditionalGammaLaw_probability delta hLM
  have hcouple := event_discrepancy_le_disagreement
    (cond infiniteRademacherMeasure (hitEvent M L)) (positiveSource M L)
    (fun omega => positiveSign (gamma M L delta omega)) {true}
  have hbad : {omega | positiveSource M L omega≠positiveSign (gamma M L delta omega)} ⊆
      {omega | gamma M L delta omega=none} := by
    intro omega ho
    by_contra hg
    exact ho (positiveSign_eq_source_off_cemetery hg).symm
  have hcem := conditional_cemetery_probability_le delta hLM
  rw [conditionalGammaLaw,map_measureReal_apply (measurable_gamma M L delta) (measurableSet_singleton _)] at hcem
  have hb := (measureReal_mono (μ := cond infiniteRademacherMeasure (hitEvent M L)) hbad).trans hcem
  have hdis := discrepancy_le (conditionalGammaLaw M L delta) (targetLaw M L delta)
    {r | positiveSign r=true} (Set.to_countable _).measurableSet
  rw [targetLaw_eq hs,mixedLaw_positive,conditionalGammaLaw,
    map_measureReal_apply (measurable_gamma M L delta) (Set.to_countable _).measurableSet] at hdis
  have htri := abs_sub_le
    ((cond infiniteRademacherMeasure (hitEvent M L)).real {omega | positiveSource M L omega=true})
    ((cond infiniteRademacherMeasure (hitEvent M L)).real {omega | positiveSign (gamma M L delta omega)=true})
    (((borderRate L : ℝ)+(totalRate (bulkStarts M L delta) L : ℝ)/2)/
      ((borderRate L : ℝ)+(totalRate (bulkStarts M L delta) L : ℝ)))
  have heTV : measureTotalVariation
      ((cond infiniteRademacherMeasure (hitEvent M L)).map (gamma M L delta))
      (mixedLaw (bulkStarts M L delta) hs L)=actualDistance M L delta := by
    rw [actualDistance,conditionalGammaLaw,targetLaw_eq hs]
  rw [heTV] at hdis
  change |(cond infiniteRademacherMeasure (hitEvent M L)).real {omega | positiveSource M L omega=true}-
    (cond infiniteRademacherMeasure (hitEvent M L)).real {omega | positiveSign (gamma M L delta omega)=true}| ≤ _ at hcouple
  change |(cond infiniteRademacherMeasure (hitEvent M L)).real {omega | positiveSign (gamma M L delta omega)=true}-
    ((borderRate L : ℝ)+(totalRate (bulkStarts M L delta) L : ℝ)/2)/
      ((borderRate L : ℝ)+(totalRate (bulkStarts M L delta) L : ℝ))| ≤ _ at hdis
  change _ ≤ actualDistance M L delta at hb
  linarith

end
end PaperC.V282.CrossoverSignComparison
