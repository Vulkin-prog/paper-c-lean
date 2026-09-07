import PaperCV282.CrossoverConditioningTools

/-! # Sparse-event conditioning on the actual infinite source -/
namespace PaperC.V282.CrossoverSparseSource

open MeasureTheory ProbabilityTheory InfiniteRademacher BulkMarkedSource BulkMarkedGeometry
open CrossoverMarkedModel CrossoverMarkedCandidate CrossoverSparseTarget CrossoverSourceCoupling
open CrossoverPrimeClockStable CrossoverBulkAtoms RarePrefixGeometry

noncomputable section
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

instance instProbabilitySourceJoint (M L K : ℕ) (delta : ℝ) : IsProbabilityMeasure (sourceJoint M L K delta) :=
  Measure.isProbabilityMeasure_map ((measurable_actualClockRecord L K).prodMk
    (measurable_spatialMarkedSource _ _)).aemeasurable

def sourceSparseEvent (M L K : ℕ) (delta : ℝ) : Set InfiniteSample :=
  (fun omega => (actualClockRecord L K omega,spatialMarkedSource (bulkStarts M L delta) L omega)) ⁻¹'
    sparseEvent (bulkStarts M L delta)

theorem measurableSet_sourceSparseEvent (M L K : ℕ) (delta : ℝ) :
    MeasurableSet (sourceSparseEvent M L K delta) :=
  ((measurable_actualClockRecord L K).prodMk (measurable_spatialMarkedSource _ _))
    (Set.to_countable _).measurableSet

theorem sourceSparse_mass (M L K : ℕ) (delta : ℝ) :
    infiniteRademacherMeasure.real (sourceSparseEvent M L K delta)=
      (sourceJoint M L K delta).real (sparseEvent (bulkStarts M L delta)) := by
  rw [sourceJoint,map_measureReal_apply ((measurable_actualClockRecord L K).prodMk
    (measurable_spatialMarkedSource _ _)) (Set.to_countable _).measurableSet]
  rfl

theorem sourceSparse_subset_hit {M L K : ℕ} {delta : ℝ}
    (hM : 2≤M) (hL : 1≤L) (hLM : L≤M) (hdelta : 0<delta) :
    sourceSparseEvent M L K delta ⊆ hitEvent M L := by
  intro omega ho
  exact source_rare_subset_hit hM hL hLM hdelta
    (sparseEvent_subset_rareEvent _ ho)

theorem sourceSparse_size_le_one {M L K : ℕ} {delta : ℝ} {omega : InfiniteSample}
    (ho : omega∈sourceSparseEvent M L K delta) :
    totalSize (bulkStarts M L delta) (spatialMarkedSource (bulkStarts M L delta) L omega)≤1 := by
  change (_ ∧ totalSize _ _=0) ∨ (_ ∧ totalSize _ _=1) at ho
  rcases ho with ⟨_,h⟩|⟨_,h⟩
  · exact (le_of_eq h).trans (by decide)
  · exact le_of_eq h

theorem conditional_candidate_source (M L K : ℕ) (delta : ℝ) :
    (cond infiniteRademacherMeasure (sourceSparseEvent M L K delta)).map (candidateSource M L K delta)=
      (cond (sourceJoint M L K delta) (sparseEvent (bulkStarts M L delta))).map (candidate (bulkStarts M L delta)) := by
  have he := congrArg (fun mu : Measure (CandidateSample (bulkStarts M L delta)) => mu.map (candidate (bulkStarts M L delta)))
    (SharpConditioningDiscrete.map_cond_eq infiniteRademacherMeasure
      ((measurable_actualClockRecord L K).prodMk (measurable_spatialMarkedSource (bulkStarts M L delta) L))
      (sparseEvent (bulkStarts M L delta)) (Set.to_countable _).measurableSet)
  rw [Measure.map_map (measurable_of_countable _)
    ((measurable_actualClockRecord L K).prodMk (measurable_spatialMarkedSource _ _))] at he
  exact he

/-- The conditional law of the paper's actual uncensored marked first departure. -/
def conditionalGammaLaw (M L : ℕ) (delta : ℝ) : Measure Record :=
  (cond infiniteRademacherMeasure (hitEvent M L)).map (gamma M L delta)

theorem conditionalGammaLaw_probability {M L : ℕ} (delta : ℝ) (hLM : L≤M) :
    IsProbabilityMeasure (conditionalGammaLaw M L delta) := by
  have hh : 0 < infiniteRademacherMeasure.real (hitEvent M L) := by
    apply (MicroscopicBorderEvents.borderEvent_probability_pos L).trans_le
    apply measureReal_mono (h₂ := measure_ne_top _ _)
    rw [hitEvent_eq_union hLM]
    exact Set.subset_union_left
  letI instProbabilityConditionalHit : IsProbabilityMeasure (cond infiniteRademacherMeasure (hitEvent M L)) :=
    cond_isProbabilityMeasure (ConditionedCountableLaw.measure_ne_zero_of_real_pos _ hh)
  exact Measure.isProbabilityMeasure_map (measurable_gamma M L delta).aemeasurable

end
end PaperC.V282.CrossoverSparseSource
