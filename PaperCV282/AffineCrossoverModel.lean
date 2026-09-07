import PaperCV282.AffineCrossoverTarget

/-! # Actual source laws before and after rare affine conditioning

The probability measure mu can be the genuine source conditioned by an
affine cylinder. None of its independence or approximation properties is
included in these definitions.
-/
namespace PaperC.V282.AffineCrossoverModel

open MeasureTheory ProbabilityTheory InfiniteRademacher BulkMarkedTypes BulkMarkedSource BulkMarkedTarget
open CrossoverMarkedModel CrossoverMarkedCandidate CrossoverPrimeClockStable CrossoverBulkAtoms
open CrossoverSparseTarget CrossoverSparseSource CrossoverSourceCoupling BulkMarkedGeometry
open RarePrefixGeometry MicroscopicBorderEvents ConditionedCountableLaw
open scoped NNReal ENNReal

noncomputable section

local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

def conditionedMeasure (A : Set InfiniteSample) : Measure InfiniteSample := cond infiniteRademacherMeasure A

theorem conditionedMeasure_probability (A : Set InfiniteSample)
    (hA : 0 < infiniteRademacherMeasure.real A) : IsProbabilityMeasure (conditionedMeasure A) :=
  cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hA)

def recordMeasure (mu : Measure InfiniteSample) (L K : ℕ) : Measure (Bool×ℕ) :=
  mu.map (actualClockRecord L K)

instance instProbabilityRecordMeasure (mu : Measure InfiniteSample) [IsProbabilityMeasure mu] (L K : ℕ) :
    IsProbabilityMeasure (recordMeasure mu L K) :=
  Measure.isProbabilityMeasure_map (measurable_actualClockRecord L K).aemeasurable

def sourceJoint (mu : Measure InfiniteSample) (M L K : ℕ) (delta : ℝ) :
    Measure (CandidateSample (bulkStarts M L delta)) :=
  mu.map (fun omega => (actualClockRecord L K omega,spatialMarkedSource (bulkStarts M L delta) L omega))

instance instProbabilitySourceJoint (mu : Measure InfiniteSample) [IsProbabilityMeasure mu]
    (M L K : ℕ) (delta : ℝ) : IsProbabilityMeasure (sourceJoint mu M L K delta) :=
  Measure.isProbabilityMeasure_map ((measurable_actualClockRecord L K).prodMk
    (measurable_spatialMarkedSource _ _)).aemeasurable

def productJoint (mu : Measure InfiniteSample) (sites : Finset ℕ) (L K : ℕ) : Measure (CandidateSample sites) :=
  (recordMeasure mu L K).prod (spatialTargetMeasure sites L)

instance instProbabilityProductJoint (mu : Measure InfiniteSample) [IsProbabilityMeasure mu]
    (sites : Finset ℕ) (L K : ℕ) : IsProbabilityMeasure (productJoint mu sites L K) := by
  unfold productJoint
  infer_instance

def jointDistance (mu : Measure InfiniteSample) (M L K : ℕ) (delta : ℝ) : ℝ :=
  SharpConditioning.measureTotalVariation (sourceJoint mu M L K delta) (productJoint mu (bulkStarts M L delta) L K)

def hitProbability (mu : Measure InfiniteSample) (M L : ℕ) : ℝ := mu.real (hitEvent M L)

def sourceLaw (mu : Measure InfiniteSample) (M L : ℕ) (delta : ℝ) : Measure Record :=
  (cond mu (hitEvent M L)).map (gamma M L delta)

theorem sourceLaw_probability (mu : Measure InfiniteSample) [IsProbabilityMeasure mu]
    (M L : ℕ) (delta : ℝ) (hh : 0<hitProbability mu M L) : IsProbabilityMeasure (sourceLaw mu M L delta) := by
  letI instProbabilityConditionalHit : IsProbabilityMeasure (cond mu (hitEvent M L)) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hh)
  exact Measure.isProbabilityMeasure_map (measurable_gamma M L delta).aemeasurable

theorem sourceLaw_conditioned (A : Set InfiniteSample) (hA : MeasurableSet A) (M L : ℕ) (delta : ℝ) :
    sourceLaw (conditionedMeasure A) M L delta=
      (cond infiniteRademacherMeasure (A∩hitEvent M L)).map (gamma M L delta) := by
  unfold sourceLaw conditionedMeasure
  rw [cond_cond_eq_cond_inter hA (measurableSet_hitEvent M L)]

def actualDistance (mu : Measure InfiniteSample) (M L : ℕ) (delta : ℝ) (alpha : ℝ≥0) : ℝ :=
  SharpConditioning.measureTotalVariation (sourceLaw mu M L delta) (AffineCrossoverTarget.targetLaw M L delta alpha)

def cappedDistance (mu : Measure InfiniteSample) (M L K : ℕ) (delta : ℝ) (alpha : ℝ≥0) : ℝ :=
  SharpConditioning.measureTotalVariation ((sourceLaw mu M L delta).map (capBorder K))
    ((AffineCrossoverTarget.targetLaw M L delta alpha).map (capBorder K))

theorem sourceSparse_mass (mu : Measure InfiniteSample) (M L K : ℕ) (delta : ℝ) :
    mu.real (sourceSparseEvent M L K delta)=
      (sourceJoint mu M L K delta).real (sparseEvent (bulkStarts M L delta)) := by
  rw [sourceJoint,map_measureReal_apply ((measurable_actualClockRecord L K).prodMk
    (measurable_spatialMarkedSource _ _)) (Set.to_countable _).measurableSet]
  rfl

theorem conditional_candidate_source (mu : Measure InfiniteSample) (M L K : ℕ) (delta : ℝ) :
    (cond mu (sourceSparseEvent M L K delta)).map (candidateSource M L K delta)=
      (cond (sourceJoint mu M L K delta) (sparseEvent (bulkStarts M L delta))).map
        (candidate (bulkStarts M L delta)) := by
  have he := congrArg (fun nu : Measure (CandidateSample (bulkStarts M L delta)) =>
      nu.map (candidate (bulkStarts M L delta)))
    (SharpConditioningDiscrete.map_cond_eq mu
      ((measurable_actualClockRecord L K).prodMk (measurable_spatialMarkedSource (bulkStarts M L delta) L))
      (sparseEvent (bulkStarts M L delta)) (Set.to_countable _).measurableSet)
  rw [Measure.map_map (measurable_of_countable _)
    ((measurable_actualClockRecord L K).prodMk (measurable_spatialMarkedSource _ _))] at he
  exact he

end
end PaperC.V282.AffineCrossoverModel
