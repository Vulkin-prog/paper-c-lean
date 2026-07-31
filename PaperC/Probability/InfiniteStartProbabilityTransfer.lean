import PaperC.Probability.InfiniteExactLengthProbabilityTransfer

/-!
# Infinite-law transfer for ordinary start events

The de-truncation argument at the end of Section 14 bounds the probability of
seeing a large mark by the first moment of starts of a longer run.  The latter
first moment was computed on finite prime cylinders.  This module identifies
it exactly with the corresponding probability under the source infinite
Rademacher product law.

For `x ∈ [N,2N)`, a start of length `L` only observes the vertices
`x - 1, ..., x + L - 1`; the deliberately generous cutoff
`dyadicCutoff N L = 2N + L` therefore covers the event.
-/

open scoped BigOperators ENNReal
open MeasureTheory Set

namespace PaperC
namespace InfiniteStartProbabilityTransfer

open InfiniteRademacher
open InfiniteCylinderTransfer
open InfiniteExactLengthProbabilityTransfer

/- Keep the measurable structure definitionally identical to the one used by
the infinite product model. -/
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

noncomputable local instance instIsProbabilityMeasureInfiniteRademacher :
    IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- A start event on a finite prime cylinder. -/
def finiteStartEvent (M x L : ℕ) : Set (SampleSpace M) :=
  {σ | startAt σ x L}

/-- The corresponding event under the unrestricted product law. -/
def infiniteStartEvent (x L : ℕ) : Set InfiniteSample :=
  {ω | StartEvent (infiniteValueBit ω) x L}

/-- A source start event is the preimage of every adequate finite cylinder. -/
theorem infiniteStartEvent_eq_preimage
    {M x L : ℕ} (hcut : x + L ≤ M) :
    infiniteStartEvent x L =
      restrictToFinite M ⁻¹' finiteStartEvent M x L := by
  ext ω
  exact (startAt_restrictToFinite_iff ω hcut).symm

/-- Every finite-cylinder start event is measurable. -/
theorem measurableSet_finiteStartEvent (M x L : ℕ) :
    MeasurableSet (finiteStartEvent M x L) :=
  Set.toFinite (finiteStartEvent M x L) |>.measurableSet

/-- Every source start event is measurable. -/
theorem measurableSet_infiniteStartEvent (x L : ℕ) :
    MeasurableSet (infiniteStartEvent x L) := by
  let M := x + L
  rw [infiniteStartEvent_eq_preimage
    (M := M) (x := x) (L := L) (by omega)]
  exact
    (measurable_restrictToFinite M)
      (measurableSet_finiteStartEvent M x L)

/--
Exact source/cylinder identity for one start in the dyadic block.
-/
theorem infiniteStartEvent_measure_eq_startProbability
    {N L x : ℕ} (hx : x ∈ dyadicBlock N) :
    infiniteRademacherMeasure (infiniteStartEvent x L) =
      ENNReal.ofReal (((startProbability N L x : ℚ) : ℝ)) := by
  classical
  have hxUpper : x < 2 * N :=
    (Finset.mem_Ico.mp (by simpa [dyadicBlock] using hx)).2
  have hcut : x + L ≤ dyadicCutoff N L := by
    unfold dyadicCutoff
    omega
  rw [infiniteStartEvent_eq_preimage hcut,
    ← Measure.map_apply (measurable_restrictToFinite (dyadicCutoff N L))
      (measurableSet_finiteStartEvent (dyadicCutoff N L) x L),
    map_infiniteRademacherMeasure_restrictToFinite]
  simpa only [finiteStartEvent, startProbability] using
    finiteRademacherMeasure_event_eq_uniformEventProbability
      (M := dyadicCutoff N L) (fun σ => startAt σ x L)

/-- Real-valued source probability of one ordinary start. -/
def infiniteStartProbability (x L : ℕ) : ℝ :=
  (infiniteRademacherMeasure (infiniteStartEvent x L)).toReal

/-- The source probability equals the exact rational cylinder probability. -/
theorem infiniteStartProbability_eq_startProbability
    {N L x : ℕ} (hx : x ∈ dyadicBlock N) :
    infiniteStartProbability x L =
      ((startProbability N L x : ℚ) : ℝ) := by
  unfold infiniteStartProbability
  rw [infiniteStartEvent_measure_eq_startProbability hx,
    ENNReal.toReal_ofReal]
  apply Rat.cast_nonneg.mpr
  unfold startProbability uniformEventProbability
  positivity

/-- Event that at least one start of length `L` occurs in the dyadic block. -/
def infiniteDyadicStartEvent (N L : ℕ) : Set InfiniteSample :=
  {ω | ∃ x ∈ dyadicBlock N,
    StartEvent (infiniteValueBit ω) x L}

/-- The preceding event is the finite union of its one-start events. -/
theorem infiniteDyadicStartEvent_eq_biUnion (N L : ℕ) :
    infiniteDyadicStartEvent N L =
      ⋃ x ∈ dyadicBlock N, infiniteStartEvent x L := by
  ext ω
  simp [infiniteDyadicStartEvent, infiniteStartEvent]

/-- The dyadic event is measurable. -/
theorem measurableSet_infiniteDyadicStartEvent (N L : ℕ) :
    MeasurableSet (infiniteDyadicStartEvent N L) := by
  rw [infiniteDyadicStartEvent_eq_biUnion]
  exact MeasurableSet.iUnion fun x =>
    MeasurableSet.iUnion fun _ =>
      measurableSet_infiniteStartEvent x L

/--
First-moment/Markov bound in the source model: the probability of at least
one start is at most the expected number of starts.
-/
theorem infiniteDyadicStartEvent_measure_toReal_le_expectation
    (N L : ℕ) :
    (infiniteRademacherMeasure
      (infiniteDyadicStartEvent N L)).toReal ≤
        (dyadicExpectation N L : ℝ) := by
  classical
  have hmeasure :
      infiniteRademacherMeasure (infiniteDyadicStartEvent N L) ≤
        ∑ x ∈ dyadicBlock N,
          infiniteRademacherMeasure (infiniteStartEvent x L) := by
    rw [infiniteDyadicStartEvent_eq_biUnion]
    exact measure_biUnion_finset_le (dyadicBlock N)
      (fun x => infiniteStartEvent x L)
  have hreal :=
    ENNReal.toReal_mono
      (by
        exact ENNReal.sum_ne_top.2 fun x hx =>
          measure_ne_top infiniteRademacherMeasure
            (infiniteStartEvent x L))
      hmeasure
  calc
    (infiniteRademacherMeasure
        (infiniteDyadicStartEvent N L)).toReal
        ≤
        (∑ x ∈ dyadicBlock N,
          infiniteRademacherMeasure (infiniteStartEvent x L)).toReal :=
      hreal
    _ =
        ∑ x ∈ dyadicBlock N,
          infiniteStartProbability x L := by
      rw [ENNReal.toReal_sum]
      · rfl
      · intro x hx
        exact measure_ne_top infiniteRademacherMeasure
          (infiniteStartEvent x L)
    _ =
        ∑ x ∈ dyadicBlock N,
          ((startProbability N L x : ℚ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact infiniteStartProbability_eq_startProbability hx
    _ = (dyadicExpectation N L : ℝ) := by
      unfold dyadicExpectation
      push_cast
      apply Finset.sum_congr rfl
      intro x hx
      rfl

end

end InfiniteStartProbabilityTransfer
end PaperC
