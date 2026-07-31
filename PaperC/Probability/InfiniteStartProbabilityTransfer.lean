import PaperC.Probability.InfiniteExactLengthProbabilityTransfer
import PaperC.Probability.SectionThirteenCouplings

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

open ArratiaGoldsteinGordonInput
open InfiniteRademacher
open InfiniteCylinderTransfer
open InfiniteExactLengthProbabilityTransfer
open ConditionalAGGAverage
open SectionThirteenCouplings
open SectionThirteenFiniteBound

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

/-! ## Exact law of the complete dyadic start count -/

/--
The complete dyadic start count, now read directly as a random variable on
the infinite Rademacher product space.

This is the source-model version of `dyadicCount`: it observes the same
finite collection of start events, but evaluates them through
`infiniteValueBit` instead of first restricting the sample to a prime
cylinder.
-/
noncomputable def infiniteDyadicStartCount
    (N L : ℕ) (ω : InfiniteSample) : ℕ := by
  classical
  exact ∑ x ∈ dyadicBlock N,
    if StartEvent (infiniteValueBit ω) x L then 1 else 0

/-- Restriction to the canonical dyadic cylinder preserves the count. -/
theorem dyadicCount_restrictToFinite_eq_infiniteDyadicStartCount
    (N L : ℕ) (ω : InfiniteSample) :
    dyadicCount N L (restrictToFinite (dyadicCutoff N L) ω) =
      infiniteDyadicStartCount N L ω := by
  classical
  unfold dyadicCount infiniteDyadicStartCount
  apply Finset.sum_congr rfl
  intro x hx
  have hxUpper : x < 2 * N :=
    (Finset.mem_Ico.mp (by simpa [dyadicBlock] using hx)).2
  have hcut : x + L ≤ dyadicCutoff N L := by
    unfold dyadicCutoff
    omega
  have hiff :=
    startAt_restrictToFinite_iff
      (M := dyadicCutoff N L) (x := x) (L := L) ω hcut
  by_cases hstart : StartEvent (infiniteValueBit ω) x L
  · simp [hstart, hiff.mpr hstart]
  · have hfinite :
        ¬ startAt (restrictToFinite (dyadicCutoff N L) ω) x L :=
      fun h => hstart (hiff.mp h)
    simp [hstart, hfinite]

/-- One atom of the infinite dyadic count. -/
def infiniteDyadicStartCountEvent
    (N L k : ℕ) : Set InfiniteSample :=
  {ω | infiniteDyadicStartCount N L ω = k}

/-- The matching atom on the canonical finite cylinder. -/
def finiteDyadicStartCountEvent
    (N L k : ℕ) : Set (DyadicSample N L) :=
  {σ | dyadicCount N L σ = k}

/-- Every infinite count atom is the preimage of its finite-cylinder atom. -/
theorem infiniteDyadicStartCountEvent_eq_preimage
    (N L k : ℕ) :
    infiniteDyadicStartCountEvent N L k =
      restrictToFinite (dyadicCutoff N L) ⁻¹'
        finiteDyadicStartCountEvent N L k := by
  ext ω
  change
    infiniteDyadicStartCount N L ω = k ↔
      dyadicCount N L (restrictToFinite (dyadicCutoff N L) ω) = k
  exact iff_of_eq
    (congrArg (fun count => count = k)
      (dyadicCount_restrictToFinite_eq_infiniteDyadicStartCount
        N L ω)).symm

/-- Finite-cylinder count atoms are measurable. -/
theorem measurableSet_finiteDyadicStartCountEvent
    (N L k : ℕ) :
    MeasurableSet (finiteDyadicStartCountEvent N L k) :=
  Set.toFinite (finiteDyadicStartCountEvent N L k) |>.measurableSet

/-- Infinite-product count atoms are measurable cylinders. -/
theorem measurableSet_infiniteDyadicStartCountEvent
    (N L k : ℕ) :
    MeasurableSet (infiniteDyadicStartCountEvent N L k) := by
  rw [infiniteDyadicStartCountEvent_eq_preimage]
  exact
    (measurable_restrictToFinite (dyadicCutoff N L))
      (measurableSet_finiteDyadicStartCountEvent N L k)

/-- Mass function of the dyadic count under the infinite product law. -/
noncomputable def infiniteDyadicStartLaw
    (N L k : ℕ) : ℝ :=
  (infiniteRademacherMeasure
    (infiniteDyadicStartCountEvent N L k)).toReal

/--
The law of `infiniteDyadicStartCount` is exactly the already audited
finite-cylinder law `fullDyadicStartLaw`.
-/
theorem infiniteDyadicStartCount_law_eq_fullDyadicStartLaw
    (N L : ℕ) :
    infiniteDyadicStartLaw N L = fullDyadicStartLaw N L := by
  funext k
  classical
  unfold infiniteDyadicStartLaw
  rw [infiniteDyadicStartCountEvent_eq_preimage,
    ← Measure.map_apply
      (measurable_restrictToFinite (dyadicCutoff N L))
      (measurableSet_finiteDyadicStartCountEvent N L k),
    map_infiniteRademacherMeasure_restrictToFinite]
  simp only [finiteDyadicStartCountEvent]
  rw [finiteRademacherMeasure_event_eq_uniformEventProbability,
    ENNReal.toReal_ofReal]
  · rw [← finiteUniformProbability_eq_uniformEventProbability,
      ← eventProbability_fullUniformPMF_eq]
    unfold fullDyadicStartLaw finiteNatLaw eventProbability
    apply Finset.sum_congr rfl
    intro ω _hω
    by_cases hcount : dyadicCount N L ω = k <;> simp [hcount]
  · apply Rat.cast_nonneg.mpr
    unfold uniformEventProbability
    positivity

end

end InfiniteStartProbabilityTransfer
end PaperC
