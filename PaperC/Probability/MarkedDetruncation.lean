import PaperC.Probability.InfiniteExactLengthDecomposition
import PaperC.Probability.InfiniteStartProbabilityTransfer

/-!
# Exact de-truncation of the marked run process

For a start of base length `L`, the mark `e` records that the run changes for
the first time at offset `L + e`.  Consequently, the occurrence of a mark
strictly larger than `E` forces an ordinary start of length `L + E + 1`.
Conversely, under the almost-sure tail-change statement of Lemma 14.4, every
such longer start has a finite exact mark strictly larger than `E`.

This file records both directions at event level, as well as the exact
first-moment/Markov bound used in the last paragraph of Section 14.  It also
packages the maximum event (with the empty configuration included) as the
void event for starts of length `L + m + 1`.
-/

open scoped BigOperators ENNReal
open MeasureTheory Set Filter

namespace PaperC
namespace MarkedDetruncation

open InfiniteRademacher
open InfiniteExactLengthDecomposition
open InfiniteExactLengthProbabilityTransfer
open InfiniteStartProbabilityTransfer
open ExactLengthDecomposition
open MixedLengthAffine

/- Keep the measurable structure definitionally identical to the source
model. -/
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

noncomputable local instance instIsProbabilityMeasureInfiniteRademacher :
    IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/--
Event that the dyadic marked process contains at least one mark strictly
larger than `E`.
-/
def infiniteMarkTailEvent (N L E : ℕ) : Set InfiniteSample :=
  {ω | ∃ x ∈ dyadicBlock N, ∃ e : ℕ, E < e ∧
    ExactLengthEvent (infiniteValueBit ω) x
      (excessRowCount L e)}

/-- Count of exact marks equal to `e` in the source dyadic process. -/
def infiniteExactLengthCount (N L e : ℕ)
    (ω : InfiniteSample) : ℕ := by
  classical
  exact ∑ x ∈ dyadicBlock N,
    if ExactLengthEvent (infiniteValueBit ω) x
        (excessRowCount L e) then 1 else 0

/-- The mark-tail event is a countable union of measurable cylinder events. -/
theorem infiniteMarkTailEvent_eq_biUnion_iUnion (N L E : ℕ) :
    infiniteMarkTailEvent N L E =
      ⋃ x ∈ dyadicBlock N, ⋃ e : ℕ, ⋃ (_h : E < e),
        infiniteExactLengthEvent x (excessRowCount L e) := by
  ext ω
  simp [infiniteMarkTailEvent, infiniteExactLengthEvent]

/-- The event of seeing a mark beyond a fixed cutoff is measurable. -/
theorem measurableSet_infiniteMarkTailEvent (N L E : ℕ) :
    MeasurableSet (infiniteMarkTailEvent N L E) := by
  rw [infiniteMarkTailEvent_eq_biUnion_iUnion]
  exact MeasurableSet.iUnion fun x =>
    MeasurableSet.iUnion fun _ =>
      MeasurableSet.iUnion fun e =>
        MeasurableSet.iUnion fun _ =>
          measurableSet_infiniteExactLengthEvent x
            (excessRowCount L e)

/--
The deterministic de-truncation inclusion: a mark `e > E` contains a start
of length `L + E + 1`.
-/
theorem infiniteMarkTailEvent_subset_longStartEvent
    (N L E : ℕ) :
    infiniteMarkTailEvent N L E ⊆
      infiniteDyadicStartEvent N (L + E + 1) := by
  intro ω hω
  rcases hω with ⟨x, hx, e, hEe, hExact⟩
  exact ⟨x, hx,
    exactLengthEvent_start_longer_of_excess_gt hEe hExact⟩

/--
The converse deterministic statement, assuming eventual change at every
start in the block.  It makes explicit the only place where Lemma 14.4 is
used in the final de-truncation.
-/
theorem longStartEvent_subset_infiniteMarkTailEvent_of_tailChanges
    {N L E : ℕ} {ω : InfiniteSample}
    (hChange : ∀ x ∈ dyadicBlock N,
      TailChangesAt (infiniteValueBit ω) x) :
    ω ∈ infiniteDyadicStartEvent N (L + E + 1) →
      ω ∈ infiniteMarkTailEvent N L E := by
  rintro ⟨x, hx, hLong⟩
  obtain ⟨f, hf⟩ :=
    exists_exactLengthEvent_of_start_of_tailChangesAt
      hLong (hChange x hx)
  refine ⟨x, hx, E + 1 + f, by omega, ?_⟩
  have hrows :
      excessRowCount L (E + 1 + f) =
        excessRowCount (L + E + 1) f := by
    simp only [excessRowCount]
    omega
  rw [hrows]
  exact hf

/-- Pointwise equality of the tail and longer-start events on good samples. -/
theorem mem_infiniteMarkTailEvent_iff_longStartEvent_of_tailChanges
    {N L E : ℕ} {ω : InfiniteSample}
    (hChange : ∀ x ∈ dyadicBlock N,
      TailChangesAt (infiniteValueBit ω) x) :
    ω ∈ infiniteMarkTailEvent N L E ↔
      ω ∈ infiniteDyadicStartEvent N (L + E + 1) := by
  exact ⟨
    fun h => infiniteMarkTailEvent_subset_longStartEvent N L E h,
    longStartEvent_subset_infiniteMarkTailEvent_of_tailChanges hChange⟩

/--
Lemma 14.4 turns the deterministic inclusion into an almost-sure equality of
events, simultaneously for every start in the fixed dyadic block.
-/
theorem ae_mem_infiniteMarkTailEvent_iff_longStartEvent
    {N L E : ℕ} (hN : 2 ≤ N) :
    ∀ᵐ ω ∂infiniteRademacherMeasure,
      (ω ∈ infiniteMarkTailEvent N L E ↔
        ω ∈ infiniteDyadicStartEvent N (L + E + 1)) := by
  filter_upwards [ae_tailChangesAt_infiniteValueBit] with ω hω
  apply mem_infiniteMarkTailEvent_iff_longStartEvent_of_tailChanges
  intro x hx
  exact hω x (two_le_of_mem_dyadicBlock hN hx)

/-- The source measures of the two de-truncation events are equal. -/
theorem measure_infiniteMarkTailEvent_eq_longStartEvent
    {N L E : ℕ} (hN : 2 ≤ N) :
    infiniteRademacherMeasure (infiniteMarkTailEvent N L E) =
      infiniteRademacherMeasure
        (infiniteDyadicStartEvent N (L + E + 1)) := by
  apply measure_congr
  filter_upwards
    [ae_mem_infiniteMarkTailEvent_iff_longStartEvent hN] with ω hω
  exact propext hω

/-- Real source probability that some mark exceeds `E`. -/
def infiniteMarkTailProbability (N L E : ℕ) : ℝ :=
  (infiniteRademacherMeasure
    (infiniteMarkTailEvent N L E)).toReal

/--
First-moment/Markov bound for the de-truncation event, with no asymptotic
hypothesis:

`P(there is a mark > E) ≤ E Z_{N,L+E+1}`.
-/
theorem infiniteMarkTailProbability_le_longStartExpectation
    (N L E : ℕ) :
    infiniteMarkTailProbability N L E ≤
      (dyadicExpectation N (L + E + 1) : ℝ) := by
  unfold infiniteMarkTailProbability
  have hmono :
      infiniteRademacherMeasure (infiniteMarkTailEvent N L E) ≤
        infiniteRademacherMeasure
          (infiniteDyadicStartEvent N (L + E + 1)) :=
    measure_mono
      (infiniteMarkTailEvent_subset_longStartEvent N L E)
  exact
    (ENNReal.toReal_mono
      (measure_ne_top infiniteRademacherMeasure
        (infiniteDyadicStartEvent N (L + E + 1)))
      hmono).trans
      (infiniteDyadicStartEvent_measure_toReal_le_expectation
        N (L + E + 1))

/-! ## Maximum event -/

/--
Event that every exact mark in the block is at most `m`.  The empty
configuration belongs to this event, implementing the manuscript convention
that its maximum is `-∞`.
-/
def infiniteMaximumAtMostEvent (N L m : ℕ) : Set InfiniteSample :=
  (infiniteMarkTailEvent N L m)ᶜ

/-- Real source probability of the maximum event. -/
def infiniteMaximumAtMostProbability (N L m : ℕ) : ℝ :=
  (infiniteRademacherMeasure
    (infiniteMaximumAtMostEvent N L m)).toReal

/-- The maximum event is measurable. -/
theorem measurableSet_infiniteMaximumAtMostEvent (N L m : ℕ) :
    MeasurableSet (infiniteMaximumAtMostEvent N L m) :=
  (measurableSet_infiniteMarkTailEvent N L m).compl

/--
Almost surely, `maximum mark ≤ m` is exactly the void event for ordinary
starts of length `L + m + 1`.
-/
theorem ae_mem_infiniteMaximumAtMostEvent_iff_no_longStart
    {N L m : ℕ} (hN : 2 ≤ N) :
    ∀ᵐ ω ∂infiniteRademacherMeasure,
      (ω ∈ infiniteMaximumAtMostEvent N L m ↔
        ω ∉ infiniteDyadicStartEvent N (L + m + 1)) := by
  filter_upwards
    [ae_mem_infiniteMarkTailEvent_iff_longStartEvent
      (N := N) (L := L) (E := m) hN] with ω hω
  simpa only [infiniteMaximumAtMostEvent, Set.mem_compl_iff]
    using not_congr hω

/-- Measure-level form of the maximum/void-event identity. -/
theorem measure_infiniteMaximumAtMostEvent_eq_no_longStart
    {N L m : ℕ} (hN : 2 ≤ N) :
    infiniteRademacherMeasure (infiniteMaximumAtMostEvent N L m) =
      infiniteRademacherMeasure
        (infiniteDyadicStartEvent N (L + m + 1))ᶜ := by
  apply measure_congr
  filter_upwards
    [ae_mem_infiniteMaximumAtMostEvent_iff_no_longStart
      (N := N) (L := L) (m := m) hN] with ω hω
  exact propext (by
    simpa only [Set.mem_compl_iff] using hω)

/--
Exact complement formula.  This is the deterministic reduction behind the
last assertion of Corollary 14.8; scalar Poisson convergence for the longer
run immediately yields the displayed limit.
-/
theorem measure_infiniteMaximumAtMostEvent_eq_one_sub_longStart
    {N L m : ℕ} (hN : 2 ≤ N) :
    infiniteRademacherMeasure (infiniteMaximumAtMostEvent N L m) =
      1 -
        infiniteRademacherMeasure
          (infiniteDyadicStartEvent N (L + m + 1)) := by
  rw [measure_infiniteMaximumAtMostEvent_eq_no_longStart hN,
    measure_compl
      (measurableSet_infiniteDyadicStartEvent N (L + m + 1))
      (measure_ne_top infiniteRademacherMeasure
        (infiniteDyadicStartEvent N (L + m + 1)))]
  simp

end

end MarkedDetruncation
end PaperC
