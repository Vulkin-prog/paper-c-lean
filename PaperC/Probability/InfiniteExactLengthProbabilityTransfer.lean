import PaperC.Probability.InfiniteCylinderTransfer
import PaperC.Probability.ExactLengthBadStartMass

/-!
# Infinite-law transfer for exact-length events

The exact-length estimates in `ExactLengthBadStartMass` are computed as exact
rational probabilities on a finite prime cylinder.  This file identifies
those quantities with the source probability under the infinite Rademacher
product law.

For an event with `q` affine rows at the start `x`, every observed integer lies
in

`{x - 1, x, ..., x + q - 1}`.

Thus the explicit condition `x + (q - 1) ≤ M` is sufficient for restriction to
the prime cylinder at `M`.  The image-law for `restrictToFinite M` then turns
the event identity into an equality of measures.  Since a finite cylinder is
uniform, its event measure is exactly

`ENNReal.ofReal ((uniformEventProbability P : ℚ) : ℝ)`.

The final theorem specializes this statement to the cutoff
`dyadicCutoff N q` used in Lemma 14.8.
-/

open scoped ENNReal
open MeasureTheory Set

namespace PaperC
namespace InfiniteExactLengthProbabilityTransfer

open InfiniteRademacher
open InfiniteCylinderTransfer
open MixedLengthAffine
open ExactLengthBadStartMass

/- Keep the measurable structure definitionally identical to the one used by
the infinite model and its finite projections. -/
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

/-! ## Event-level transfer -/

/-- The exact-length event on the finite prime cylinder at `M`. -/
def finiteExactLengthEvent (M x q : ℕ) : Set (SampleSpace M) :=
  {σ | exactLengthAt σ x q}

/-- The source exact-length event under the infinite Rademacher law. -/
def infiniteExactLengthEvent (x q : ℕ) : Set InfiniteSample :=
  {ω | ExactLengthEvent (infiniteValueBit ω) x q}

/-- Exact rational probability of the event in the prime cylinder at `M`. -/
def finiteExactLengthProbabilityAtCutoff (M x q : ℕ) : ℚ := by
  classical
  exact uniformEventProbability (M := M) (fun σ => exactLengthAt σ x q)

/-- Restriction to a finite set of prime coordinates is measurable. -/
theorem measurable_restrictToFinite (M : ℕ) :
    Measurable (restrictToFinite M) := by
  exact measurable_pi_lambda _ fun p ↦
    measurable_pi_apply (finitePrimeCoordinate M p)

/-- Every exact-length event in a finite cylinder is measurable. -/
theorem measurableSet_finiteExactLengthEvent (M x q : ℕ) :
    MeasurableSet (finiteExactLengthEvent M x q) := by
  exact Set.toFinite (finiteExactLengthEvent M x q) |>.measurableSet

/--
The finite and infinite exact-length predicates agree once the cutoff covers
the rightmost observed vertex `x + q - 1`.
-/
theorem exactLengthAt_restrictToFinite_iff
    {M x q : ℕ} (ω : InfiniteSample)
    (hcut : x + (q - 1) ≤ M) :
    exactLengthAt (restrictToFinite M ω) x q ↔
      ExactLengthEvent (infiniteValueBit ω) x q := by
  unfold exactLengthAt ExactLengthEvent
  constructor
  · rintro ⟨hleft, hmiddle, hright⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa only [
        valueBit_restrictToFinite_eq_infiniteValueBit
          ω (show x - 1 ≤ M by omega),
        valueBit_restrictToFinite_eq_infiniteValueBit
          ω (show x ≤ M by omega)] using hleft
    · intro j hj0 hjlast
      have hj := hmiddle j hj0 hjlast
      simpa only [
        valueBit_restrictToFinite_eq_infiniteValueBit
          ω (show x ≤ M by omega),
        valueBit_restrictToFinite_eq_infiniteValueBit
          ω (show x + j ≤ M by omega)] using hj
    · simpa only [
        valueBit_restrictToFinite_eq_infiniteValueBit
          ω (show x ≤ M by omega),
        valueBit_restrictToFinite_eq_infiniteValueBit
          ω hcut] using hright
  · rintro ⟨hleft, hmiddle, hright⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa only [
        valueBit_restrictToFinite_eq_infiniteValueBit
          ω (show x - 1 ≤ M by omega),
        valueBit_restrictToFinite_eq_infiniteValueBit
          ω (show x ≤ M by omega)] using hleft
    · intro j hj0 hjlast
      have hj := hmiddle j hj0 hjlast
      simpa only [
        valueBit_restrictToFinite_eq_infiniteValueBit
          ω (show x ≤ M by omega),
        valueBit_restrictToFinite_eq_infiniteValueBit
          ω (show x + j ≤ M by omega)] using hj
    · simpa only [
        valueBit_restrictToFinite_eq_infiniteValueBit
          ω (show x ≤ M by omega),
        valueBit_restrictToFinite_eq_infiniteValueBit
          ω hcut] using hright

/-- The infinite event is literally the preimage of its adequate cylinder. -/
theorem infiniteExactLengthEvent_eq_preimage
    {M x q : ℕ} (hcut : x + (q - 1) ≤ M) :
    infiniteExactLengthEvent x q =
      restrictToFinite M ⁻¹' finiteExactLengthEvent M x q := by
  ext ω
  exact (exactLengthAt_restrictToFinite_iff ω hcut).symm

/-- Exact-length events in the infinite product model are measurable. -/
theorem measurableSet_infiniteExactLengthEvent (x q : ℕ) :
    MeasurableSet (infiniteExactLengthEvent x q) := by
  let M := x + (q - 1)
  rw [infiniteExactLengthEvent_eq_preimage
    (M := M) (x := x) (q := q) (by omega)]
  exact
    (measurable_restrictToFinite M)
      (measurableSet_finiteExactLengthEvent M x q)

/-! ## Exact finite probabilities as measures -/

/--
The finite Rademacher product measure of any event is the `ENNReal` embedding
of its exact rational uniform-cylinder probability.
-/
theorem finiteRademacherMeasure_event_eq_uniformEventProbability
    {M : ℕ} (P : SampleSpace M → Prop) [DecidablePred P] :
    finiteRademacherMeasure M {σ | P σ} =
      ENNReal.ofReal (((uniformEventProbability P : ℚ) : ℝ)) := by
  classical
  let s : Finset (SampleSpace M) := Finset.univ.filter P
  have hset : ({σ : SampleSpace M | P σ} : Set (SampleSpace M)) = s := by
    ext σ
    simp [s]
  rw [hset, ← sum_measure_singleton]
  simp_rw [finiteRademacherMeasure_singleton]
  rw [Finset.sum_const, nsmul_eq_mul]
  unfold uniformEventProbability
  change
    (s.card : ℝ≥0∞) *
        ((2 : ℝ≥0∞)⁻¹) ^ Fintype.card (PrimeUpTo M) =
      ENNReal.ofReal
        (((s.card : ℚ) / (Fintype.card (SampleSpace M) : ℚ) : ℚ) : ℝ)
  simp only [Fintype.card_fun, ZMod.card]
  norm_num only [Rat.cast_div, Rat.cast_natCast]
  rw [ENNReal.ofReal_div_of_pos (by positivity)]
  simp only [ENNReal.ofReal_natCast, Nat.cast_pow,
    Nat.cast_ofNat]
  rw [ENNReal.ofReal_pow (by norm_num)]
  simp only [ENNReal.ofReal_ofNat, div_eq_mul_inv, ENNReal.inv_pow]

/--
Measure-level transfer at an arbitrary adequate cutoff.
-/
theorem infiniteExactLengthEvent_measure_eq_finiteProbabilityAtCutoff
    {M x q : ℕ} (hcut : x + (q - 1) ≤ M) :
    infiniteRademacherMeasure (infiniteExactLengthEvent x q) =
      ENNReal.ofReal
        (((finiteExactLengthProbabilityAtCutoff M x q : ℚ) : ℝ)) := by
  classical
  rw [infiniteExactLengthEvent_eq_preimage hcut,
    ← Measure.map_apply (measurable_restrictToFinite M)
      (measurableSet_finiteExactLengthEvent M x q),
    map_infiniteRademacherMeasure_restrictToFinite]
  simpa only [finiteExactLengthProbabilityAtCutoff,
    finiteExactLengthEvent] using
    finiteRademacherMeasure_event_eq_uniformEventProbability
      (fun σ : SampleSpace M => exactLengthAt σ x q)

/-! ## Source reading of the probability used in Lemma 14.8 -/

/--
The rational exact-length probability used in Lemma 14.8 is exactly the
source probability under the infinite Rademacher product law.

The block assumptions are precisely those used by the finite estimates.  The
chosen cylinder `dyadicCutoff N q = 2N+q` covers the rightmost exact-length
vertex for every `x ∈ [N,2N)`.
-/
theorem infiniteExactLengthEvent_measure_eq_exactLengthProbability
    {N q x : ℕ} (hx : x ∈ dyadicBlock N) :
    infiniteRademacherMeasure (infiniteExactLengthEvent x q) =
      ENNReal.ofReal (((exactLengthProbability N q x : ℚ) : ℝ)) := by
  classical
  have hxUpper : x < 2 * N := by
    exact (Finset.mem_Ico.mp (by simpa [dyadicBlock] using hx)).2
  have hcut :
      x + (q - 1) ≤ dyadicCutoff N q := by
    unfold dyadicCutoff
    omega
  simpa only [finiteExactLengthProbabilityAtCutoff,
    exactLengthProbability] using
      (infiniteExactLengthEvent_measure_eq_finiteProbabilityAtCutoff
        (M := dyadicCutoff N q) (x := x) (q := q) hcut)

/--
Real-valued source probability of one exact-length event.  This is the
`toReal` of a probability measure, hence loses no information.
-/
def infiniteExactLengthProbability (x q : ℕ) : ℝ :=
  (infiniteRademacherMeasure (infiniteExactLengthEvent x q)).toReal

/--
Real form of the dyadic specialization.  This is the pointwise replacement
needed to read the rational summands in Lemma 14.8 as source probabilities.
-/
theorem infiniteExactLengthProbability_eq_exactLengthProbability
    {N q x : ℕ} (hx : x ∈ dyadicBlock N) :
    infiniteExactLengthProbability x q =
      ((exactLengthProbability N q x : ℚ) : ℝ) := by
  unfold infiniteExactLengthProbability
  rw [infiniteExactLengthEvent_measure_eq_exactLengthProbability hx,
    ENNReal.toReal_ofReal]
  exact Rat.cast_nonneg.mpr (exactLengthProbability_nonneg N q x)

/--
The literal double sum of source probabilities over the removed starts and
the marks `0 ≤ e ≤ E`.
-/
def totalRemovedInfiniteExactLengthProbability
    (N L E : ℕ) : ℝ :=
  ∑ e ∈ Finset.range (E + 1),
    ∑ x ∈ removedExactLengthStarts N L E,
      infiniteExactLengthProbability x (excessRowCount L e)

/--
Exact source/cylinder identity for the whole left-hand side of Lemma 14.8.
No asymptotic estimate is used here.
-/
theorem totalRemovedInfiniteExactLengthProbability_eq_finiteMass
    (N L E : ℕ) :
    totalRemovedInfiniteExactLengthProbability N L E =
      ((totalRemovedExactLengthProbabilityMass N L E : ℚ) : ℝ) := by
  classical
  unfold totalRemovedInfiniteExactLengthProbability
    totalRemovedExactLengthProbabilityMass
    removedExactLengthProbabilityMass
    exactLengthProbabilityMass
  push_cast
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro x hx
  apply infiniteExactLengthProbability_eq_exactLengthProbability
  exact (BadStartCount.mem_terminalBadStarts.mp
    (by simpa only [removedExactLengthStarts] using hx)).1

end

end InfiniteExactLengthProbabilityTransfer
end PaperC
