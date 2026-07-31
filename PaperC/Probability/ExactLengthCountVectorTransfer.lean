import PaperC.Probability.MarkedDetruncation
import PaperC.Probability.MarkedConditionalDependencyGraph

/-!
# Finite-vector transfer for exact run-length counts

For a fixed mark cutoff `E`, the vector

`(C₀, ..., C_E)`,  `C_e = ∑_{x ∈ [N,2N)} K_{x,e}`,

depends only on the finite prime cylinder at the common row count
`Q = L + E + 1`.  This file records the exact image-law transfer for both
the complete vector and the vector restricted to the retained starts of
Lemma 14.8.

It also isolates the deterministic coupling used after the marked
Stein--Chen argument: the complete and retained vectors can differ only if
one of the removed exact-length events occurs.  Consequently every joint
atom differs by at most the literal removed probability mass from
Lemma 14.8.
-/

open scoped BigOperators ENNReal symmDiff
open MeasureTheory Set

namespace PaperC
namespace ExactLengthCountVectorTransfer

open ExactLengthBadStartMass
open InfiniteCylinderTransfer
open InfiniteExactLengthProbabilityTransfer
open InfiniteRademacher
open MarkedConditionalDependencyGraph
open MarkedDetruncation
open MixedLengthAffine

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

local instance (P : Prop) : Decidable P :=
  Classical.propDecidable P

noncomputable local instance instIsProbabilityMeasureInfiniteRademacher :
    IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- Type of the count vector with marks `0, ..., E`. -/
abbrev ExactLengthCountVector (E : ℕ) :=
  Fin (E + 1) → ℕ

/--
Finite-cylinder count vector on an arbitrary set of starts contained in the
dyadic block.
-/
def finiteExactLengthCountVectorOn
    (N L E : ℕ) (starts : Finset ℕ)
    (σ : SampleSpace (markedCylinderCutoff N L E)) :
    ExactLengthCountVector E :=
  fun e ↦
    ∑ x ∈ starts,
      if exactLengthAt σ x (excessRowCount L e.1) then 1 else 0

/-- Source count vector on an arbitrary finite set of starts. -/
def infiniteExactLengthCountVectorOn
    (L E : ℕ) (starts : Finset ℕ)
    (ω : InfiniteSample) :
    ExactLengthCountVector E :=
  fun e ↦
    ∑ x ∈ starts,
      if ExactLengthEvent (infiniteValueBit ω) x
          (excessRowCount L e.1) then 1 else 0

/-- Complete finite-cylinder exact-length count vector. -/
def finiteExactLengthCountVector
    (N L E : ℕ)
    (σ : SampleSpace (markedCylinderCutoff N L E)) :
    ExactLengthCountVector E :=
  finiteExactLengthCountVectorOn N L E (dyadicBlock N) σ

/-- Complete source exact-length count vector. -/
def infiniteExactLengthCountVector
    (N L E : ℕ) (ω : InfiniteSample) :
    ExactLengthCountVector E :=
  infiniteExactLengthCountVectorOn L E (dyadicBlock N) ω

/-- Finite-cylinder vector after removing the starts in `D(Q)`. -/
def finiteRetainedExactLengthCountVector
    (N L E : ℕ)
    (σ : SampleSpace (markedCylinderCutoff N L E)) :
    ExactLengthCountVector E :=
  finiteExactLengthCountVectorOn N L E
    (retainedMarkedStarts N L E) σ

/-- Source vector after removing the starts in `D(Q)`. -/
def infiniteRetainedExactLengthCountVector
    (N L E : ℕ) (ω : InfiniteSample) :
    ExactLengthCountVector E :=
  infiniteExactLengthCountVectorOn L E
    (retainedMarkedStarts N L E) ω

/-- The vector coordinate agrees with the scalar count from de-truncation. -/
theorem infiniteExactLengthCountVector_apply
    (N L E : ℕ) (ω : InfiniteSample) (e : Fin (E + 1)) :
    infiniteExactLengthCountVector N L E ω e =
      infiniteExactLengthCount N L e.1 ω := by
  rfl

/-- Retained starts form a subset of the dyadic block. -/
theorem retainedMarkedStarts_subset_dyadicBlock
    (N L E : ℕ) :
    retainedMarkedStarts N L E ⊆ dyadicBlock N := by
  intro x hx
  exact (mem_retainedMarkedStarts.mp hx).1

/--
Every coordinate of the source vector agrees with restriction to the common
finite cylinder.
-/
theorem finiteExactLengthCountVectorOn_restrictToFinite
    {N L E : ℕ} {starts : Finset ℕ}
    (hstarts : starts ⊆ dyadicBlock N)
    (ω : InfiniteSample) :
    finiteExactLengthCountVectorOn N L E starts
        (restrictToFinite (markedCylinderCutoff N L E) ω) =
      infiniteExactLengthCountVectorOn L E starts ω := by
  classical
  funext e
  unfold finiteExactLengthCountVectorOn
    infiniteExactLengthCountVectorOn
  apply Finset.sum_congr rfl
  intro x hx
  have hxBlock := hstarts hx
  have hxUpper : x < 2 * N :=
    (Finset.mem_Ico.mp (by simpa [dyadicBlock] using hxBlock)).2
  have he : e.1 ≤ E := Nat.lt_succ_iff.mp e.2
  have hcut :
      x + (excessRowCount L e.1 - 1) ≤
        markedCylinderCutoff N L E := by
    simp only [markedCylinderCutoff, markedCommonRowCount,
      commonExactRowCount, excessRowCount, dyadicCutoff]
    omega
  have hiff :=
    exactLengthAt_restrictToFinite_iff
      (M := markedCylinderCutoff N L E)
      (x := x) (q := excessRowCount L e.1) ω hcut
  by_cases hExact :
      ExactLengthEvent (infiniteValueBit ω) x
        (excessRowCount L e.1)
  · simp [hExact, hiff.mpr hExact]
  · have hFinite :
        ¬ exactLengthAt
          (restrictToFinite (markedCylinderCutoff N L E) ω)
          x (excessRowCount L e.1) :=
      fun h ↦ hExact (hiff.mp h)
    simp [hExact, hFinite]

theorem finiteExactLengthCountVector_restrictToFinite
    (N L E : ℕ) (ω : InfiniteSample) :
    finiteExactLengthCountVector N L E
        (restrictToFinite (markedCylinderCutoff N L E) ω) =
      infiniteExactLengthCountVector N L E ω := by
  exact finiteExactLengthCountVectorOn_restrictToFinite
    (N := N) (L := L) (E := E) (starts := dyadicBlock N)
    (fun _ hx ↦ hx) ω

theorem finiteRetainedExactLengthCountVector_restrictToFinite
    (N L E : ℕ) (ω : InfiniteSample) :
    finiteRetainedExactLengthCountVector N L E
        (restrictToFinite (markedCylinderCutoff N L E) ω) =
      infiniteRetainedExactLengthCountVector N L E ω := by
  exact finiteExactLengthCountVectorOn_restrictToFinite
    (N := N) (L := L) (E := E)
    (starts := retainedMarkedStarts N L E)
    (retainedMarkedStarts_subset_dyadicBlock N L E) ω

/-! ## Joint atoms and exact source/cylinder transfer -/

/-- A complete-vector atom on the common finite cylinder. -/
def finiteExactLengthCountVectorEvent
    (N L E : ℕ) (k : ExactLengthCountVector E) :
    Set (SampleSpace (markedCylinderCutoff N L E)) :=
  {σ | finiteExactLengthCountVector N L E σ = k}

/-- A retained-vector atom on the common finite cylinder. -/
def finiteRetainedExactLengthCountVectorEvent
    (N L E : ℕ) (k : ExactLengthCountVector E) :
    Set (SampleSpace (markedCylinderCutoff N L E)) :=
  {σ | finiteRetainedExactLengthCountVector N L E σ = k}

/-- A complete-vector atom in the source model. -/
def infiniteExactLengthCountVectorEvent
    (N L E : ℕ) (k : ExactLengthCountVector E) :
    Set InfiniteSample :=
  {ω | infiniteExactLengthCountVector N L E ω = k}

/-- A retained-vector atom in the source model. -/
def infiniteRetainedExactLengthCountVectorEvent
    (N L E : ℕ) (k : ExactLengthCountVector E) :
    Set InfiniteSample :=
  {ω | infiniteRetainedExactLengthCountVector N L E ω = k}

theorem measurableSet_finiteExactLengthCountVectorEvent
    (N L E : ℕ) (k : ExactLengthCountVector E) :
    MeasurableSet (finiteExactLengthCountVectorEvent N L E k) :=
  Set.toFinite (finiteExactLengthCountVectorEvent N L E k) |>.measurableSet

theorem measurableSet_finiteRetainedExactLengthCountVectorEvent
    (N L E : ℕ) (k : ExactLengthCountVector E) :
    MeasurableSet (finiteRetainedExactLengthCountVectorEvent N L E k) :=
  Set.toFinite
    (finiteRetainedExactLengthCountVectorEvent N L E k) |>.measurableSet

theorem infiniteExactLengthCountVectorEvent_eq_preimage
    (N L E : ℕ) (k : ExactLengthCountVector E) :
    infiniteExactLengthCountVectorEvent N L E k =
      restrictToFinite (markedCylinderCutoff N L E) ⁻¹'
        finiteExactLengthCountVectorEvent N L E k := by
  ext ω
  change
    infiniteExactLengthCountVector N L E ω = k ↔
      finiteExactLengthCountVector N L E
        (restrictToFinite (markedCylinderCutoff N L E) ω) = k
  exact iff_of_eq
    (congrArg (fun v ↦ v = k)
      (finiteExactLengthCountVector_restrictToFinite N L E ω)).symm

theorem infiniteRetainedExactLengthCountVectorEvent_eq_preimage
    (N L E : ℕ) (k : ExactLengthCountVector E) :
    infiniteRetainedExactLengthCountVectorEvent N L E k =
      restrictToFinite (markedCylinderCutoff N L E) ⁻¹'
        finiteRetainedExactLengthCountVectorEvent N L E k := by
  ext ω
  change
    infiniteRetainedExactLengthCountVector N L E ω = k ↔
      finiteRetainedExactLengthCountVector N L E
        (restrictToFinite (markedCylinderCutoff N L E) ω) = k
  exact iff_of_eq
    (congrArg (fun v ↦ v = k)
      (finiteRetainedExactLengthCountVector_restrictToFinite
        N L E ω)).symm

theorem measurableSet_infiniteExactLengthCountVectorEvent
    (N L E : ℕ) (k : ExactLengthCountVector E) :
    MeasurableSet (infiniteExactLengthCountVectorEvent N L E k) := by
  rw [infiniteExactLengthCountVectorEvent_eq_preimage]
  exact
    (measurable_restrictToFinite (markedCylinderCutoff N L E))
      (measurableSet_finiteExactLengthCountVectorEvent N L E k)

theorem measurableSet_infiniteRetainedExactLengthCountVectorEvent
    (N L E : ℕ) (k : ExactLengthCountVector E) :
    MeasurableSet
      (infiniteRetainedExactLengthCountVectorEvent N L E k) := by
  rw [infiniteRetainedExactLengthCountVectorEvent_eq_preimage]
  exact
    (measurable_restrictToFinite (markedCylinderCutoff N L E))
      (measurableSet_finiteRetainedExactLengthCountVectorEvent N L E k)

/-- Exact real joint mass of the complete finite-cylinder vector. -/
def finiteExactLengthCountVectorLaw
    (N L E : ℕ) (k : ExactLengthCountVector E) : ℝ :=
  (((uniformEventProbability
    (M := markedCylinderCutoff N L E)
    (fun σ ↦ finiteExactLengthCountVector N L E σ = k) : ℚ) : ℝ))

/-- Exact real joint mass of the retained finite-cylinder vector. -/
def finiteRetainedExactLengthCountVectorLaw
    (N L E : ℕ) (k : ExactLengthCountVector E) : ℝ :=
  (((uniformEventProbability
    (M := markedCylinderCutoff N L E)
    (fun σ ↦
      finiteRetainedExactLengthCountVector N L E σ = k) : ℚ) : ℝ))

/-- Joint mass of the complete vector under the source law. -/
def infiniteExactLengthCountVectorLaw
    (N L E : ℕ) (k : ExactLengthCountVector E) : ℝ :=
  (infiniteRademacherMeasure
    (infiniteExactLengthCountVectorEvent N L E k)).toReal

/-- Joint mass of the retained vector under the source law. -/
def infiniteRetainedExactLengthCountVectorLaw
    (N L E : ℕ) (k : ExactLengthCountVector E) : ℝ :=
  (infiniteRademacherMeasure
    (infiniteRetainedExactLengthCountVectorEvent N L E k)).toReal

theorem infiniteExactLengthCountVectorLaw_eq_finite
    (N L E : ℕ) (k : ExactLengthCountVector E) :
    infiniteExactLengthCountVectorLaw N L E k =
      finiteExactLengthCountVectorLaw N L E k := by
  classical
  unfold infiniteExactLengthCountVectorLaw
    finiteExactLengthCountVectorLaw
  rw [infiniteExactLengthCountVectorEvent_eq_preimage,
    ← Measure.map_apply
      (measurable_restrictToFinite (markedCylinderCutoff N L E))
      (measurableSet_finiteExactLengthCountVectorEvent N L E k),
    map_infiniteRademacherMeasure_restrictToFinite]
  simp only [finiteExactLengthCountVectorEvent]
  rw [finiteRademacherMeasure_event_eq_uniformEventProbability,
    ENNReal.toReal_ofReal]
  apply Rat.cast_nonneg.mpr
  unfold uniformEventProbability
  positivity

theorem infiniteRetainedExactLengthCountVectorLaw_eq_finite
    (N L E : ℕ) (k : ExactLengthCountVector E) :
    infiniteRetainedExactLengthCountVectorLaw N L E k =
      finiteRetainedExactLengthCountVectorLaw N L E k := by
  classical
  unfold infiniteRetainedExactLengthCountVectorLaw
    finiteRetainedExactLengthCountVectorLaw
  rw [infiniteRetainedExactLengthCountVectorEvent_eq_preimage,
    ← Measure.map_apply
      (measurable_restrictToFinite (markedCylinderCutoff N L E))
      (measurableSet_finiteRetainedExactLengthCountVectorEvent
        N L E k),
    map_infiniteRademacherMeasure_restrictToFinite]
  simp only [finiteRetainedExactLengthCountVectorEvent]
  rw [finiteRademacherMeasure_event_eq_uniformEventProbability,
    ENNReal.toReal_ofReal]
  apply Rat.cast_nonneg.mpr
  unfold uniformEventProbability
  positivity

/-! ## Coupling the complete and retained vectors -/

/--
Event that at least one removed start carries one of the marks
`0, ..., E`.
-/
def infiniteRemovedExactLengthEvent
    (N L E : ℕ) : Set InfiniteSample :=
  {ω | ∃ e ∈ Finset.range (E + 1),
    ∃ x ∈ removedExactLengthStarts N L E,
      ExactLengthEvent (infiniteValueBit ω) x
        (excessRowCount L e)}

theorem infiniteRemovedExactLengthEvent_eq_biUnion
    (N L E : ℕ) :
    infiniteRemovedExactLengthEvent N L E =
      ⋃ e ∈ Finset.range (E + 1),
        ⋃ x ∈ removedExactLengthStarts N L E,
          infiniteExactLengthEvent x (excessRowCount L e) := by
  ext ω
  simp [infiniteRemovedExactLengthEvent, infiniteExactLengthEvent]

theorem measurableSet_infiniteRemovedExactLengthEvent
    (N L E : ℕ) :
    MeasurableSet (infiniteRemovedExactLengthEvent N L E) := by
  rw [infiniteRemovedExactLengthEvent_eq_biUnion]
  exact MeasurableSet.iUnion fun e ↦
    MeasurableSet.iUnion fun _ ↦
      MeasurableSet.iUnion fun x ↦
        MeasurableSet.iUnion fun _ ↦
          measurableSet_infiniteExactLengthEvent x
            (excessRowCount L e)

/--
If no removed exact-length event occurs, the complete and retained vectors
are literally equal.
-/
theorem infiniteExactLengthCountVector_eq_retained_of_no_removed
    {N L E : ℕ} {ω : InfiniteSample}
    (hno : ω ∉ infiniteRemovedExactLengthEvent N L E) :
    infiniteExactLengthCountVector N L E ω =
      infiniteRetainedExactLengthCountVector N L E ω := by
  classical
  funext e
  unfold infiniteExactLengthCountVector
    infiniteRetainedExactLengthCountVector
    infiniteExactLengthCountVectorOn
  symm
  apply Finset.sum_subset
    (retainedMarkedStarts_subset_dyadicBlock N L E)
  intro x hxBlock hxNotRetained
  have hxRemoved : x ∈ removedExactLengthStarts N L E := by
    by_contra hxNotRemoved
    exact hxNotRetained
      (mem_retainedMarkedStarts.mpr ⟨hxBlock, hxNotRemoved⟩)
  rw [if_neg]
  intro hExact
  apply hno
  exact ⟨e.1, Finset.mem_range.mpr e.2,
    x, hxRemoved, hExact⟩

theorem infiniteCountVector_disagreement_subset_removed
    (N L E : ℕ) :
    {ω |
      infiniteExactLengthCountVector N L E ω ≠
        infiniteRetainedExactLengthCountVector N L E ω} ⊆
      infiniteRemovedExactLengthEvent N L E := by
  intro ω hne
  by_contra hno
  exact hne
    (infiniteExactLengthCountVector_eq_retained_of_no_removed hno)

/--
The source probability of any complete/retained vector disagreement is at
most the literal double sum appearing in Lemma 14.8.
-/
theorem infiniteRemovedExactLengthEvent_measureReal_le_mass
    (N L E : ℕ) :
    infiniteRademacherMeasure.real
        (infiniteRemovedExactLengthEvent N L E) ≤
      totalRemovedInfiniteExactLengthProbability N L E := by
  classical
  have hmeasure :
      infiniteRademacherMeasure
          (infiniteRemovedExactLengthEvent N L E) ≤
        ∑ e ∈ Finset.range (E + 1),
          ∑ x ∈ removedExactLengthStarts N L E,
            infiniteRademacherMeasure
              (infiniteExactLengthEvent x
                (excessRowCount L e)) := by
    rw [infiniteRemovedExactLengthEvent_eq_biUnion]
    calc
      infiniteRademacherMeasure
          (⋃ e ∈ Finset.range (E + 1),
            ⋃ x ∈ removedExactLengthStarts N L E,
              infiniteExactLengthEvent x (excessRowCount L e)) ≤
          ∑ e ∈ Finset.range (E + 1),
            infiniteRademacherMeasure
              (⋃ x ∈ removedExactLengthStarts N L E,
                infiniteExactLengthEvent x
                  (excessRowCount L e)) :=
        measure_biUnion_finset_le (Finset.range (E + 1)) _
      _ ≤
          ∑ e ∈ Finset.range (E + 1),
            ∑ x ∈ removedExactLengthStarts N L E,
              infiniteRademacherMeasure
                (infiniteExactLengthEvent x
                  (excessRowCount L e)) := by
        apply Finset.sum_le_sum
        intro e _
        exact measure_biUnion_finset_le
          (removedExactLengthStarts N L E)
          (fun x ↦
            infiniteExactLengthEvent x (excessRowCount L e))
  have hfinite :
      (∑ e ∈ Finset.range (E + 1),
        ∑ x ∈ removedExactLengthStarts N L E,
          infiniteRademacherMeasure
            (infiniteExactLengthEvent x
              (excessRowCount L e))) ≠ ∞ := by
    exact ENNReal.sum_ne_top.2 fun e _ ↦
      ENNReal.sum_ne_top.2 fun x _ ↦
        measure_ne_top infiniteRademacherMeasure
          (infiniteExactLengthEvent x (excessRowCount L e))
  have hreal := ENNReal.toReal_mono hfinite hmeasure
  calc
    infiniteRademacherMeasure.real
        (infiniteRemovedExactLengthEvent N L E) ≤
      (∑ e ∈ Finset.range (E + 1),
        ∑ x ∈ removedExactLengthStarts N L E,
          infiniteRademacherMeasure
            (infiniteExactLengthEvent x
              (excessRowCount L e))).toReal :=
        hreal
    _ =
      totalRemovedInfiniteExactLengthProbability N L E := by
        unfold totalRemovedInfiniteExactLengthProbability
          infiniteExactLengthProbability
        rw [ENNReal.toReal_sum]
        · apply Finset.sum_congr rfl
          intro e _
          rw [ENNReal.toReal_sum]
          intro x hx
          exact measure_ne_top infiniteRademacherMeasure
            (infiniteExactLengthEvent x (excessRowCount L e))
        · intro e _
          exact ENNReal.sum_ne_top.2 fun x _ ↦
            measure_ne_top infiniteRademacherMeasure
              (infiniteExactLengthEvent x
                (excessRowCount L e))

/--
Pointwise coupling inequality for the joint count-vector law.
-/
theorem abs_infiniteExactLengthCountVectorLaw_sub_retained_le_mass
    (N L E : ℕ) (k : ExactLengthCountVector E) :
    |infiniteExactLengthCountVectorLaw N L E k -
        infiniteRetainedExactLengthCountVectorLaw N L E k| ≤
      totalRemovedInfiniteExactLengthProbability N L E := by
  let A := infiniteExactLengthCountVectorEvent N L E k
  let B := infiniteRetainedExactLengthCountVectorEvent N L E k
  let D :=
    {ω |
      infiniteExactLengthCountVector N L E ω ≠
        infiniteRetainedExactLengthCountVector N L E ω}
  have hsymm : A ∆ B ⊆ D := by
    intro ω hω
    rcases hω with hω | hω
    · intro heq
      exact hω.2 (by
        change infiniteRetainedExactLengthCountVector N L E ω = k
        rw [← heq]
        exact hω.1)
    · intro heq
      exact hω.2 (by
        change infiniteExactLengthCountVector N L E ω = k
        rw [heq]
        exact hω.1)
  have hD :
      D ⊆ infiniteRemovedExactLengthEvent N L E :=
    infiniteCountVector_disagreement_subset_removed N L E
  calc
    |infiniteExactLengthCountVectorLaw N L E k -
        infiniteRetainedExactLengthCountVectorLaw N L E k| =
      |infiniteRademacherMeasure.real A -
        infiniteRademacherMeasure.real B| := rfl
    _ ≤ infiniteRademacherMeasure.real (A ∆ B) :=
      abs_measureReal_sub_le_measureReal_symmDiff
        (measurableSet_infiniteExactLengthCountVectorEvent
          N L E k).nullMeasurableSet
        (measurableSet_infiniteRetainedExactLengthCountVectorEvent
          N L E k).nullMeasurableSet
    _ ≤ infiniteRademacherMeasure.real D :=
      measureReal_mono hsymm
    _ ≤ infiniteRademacherMeasure.real
        (infiniteRemovedExactLengthEvent N L E) :=
      measureReal_mono hD
    _ ≤ totalRemovedInfiniteExactLengthProbability N L E :=
      infiniteRemovedExactLengthEvent_measureReal_le_mass N L E

end

end ExactLengthCountVectorTransfer
end PaperC
