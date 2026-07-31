import PaperC.Probability.MixedLengthAffine

/-!
# Almost-sure exact-length decomposition: deterministic core

This module isolates the deterministic statement used immediately after
Lemma 14.4.  If a start of length at least `L` eventually changes value, then
there is a unique excess `e` for which the exact-length event with
`qₑ = L + e + 1` rows occurs.

The result is stated for an arbitrary bit-valued sequence.  The unrestricted
Rademacher model and the almost-sure specialization are supplied separately.
-/

namespace PaperC
namespace ExactLengthDecomposition

open MixedLengthAffine

/-- The sequence eventually differs from its value at `x`. -/
def TailChangesAt (g : ℕ → F₂) (x : ℕ) : Prop :=
  ∃ n : ℕ, x ≤ n ∧ g n ≠ g x

/-- Set of excess lengths whose exact-run event occurs. -/
def exactExcessSet (g : ℕ → F₂) (x L : ℕ) : Set ℕ :=
  {e | ExactLengthEvent g x (excessRowCount L e)}

/-- Over `F₂`, two bits are distinct exactly when their sum is one. -/
theorem add_eq_one_iff_ne (a b : F₂) :
    a + b = 1 ↔ a ≠ b := by
  revert a b
  decide

/--
An exact-length event with excess `e` is in particular a start of length
at least `L`.
-/
theorem exactLengthEvent_start
    {g : ℕ → F₂} {x L e : ℕ}
    (hExact :
      ExactLengthEvent g x (excessRowCount L e)) :
    StartEvent g x L := by
  refine ⟨hExact.1, ?_⟩
  intro j hj
  by_cases hj0 : j = 0
  · simp [hj0]
  · exact
      (hExact.2.1 j (Nat.zero_lt_of_ne_zero hj0) (by
        simp only [excessRowCount]
        omega)).symm

/-- An exact-length event supplies an explicit later change. -/
theorem exactLengthEvent_tailChangesAt
    {g : ℕ → F₂} {x L e : ℕ}
    (hExact :
      ExactLengthEvent g x (excessRowCount L e)) :
    TailChangesAt g x := by
  refine ⟨x + (excessRowCount L e - 1), by omega, ?_⟩
  exact ((add_eq_one_iff_ne _ _).mp hExact.2.2).symm

/--
The deterministic inclusion used for de-truncating the marked process: an
exact mark `e > E` contains a start of length `L + E + 1`.
-/
theorem exactLengthEvent_start_longer_of_excess_gt
    {g : ℕ → F₂} {x L e E : ℕ} (hEe : E < e)
    (hExact :
      ExactLengthEvent g x (excessRowCount L e)) :
    StartEvent g x (L + E + 1) := by
  refine ⟨hExact.1, ?_⟩
  intro j hj
  by_cases hj0 : j = 0
  · simp [hj0]
  · exact
      (hExact.2.1 j (Nat.zero_lt_of_ne_zero hj0) (by
        simp only [excessRowCount]
        omega)).symm

/--
Existence of an exact excess length.  The proof chooses the first offset at
which the sequence differs from its value at the start.
-/
theorem exists_exactLengthEvent_of_start_of_tailChangesAt
    {g : ℕ → F₂} {x L : ℕ}
    (hStart : StartEvent g x L)
    (hChange : TailChangesAt g x) :
    ∃ e : ℕ, ExactLengthEvent g x (excessRowCount L e) := by
  obtain ⟨n, hxn, hn⟩ := hChange
  have hOffset :
      ∃ d : ℕ, g (x + d) ≠ g x := by
    refine ⟨n - x, ?_⟩
    simpa [Nat.add_sub_of_le hxn] using hn
  let d : ℕ := Nat.find hOffset
  have hdChange : g (x + d) ≠ g x :=
    Nat.find_spec hOffset
  have hLd : L ≤ d := by
    by_contra h
    have hdL : d < L := Nat.lt_of_not_ge h
    exact hdChange (hStart.2 d hdL)
  let e : ℕ := d - L
  have hLe : L + e = d := by
    dsimp only [e]
    exact Nat.add_sub_of_le hLd
  refine ⟨e, hStart.1, ?_, ?_⟩
  · intro j hjPos hjLast
    have hjd : j < d := by
      simp only [excessRowCount] at hjLast
      omega
    have hnot : ¬g (x + j) ≠ g x :=
      Nat.find_min hOffset hjd
    exact (not_ne_iff.mp hnot).symm
  · rw [add_eq_one_iff_ne]
    simpa [excessRowCount, hLe] using hdChange.symm

/-- Two exact excess lengths for the same start are equal. -/
theorem exactLengthEvent_excess_unique
    {g : ℕ → F₂} {x L e f : ℕ} (hL : 1 ≤ L)
    (he : ExactLengthEvent g x (excessRowCount L e))
    (hf : ExactLengthEvent g x (excessRowCount L f)) :
    e = f := by
  by_contra hef
  rcases lt_or_gt_of_ne hef with hefLt | hfeLt
  · have heNe :
        g x ≠ g (x + (excessRowCount L e - 1)) :=
      (add_eq_one_iff_ne _ _).mp he.2.2
    have hfMiddle :
        g x = g (x + (L + e)) :=
      hf.2.1 (L + e) (by omega) (by
        simp only [excessRowCount]
        omega)
    apply heNe
    simpa [excessRowCount] using hfMiddle
  · have hfNe :
        g x ≠ g (x + (excessRowCount L f - 1)) :=
      (add_eq_one_iff_ne _ _).mp hf.2.2
    have heMiddle :
        g x = g (x + (L + f)) :=
      he.2.1 (L + f) (by omega) (by
        simp only [excessRowCount]
        omega)
    apply hfNe
    simpa [excessRowCount] using heMiddle

/--
Source-level form of the identity
`J_{x,L} = ∑_{e ≥ 0} K_{x,e}`:
when the run changes eventually, a start occurs exactly when there is a
unique exact excess length.
-/
theorem startEvent_iff_existsUnique_exactLengthEvent
    {g : ℕ → F₂} {x L : ℕ} (hL : 1 ≤ L)
    (hChange : TailChangesAt g x) :
    StartEvent g x L ↔
      ∃! e : ℕ, ExactLengthEvent g x (excessRowCount L e) := by
  constructor
  · intro hStart
    obtain ⟨e, he⟩ :=
      exists_exactLengthEvent_of_start_of_tailChangesAt
        hStart hChange
    refine ⟨e, he, ?_⟩
    intro f hf
    exact exactLengthEvent_excess_unique hL hf he
  · rintro ⟨e, he, _⟩
    exact exactLengthEvent_start he

/--
Cardinal form of `J_{x,L} = ∑ₑ K_{x,e}` on the active branch: under
eventual change, a start activates exactly one excess length.
-/
theorem ncard_exactExcessSet_of_start
    {g : ℕ → F₂} {x L : ℕ} (hL : 1 ≤ L)
    (hChange : TailChangesAt g x) (hStart : StartEvent g x L) :
    (exactExcessSet g x L).ncard = 1 := by
  classical
  obtain ⟨e, he, hunique⟩ :=
    (startEvent_iff_existsUnique_exactLengthEvent
      hL hChange).mp hStart
  have hset : exactExcessSet g x L = {e} := by
    ext f
    constructor
    · intro hf
      have hfe : f = e := hunique f hf
      simp [hfe]
    · intro hf
      have hfe : f = e := Set.mem_singleton_iff.mp hf
      simpa [hfe, exactExcessSet] using he
  simp [hset]

/--
Cardinal form of `J_{x,L} = ∑ₑ K_{x,e}` on the inactive branch: without a
start, no exact excess length is active.
-/
theorem ncard_exactExcessSet_of_not_start
    {g : ℕ → F₂} {x L : ℕ} (hStart : ¬ StartEvent g x L) :
    (exactExcessSet g x L).ncard = 0 := by
  classical
  have hset : exactExcessSet g x L = ∅ := by
    ext e
    constructor
    · intro he
      exact False.elim (hStart (exactLengthEvent_start he))
    · intro he
      simp at he
  simp [hset]

end ExactLengthDecomposition
end PaperC
