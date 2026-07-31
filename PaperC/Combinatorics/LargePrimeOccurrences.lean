import PaperC.Affine.RelationalPrimeAssignment

set_option maxHeartbeats 1200000

/-!
# Occurrences of one large prime in two start blocks

For a pair of starts, an occurrence is one of the `L+1` complete vertices
in either block.  This module records the first local fact used in Section 6:
a prime `p > L+1` can occur with odd valuation at most once in each block.
Thus its total occurrence set has cardinality at most two.  A two-element
set joins opposite blocks, while a singleton is a pin.

No quotient graph is constructed here.
-/

namespace PaperC
namespace LargePrimeOccurrences

open Affine

noncomputable section

/-- The disjoint union of complete-boundary occurrences in the two blocks. -/
abbrev Occurrence (L : ℕ) :=
  Sum (Fin (L + 1)) (Fin (L + 1))

/-- Occurrences at which the `p`-coordinate of the parity vector is one. -/
def primeOccurrences
    (x y L p : ℕ) : Finset (Occurrence L) :=
  Finset.univ.filter fun v ↦
    parityVec (twoStartCompleteVertexLabel x y L v) p = 1

@[simp]
theorem mem_primeOccurrences
    {x y L p : ℕ} {v : Occurrence L} :
    v ∈ primeOccurrences x y L p ↔
      parityVec (twoStartCompleteVertexLabel x y L v) p = 1 := by
  simp [primeOccurrences]

/-- Membership in the occurrence set gives a nonzero parity coordinate. -/
theorem parityVec_ne_zero_of_mem
    {x y L p : ℕ} {v : Occurrence L}
    (hv : v ∈ primeOccurrences x y L p) :
    parityVec (twoStartCompleteVertexLabel x y L v) p ≠ 0 := by
  have hone := mem_primeOccurrences.mp hv
  rw [hone]
  exact one_ne_zero

/--
There is at most one large-prime occurrence in the left start block.
The primality hypothesis is retained to match the Section 6 interface;
the stronger local uniqueness lemma only needs the size inequality.
-/
theorem inl_eq_of_mem
    {x y L p : ℕ}
    (hx : 1 ≤ x) (_hp : p.Prime) (hpL : L + 1 < p)
    {v w : Fin (L + 1)}
    (hv : Sum.inl v ∈ primeOccurrences x y L p)
    (hw : Sum.inl w ∈ primeOccurrences x y L p) :
    v = w := by
  apply
    Affine.RelationalPrimeAssignment.parityVec_ne_zero_unique_in_start
      hx hpL
  · exact parityVec_ne_zero_of_mem hv
  · exact parityVec_ne_zero_of_mem hw

/-- There is at most one large-prime occurrence in the right start block. -/
theorem inr_eq_of_mem
    {x y L p : ℕ}
    (hy : 1 ≤ y) (_hp : p.Prime) (hpL : L + 1 < p)
    {v w : Fin (L + 1)}
    (hv : Sum.inr v ∈ primeOccurrences x y L p)
    (hw : Sum.inr w ∈ primeOccurrences x y L p) :
    v = w := by
  apply
    Affine.RelationalPrimeAssignment.parityVec_ne_zero_unique_in_start
      hy hpL
  · exact parityVec_ne_zero_of_mem hv
  · exact parityVec_ne_zero_of_mem hw

/-- The block containing an occurrence. -/
def occurrenceBlock {L : ℕ} : Occurrence L → Bool
  | Sum.inl _ => false
  | Sum.inr _ => true

/--
On the occurrence set of a prime above `L+1`, the block map is injective:
each of the two blocks supplies at most one occurrence.
-/
theorem occurrenceBlock_injOn
    {x y L p : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hp : p.Prime) (hpL : L + 1 < p) :
    Set.InjOn occurrenceBlock
      (↑(primeOccurrences x y L p) : Set (Occurrence L)) := by
  intro v hv w hw hblock
  cases v with
  | inl v =>
      cases w with
      | inl w =>
          exact congrArg Sum.inl
            (inl_eq_of_mem hx hp hpL hv hw)
      | inr w =>
          simp [occurrenceBlock] at hblock
  | inr v =>
      cases w with
      | inl w =>
          simp [occurrenceBlock] at hblock
      | inr w =>
          exact congrArg Sum.inr
            (inr_eq_of_mem hy hp hpL hv hw)

/-- A large prime has at most two occurrences across the two blocks. -/
theorem card_primeOccurrences_le_two
    {x y L p : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hp : p.Prime) (hpL : L + 1 < p) :
    (primeOccurrences x y L p).card ≤ 2 := by
  have hcard :
      ((primeOccurrences x y L p).image occurrenceBlock).card =
        (primeOccurrences x y L p).card :=
    Finset.card_image_of_injOn
      (occurrenceBlock_injOn hx hy hp hpL)
  calc
    (primeOccurrences x y L p).card =
        ((primeOccurrences x y L p).image occurrenceBlock).card :=
      hcard.symm
    _ ≤ (Finset.univ : Finset Bool).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = 2 := by decide

/-- Two occurrences lie in opposite blocks. -/
def InOppositeBlocks {L : ℕ}
    (v w : Occurrence L) : Prop :=
  (∃ i j, v = Sum.inl i ∧ w = Sum.inr j) ∨
    (∃ i j, v = Sum.inr i ∧ w = Sum.inl j)

/--
Any two distinct large-prime occurrences must belong to opposite blocks.
-/
theorem inOppositeBlocks_of_mem_of_ne
    {x y L p : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hp : p.Prime) (hpL : L + 1 < p)
    {v w : Occurrence L}
    (hv : v ∈ primeOccurrences x y L p)
    (hw : w ∈ primeOccurrences x y L p)
    (hvw : v ≠ w) :
    InOppositeBlocks v w := by
  cases v with
  | inl v =>
      cases w with
      | inl w =>
          have heq := inl_eq_of_mem hx hp hpL hv hw
          exact (hvw (congrArg Sum.inl heq)).elim
      | inr w =>
          exact Or.inl ⟨v, w, rfl, rfl⟩
  | inr v =>
      cases w with
      | inl w =>
          exact Or.inr ⟨v, w, rfl, rfl⟩
      | inr w =>
          have heq := inr_eq_of_mem hy hp hpL hv hw
          exact (hvw (congrArg Sum.inr heq)).elim

/--
If the prime occurs twice, its occurrence set consists of one left and one
right occurrence.
-/
theorem eq_pair_inl_inr_of_card_eq_two
    {x y L p : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hp : p.Prime) (hpL : L + 1 < p)
    (hcard : (primeOccurrences x y L p).card = 2) :
    ∃ v w : Fin (L + 1),
      primeOccurrences x y L p =
        {Sum.inl v, Sum.inr w} := by
  obtain ⟨v, w, hvw, hset⟩ :=
    Finset.card_eq_two.mp hcard
  have hv : v ∈ primeOccurrences x y L p := by
    rw [hset]
    simp
  have hw : w ∈ primeOccurrences x y L p := by
    rw [hset]
    simp
  have hopposite :=
    inOppositeBlocks_of_mem_of_ne hx hy hp hpL hv hw hvw
  rcases hopposite with
      ⟨vLeft, wRight, hv, hw⟩ |
      ⟨vRight, wLeft, hv, hw⟩
  · subst v
    subst w
    exact ⟨vLeft, wRight, hset⟩
  · subst v
    subst w
    exact
      ⟨wLeft, vRight,
        hset.trans (Finset.pair_comm _ _)⟩

/--
An occurrence is pinned by `p` when it is the unique member of the
`p`-occurrence set.
-/
def IsPin
    (x y L p : ℕ) (v : Occurrence L) : Prop :=
  primeOccurrences x y L p = {v}

/-- A singleton occurrence set is a pin, situated in one of the two blocks. -/
theorem exists_pin_of_card_eq_one
    {x y L p : ℕ}
    (hcard : (primeOccurrences x y L p).card = 1) :
    (∃ v : Fin (L + 1), IsPin x y L p (Sum.inl v)) ∨
      (∃ v : Fin (L + 1), IsPin x y L p (Sum.inr v)) := by
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcard
  cases v with
  | inl v =>
      exact Or.inl ⟨v, hv⟩
  | inr v =>
      exact Or.inr ⟨v, hv⟩

end

end LargePrimeOccurrences
end PaperC
