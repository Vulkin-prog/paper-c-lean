import PaperC.Arithmetic.ChannelGeometry
import PaperC.Arithmetic.ChannelUniqueness
import Mathlib.Data.Finset.Card

/-!
# Canonical reduced channels

This module turns the determinant argument of Lemma 5.2 into a finite
selection API.  A candidate is a positive coprime pair `(a,b)`, bounded by a
height `H`, for which

`|b*y - a*x| < (a+b) B`.

Above the explicit determinant threshold there is at most one candidate, so
the optional canonical candidate agrees with every witness.  The final
coverage theorem shows that every primitive channel containing at least two
exact units is a candidate at height `(L+1)^A`.
-/

namespace PaperC

open Finset

/-- The integer error of the reduced channel `(a,b)` at the pair `(x,y)`. -/
def pairChannelError (x y a b : ℕ) : ℤ :=
  (b : ℤ) * (y : ℤ) - (a : ℤ) * (x : ℤ)

/-- The strict channel inequality from (5.1). -/
def SatisfiesChannelInequality
    (x y B a b : ℕ) : Prop :=
  |pairChannelError x y a b| < (((a + b) * B : ℕ) : ℤ)

instance (x y B a b : ℕ) :
    Decidable (SatisfiesChannelInequality x y B a b) :=
  by
    unfold SatisfiesChannelInequality
    infer_instance

/-- Finite set of positive reduced candidates of height at most `H`. -/
def reducedChannelCandidates
    (x y B H : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 H) ×ˢ (Finset.Icc 1 H)).filter fun c ↦
    c.1.Coprime c.2 ∧
      SatisfiesChannelInequality x y B c.1 c.2

@[simp]
theorem mem_reducedChannelCandidates
    {x y B H a b : ℕ} :
    (a, b) ∈ reducedChannelCandidates x y B H ↔
      0 < a ∧ 0 < b ∧ a ≤ H ∧ b ≤ H ∧
        a.Coprime b ∧
        SatisfiesChannelInequality x y B a b := by
  simp [reducedChannelCandidates, Nat.succ_le_iff,
    and_assoc, and_left_comm, and_comm]

/--
The exact determinant criterion implies that the finite candidate set has at
most one element.
-/
theorem card_reducedChannelCandidates_le_one
    {x y B H : ℕ} (hx : 4 * H ^ 2 * B < x) :
    (reducedChannelCandidates x y B H).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro c hc d hd
  obtain ⟨ha, hb, haH, hbH, hab, hclose⟩ :=
    mem_reducedChannelCandidates.mp hc
  obtain ⟨ha', hb', ha'H, hb'H, hab', hclose'⟩ :=
    mem_reducedChannelCandidates.mp hd
  obtain ⟨hfst, hsnd⟩ :=
    reducedChannel_unique x y B H
      c.1 c.2 d.1 d.2
      ha hb ha' hb' hab hab'
      haH hbH ha'H hb'H hx hclose hclose'
  exact Prod.ext hfst hsnd

/-- Optional canonical reduced channel, chosen from the finite candidate set. -/
noncomputable def canonicalReducedChannel?
    (x y B H : ℕ) : Option (ℕ × ℕ) :=
  if h : (reducedChannelCandidates x y B H).Nonempty then
    some h.choose
  else
    none

theorem canonicalReducedChannel?_eq_none_iff
    {x y B H : ℕ} :
    canonicalReducedChannel? x y B H = none ↔
      reducedChannelCandidates x y B H = ∅ := by
  classical
  simp [canonicalReducedChannel?, Finset.not_nonempty_iff_eq_empty]

theorem canonicalReducedChannel?_mem
    {x y B H : ℕ} {c : ℕ × ℕ}
    (hc : canonicalReducedChannel? x y B H = some c) :
    c ∈ reducedChannelCandidates x y B H := by
  classical
  unfold canonicalReducedChannel? at hc
  split at hc
  · simp only [Option.some.injEq] at hc
    subst c
    exact ‹(reducedChannelCandidates x y B H).Nonempty›.choose_spec
  · simp at hc

/--
Above the uniqueness threshold, the canonical option is exactly every
candidate witness.
-/
theorem canonicalReducedChannel?_eq_some_of_mem
    {x y B H : ℕ} (hx : 4 * H ^ 2 * B < x)
    {c : ℕ × ℕ}
    (hc : c ∈ reducedChannelCandidates x y B H) :
    canonicalReducedChannel? x y B H = some c := by
  classical
  let s := reducedChannelCandidates x y B H
  have hnonempty : s.Nonempty := ⟨c, hc⟩
  unfold canonicalReducedChannel?
  rw [dif_pos hnonempty]
  congr 1
  have hcard :=
    card_reducedChannelCandidates_le_one
      (x := x) (y := y) (B := B) (H := H) hx
  rw [Finset.card_le_one] at hcard
  exact hcard _ hnonempty.choose_spec _ hc

/-- Every allowed offset has absolute value strictly below `L+1`. -/
theorem abs_lt_length_add_one_of_mem_offsetInterval
    {L : ℕ} (hL : 0 < L) {i : ℤ}
    (hi : i ∈ offsetInterval L) :
    |i| < (L + 1 : ℕ) := by
  rw [mem_offsetInterval] at hi
  rw [abs_lt]
  constructor <;> omega

/--
A nonempty positive channel in the offset box automatically satisfies the
strict error bound `|h| < (a+b)(L+1)`.
-/
theorem abs_channelParameter_lt
    {L a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {h : ℤ} {cell : ℤ × ℤ}
    (hcell : cell ∈ channelCells L a b h) :
    |h| < (((a + b) * (L + 1) : ℕ) : ℤ) := by
  have hdata := mem_channelCells.mp hcell
  by_cases hL : L = 0
  · subst L
    have hi : cell.1 = -1 := by
      have hiBounds := (mem_offsetBox.mp hdata.1).1
      norm_num at hiBounds
      omega
    have hj : cell.2 = -1 := by
      have hjBounds := (mem_offsetBox.mp hdata.1).2
      norm_num at hjBounds
      omega
    have hchannel := hdata.2
    unfold OnChannel at hchannel
    rw [hi, hj] at hchannel
    rw [← hchannel]
    push_cast
    rw [abs_lt]
    constructor <;> nlinarith
  have hLpos : 0 < L := Nat.pos_of_ne_zero hL
  have hi :
      |cell.1| < ((L + 1 : ℕ) : ℤ) := by
    exact_mod_cast
      abs_lt_length_add_one_of_mem_offsetInterval hLpos
        (by simpa [offsetBox] using
          (Finset.mem_product.mp hdata.1).1)
  have hj :
      |cell.2| < ((L + 1 : ℕ) : ℤ) := by
    exact_mod_cast
      abs_lt_length_add_one_of_mem_offsetInterval hLpos
        (by simpa [offsetBox] using
          (Finset.mem_product.mp hdata.1).2)
  have haZ : (0 : ℤ) < (a : ℤ) := by exact_mod_cast ha
  have hbZ : (0 : ℤ) < (b : ℤ) := by exact_mod_cast hb
  have htriangle :
      |(a : ℤ) * cell.1 - (b : ℤ) * cell.2| ≤
        (a : ℤ) * |cell.1| + (b : ℤ) * |cell.2| := by
    calc
      |(a : ℤ) * cell.1 - (b : ℤ) * cell.2| ≤
          |(a : ℤ) * cell.1| + |(b : ℤ) * cell.2| :=
        abs_sub _ _
      _ = (a : ℤ) * |cell.1| + (b : ℤ) * |cell.2| := by
        rw [abs_mul, abs_mul, abs_of_pos haZ, abs_of_pos hbZ]
  rw [← hdata.2]
  calc
    |(a : ℤ) * cell.1 - (b : ℤ) * cell.2| ≤
        (a : ℤ) * |cell.1| + (b : ℤ) * |cell.2| :=
      htriangle
    _ < (a : ℤ) * (L + 1 : ℕ) +
          (b : ℤ) * (L + 1 : ℕ) :=
      add_lt_add
        (mul_lt_mul_of_pos_left hi haZ)
        (mul_lt_mul_of_pos_left hj hbZ)
    _ = (((a + b) * (L + 1) : ℕ) : ℤ) := by
      push_cast
      ring

/--
An exact unit identifies the affine channel parameter with `b*y-a*x`.
-/
theorem pairChannelError_eq_of_exact_unit
    {x y a b : ℕ} {h : ℤ} {cell : ℤ × ℤ}
    (hchannel : OnChannel a b h cell)
    (hexact :
      (a : ℤ) * ((x : ℤ) + cell.1) =
        (b : ℤ) * ((y : ℤ) + cell.2)) :
    pairChannelError x y a b = h := by
  unfold pairChannelError OnChannel at *
  linarith

/--
Every primitive channel with at least two exact units is covered by the
height-`(L+1)^A` candidate definition.  This is the finite second assertion
of Lemma 5.2.
-/
theorem channel_mem_reducedCandidates_of_two_units
    {x y L A a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hA : 1 ≤ A)
    {h : ℤ}
    (hparameter : pairChannelError x y a b = h)
    (hm : 2 ≤ (channelCells L a b h).card) :
    (a, b) ∈
      reducedChannelCandidates x y (L + 1) ((L + 1) ^ A) := by
  classical
  obtain ⟨cell₁, hcell₁, cell₂, hcell₂, hne⟩ :
      ∃ cell₁ ∈ channelCells L a b h,
        ∃ cell₂ ∈ channelCells L a b h, cell₁ ≠ cell₂ := by
    exact Finset.one_lt_card.mp hm
  have hheight :=
    channel_coefficients_le_length_of_mem
      ha hb hab hcell₁ hcell₂ hne
  have hbase : L + 1 ≤ (L + 1) ^ A := by
    calc
      L + 1 = (L + 1) ^ 1 := (pow_one _).symm
      _ ≤ (L + 1) ^ A :=
        pow_le_pow_right' (by omega) hA
  rw [mem_reducedChannelCandidates]
  refine ⟨ha, hb, hheight.1.trans (Nat.le_succ L) |>.trans hbase,
    hheight.2.trans (Nat.le_succ L) |>.trans hbase, hab, ?_⟩
  unfold SatisfiesChannelInequality
  rw [hparameter]
  exact abs_channelParameter_lt ha hb hcell₁

end PaperC
