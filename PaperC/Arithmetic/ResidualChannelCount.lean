import PaperC.Arithmetic.ResidualChannelCells

/-!
# Counting residual cells on one primitive channel

This file proves the finite geometric estimate in (7.3).  Residual cells
are grouped according to the value

`Δ = h + b*j - a*i`.

The possible values lie in an interval of length
`8 * max(a,b) * (L+1)` and are all congruent to zero modulo `p`.  For a
fixed value `d`, the corresponding cells lie on the translated channel
with height `h-d`, so `ChannelCount` bounds every fiber by
`1 + (L+1)/max(a,b)`.
-/

namespace PaperC

open Finset

/-- Values of the residual expression attained by residual `p`-cells. -/
def residualChannelValues
    (L a b p : ℕ) (h : ℤ) : Finset ℤ :=
  (residualPrimeCells L a b p h).image
    (residualChannelExpression a b h)

@[simp]
theorem mem_residualChannelValues
    {L a b p : ℕ} {h d : ℤ} :
    d ∈ residualChannelValues L a b p h ↔
      ∃ cell ∈ residualPrimeCells L a b p h,
        residualChannelExpression a b h cell = d := by
  simp [residualChannelValues]

/--
The explicit interval/congruence envelope containing all residual values.
Its interval has length `8 * q * B`, with `q=max(a,b)` and `B=L+1`.
-/
def residualValueEnvelope
    (L a b p : ℕ) : Finset ℤ :=
  {d ∈
      Ico
        (-((4 * Nat.max a b * (L + 1) : ℕ) : ℤ))
        ((4 * Nat.max a b * (L + 1) : ℕ) : ℤ) |
    d ≡ 0 [ZMOD (p : ℤ)]}

@[simp]
theorem mem_residualValueEnvelope
    {L a b p : ℕ} {d : ℤ} :
    d ∈ residualValueEnvelope L a b p ↔
      -((4 * Nat.max a b * (L + 1) : ℕ) : ℤ) ≤ d ∧
      d < ((4 * Nat.max a b * (L + 1) : ℕ) : ℤ) ∧
      (p : ℤ) ∣ d := by
  simp only [residualValueEnvelope, mem_filter, mem_Ico,
    Int.modEq_zero_iff_dvd]
  tauto

/-- Every attained residual value belongs to the explicit envelope. -/
theorem residualChannelValues_subset_envelope
    {L a b p : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hm : 2 ≤ (channelCells L a b h).card) :
    residualChannelValues L a b p h ⊆
      residualValueEnvelope L a b p := by
  intro d hd
  obtain ⟨cell, hcell, rfl⟩ :=
    mem_residualChannelValues.mp hd
  have hmem := mem_residualPrimeCells.mp hcell
  have habs :=
    abs_residualChannelExpression_lt_four_mul_max
      ha hb hab hm hmem.1
  rw [abs_lt] at habs
  rw [mem_residualValueEnvelope]
  exact ⟨habs.1.le, habs.2, hmem.2.2⟩

/--
The number of possible residual values is at most
`1 + 8*q*(L+1)/p`.
-/
theorem residualValueEnvelope_card_cast_le
    (L a b p : ℕ) (hp : 0 < p) :
    ((residualValueEnvelope L a b p).card : ℚ) ≤
      1 +
        ((8 * Nat.max a b * (L + 1) : ℕ) : ℚ) / (p : ℚ) := by
  have hcount :=
    card_Ico_modEq_cast_le_div_add_one
      (-((4 * Nat.max a b * (L + 1) : ℕ) : ℤ))
      ((4 * Nat.max a b * (L + 1) : ℕ) : ℤ)
      0 (p : ℤ)
      (by exact_mod_cast hp)
      (by
        have hnonneg :
            (0 : ℤ) ≤
              ((4 * Nat.max a b * (L + 1) : ℕ) : ℤ) := by
          positivity
        omega)
  unfold residualValueEnvelope
  refine hcount.trans_eq ?_
  push_cast
  ring

/--
At a fixed residual value `d`, the relevant fiber lies on the translated
exact channel of height `h-d`.
-/
theorem residualExpression_fiber_subset_channelCells
    {L a b p : ℕ} {h d : ℤ} :
    {cell ∈ residualPrimeCells L a b p h |
        residualChannelExpression a b h cell = d} ⊆
      channelCells L a b (h - d) := by
  intro cell hcell
  simp only [mem_filter] at hcell
  rw [mem_channelCells]
  refine ⟨(mem_residualPrimeCells.mp hcell.1).1, ?_⟩
  unfold residualChannelExpression OnChannel at *
  linarith

/--
Every residual-value fiber satisfies the primitive-channel lattice count.
-/
theorem residualExpression_fiber_card_cast_le
    (L a b p : ℕ) (h d : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) :
    (({cell ∈ residualPrimeCells L a b p h |
        residualChannelExpression a b h cell = d}.card : ℕ) : ℚ) ≤
      1 + (((L + 1 : ℕ) : ℚ) / (Nat.max a b : ℚ)) := by
  have hmono :
      {cell ∈ residualPrimeCells L a b p h |
          residualChannelExpression a b h cell = d}.card ≤
        (channelCells L a b (h - d)).card :=
    card_mono residualExpression_fiber_subset_channelCells
  have hmonoQ :
      (({cell ∈ residualPrimeCells L a b p h |
          residualChannelExpression a b h cell = d}.card : ℕ) : ℚ) ≤
        ((channelCells L a b (h - d)).card : ℚ) := by
    exact_mod_cast hmono
  refine hmonoQ.trans ?_
  have hchannel :=
    channelCells_card_cast_le_maxStep
      L a b ha hb hab (h - d)
  convert hchannel using 1
  push_cast
  ring

/--
Finite form of the residual-cell estimate (7.3).

The first factor counts the possible nonzero multiples of `p` in the
geometric value range; the second is the maximal size of a translated
primitive-channel fiber.
-/
theorem residualPrimeCells_card_cast_le
    {L a b p : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hp : 0 < p)
    (hm : 2 ≤ (channelCells L a b h).card) :
    ((residualPrimeCells L a b p h).card : ℚ) ≤
      (1 +
          ((8 * Nat.max a b * (L + 1) : ℕ) : ℚ) / (p : ℚ)) *
        (1 + (((L + 1 : ℕ) : ℚ) / (Nat.max a b : ℚ))) := by
  let s := residualPrimeCells L a b p h
  let f : ℤ × ℤ → ℤ := residualChannelExpression a b h
  let t := residualValueEnvelope L a b p
  have hmaps : s.toSet.MapsTo f t := by
    intro cell hcell
    have hvalue :
        f cell ∈ residualChannelValues L a b p h := by
      rw [mem_residualChannelValues]
      exact ⟨cell, hcell, rfl⟩
    exact residualChannelValues_subset_envelope ha hb hab hm hvalue
  have hcard :
      s.card =
        ∑ d ∈ t, ({cell ∈ s | f cell = d}).card :=
    card_eq_sum_card_fiberwise hmaps
  have hfiber :
      ∀ d ∈ t,
        ((({cell ∈ s | f cell = d}).card : ℕ) : ℚ) ≤
          1 + (((L + 1 : ℕ) : ℚ) / (Nat.max a b : ℚ)) := by
    intro d _hd
    simpa only [s, f] using
      residualExpression_fiber_card_cast_le
        L a b p h d ha hb hab
  have hvalueCount :
      ((t.card : ℕ) : ℚ) ≤
        1 +
          ((8 * Nat.max a b * (L + 1) : ℕ) : ℚ) / (p : ℚ) := by
    simpa only [t] using
      residualValueEnvelope_card_cast_le L a b p hp
  have hfiberNonneg :
      0 ≤ 1 + (((L + 1 : ℕ) : ℚ) / (Nat.max a b : ℚ)) := by
    positivity
  calc
    ((residualPrimeCells L a b p h).card : ℚ) =
        ∑ d ∈ t,
          ((({cell ∈ s | f cell = d}).card : ℕ) : ℚ) := by
      rw [show residualPrimeCells L a b p h = s by rfl, hcard,
        Nat.cast_sum]
    _ ≤ ∑ _d ∈ t,
          (1 + (((L + 1 : ℕ) : ℚ) / (Nat.max a b : ℚ))) := by
      exact sum_le_sum hfiber
    _ = ((t.card : ℕ) : ℚ) *
          (1 + (((L + 1 : ℕ) : ℚ) / (Nat.max a b : ℚ))) := by
      simp
      ring
    _ ≤
        (1 +
            ((8 * Nat.max a b * (L + 1) : ℕ) : ℚ) / (p : ℚ)) *
          (1 + (((L + 1 : ℕ) : ℚ) / (Nat.max a b : ℚ))) := by
      exact mul_le_mul_of_nonneg_right hvalueCount hfiberNonneg

end PaperC
