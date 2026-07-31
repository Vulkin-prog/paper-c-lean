import PaperC.Arithmetic.ResidualChannelCount

/-!
# Support restrictions for residual channel cells

This module records three consequences needed before summing the
single-prime estimate (7.3):

* a positive primitive channel with at least two exact cells has
  `max(a,b) ≤ L`;
* residual `p`-cells vanish beyond the explicit geometric cutoff
  `4 * max(a,b) * (L+1)`;
* every restricted family of residual cells inherits the same rational
  cardinality bound as the full family.
-/

namespace PaperC

open Finset
open Affine.RationalChannelCode

/--
Integer-cell form of the final coefficient bound in Lemma 5.1.  A positive
primitive channel containing at least two exact cells satisfies
`max(a,b) ≤ L`.
-/
theorem channel_max_le_length_of_two_cells
    {L a b : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hm : 2 ≤ (channelCells L a b h).card) :
    Nat.max a b ≤ L := by
  have hmUnits :
      2 ≤ (rationalChannelUnits L a b h).card := by
    rw [card_rationalChannelUnits_eq_channelCells]
    exact hm
  exact max_channelCoefficients_le_length ha hb hab hmUnits

/--
There are no residual `p`-cells once `p` reaches the explicit support
cutoff.  The strict inequality for every carried prime, proved in
`ResidualChannelCells`, makes the endpoint inclusive here.
-/
theorem residualPrimeCells_eq_empty_of_cutoff_le
    {L a b p : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hm : 2 ≤ (channelCells L a b h).card)
    (hp : p.Prime)
    (hcutoff : 4 * Nat.max a b * (L + 1) ≤ p) :
    residualPrimeCells L a b p h = ∅ := by
  rw [eq_empty_iff_forall_not_mem]
  intro cell hcell
  have hpLt :
      p < 4 * Nat.max a b * (L + 1) :=
    prime_lt_four_mul_max_of_mem_residualPrimeCells
      ha hb hab hm hcell hp
  omega

/-- Complete-start vertex version of the support cutoff. -/
theorem residualVertexPrimeCells_eq_empty_of_cutoff_le
    {L a b p : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hm : 2 ≤ (channelCells L a b h).card)
    (hp : p.Prime)
    (hcutoff : 4 * Nat.max a b * (L + 1) ≤ p) :
    residualVertexPrimeCells L a b p h = ∅ := by
  rw [eq_empty_iff_forall_not_mem]
  intro cell hcell
  have hpLt :
      p < 4 * Nat.max a b * (L + 1) :=
    prime_lt_four_mul_max_of_mem_residualVertexPrimeCells
      ha hb hab hm hcell hp
  omega

/--
Any subfamily of the residual cells inherits the finite estimate (7.3).
This wrapper is useful when later arguments impose extra certificate or
prime-range conditions.
-/
theorem card_cast_le_residual_bound_of_subset
    {L a b p : ℕ} {h : ℤ}
    {s : Finset (ℤ × ℤ)}
    (hs : s ⊆ residualPrimeCells L a b p h)
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hp : 0 < p)
    (hm : 2 ≤ (channelCells L a b h).card) :
    (s.card : ℚ) ≤
      (1 +
          ((8 * Nat.max a b * (L + 1) : ℕ) : ℚ) / (p : ℚ)) *
        (1 + (((L + 1 : ℕ) : ℚ) / (Nat.max a b : ℚ))) := by
  have hcard : s.card ≤ (residualPrimeCells L a b p h).card :=
    card_mono hs
  have hcardQ :
      (s.card : ℚ) ≤
        ((residualPrimeCells L a b p h).card : ℚ) := by
    exact_mod_cast hcard
  exact hcardQ.trans
    (residualPrimeCells_card_cast_le ha hb hab hp hm)

end PaperC
