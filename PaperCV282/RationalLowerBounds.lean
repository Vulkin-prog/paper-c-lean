import PaperCV282.HostRankMass
import PaperC.Affine.RationalChannelCode

/-!
# Exact-unit lower bounds for the two rational families

The codes of the channels of slopes two and three-halves are subspaces
of the actual homogeneous relation space. The argument does not require
that the canonical selector choose these channels.
-/

namespace PaperC.V282.RationalLowerBounds

open Affine Affine.RationalChannelCode HostRankMass
open scoped BigOperators

noncomputable section

/-- All exact units of the channel of slope two, including `L=0`. -/
theorem channelCells_two_one_zero (L : ℕ) :
    channelCells L 2 1 0 =
      (Finset.range ((L + 1) / 2)).image (fun k : ℕ => ((k : ℤ), 2 * (k : ℤ))) := by
  ext ⟨i, j⟩
  simp only [mem_channelCells, mem_offsetBox, OnChannel, Nat.cast_ofNat,
    Finset.mem_image, Finset.mem_range, Prod.mk.injEq]
  constructor
  · intro h
    refine ⟨i.toNat, ?_, ?_, ?_⟩ <;> omega
  · rintro ⟨k, hk, hfst, hsnd⟩
    simp only [← hfst, ← hsnd]
    omega

/-- The half-length multiplicity in equation (3.23). -/
theorem card_channelCells_two_one_zero (L : ℕ) :
    (channelCells L 2 1 0).card = (L + 1) / 2 := by
  rw [channelCells_two_one_zero, Finset.card_image_of_injective]
  · simp
  · intro k j h
    have hfst := congrArg Prod.fst h
    change (k : ℤ) = j at hfst
    exact_mod_cast hfst

/-- All exact units of the channel of slope three-halves, including `L=0`. -/
theorem channelCells_three_two_zero (L : ℕ) :
    channelCells L 3 2 0 =
      (Finset.range ((L + 2) / 3)).image (fun k : ℕ => (2 * (k : ℤ), 3 * (k : ℤ))) := by
  ext ⟨i, j⟩
  simp only [mem_channelCells, mem_offsetBox, OnChannel, Nat.cast_ofNat,
    Finset.mem_image, Finset.mem_range, Prod.mk.injEq]
  constructor
  · intro h
    refine ⟨i.toNat / 2, ?_, ?_, ?_⟩ <;> omega
  · rintro ⟨k, hk, hfst, hsnd⟩
    simp only [← hfst, ← hsnd]
    omega

/-- The one-third multiplicity in equation (3.22). -/
theorem card_channelCells_three_two_zero (L : ℕ) :
    (channelCells L 3 2 0).card = (L + 2) / 3 := by
  rw [channelCells_three_two_zero, Finset.card_image_of_injective]
  · simp
  · intro k j h
    have hfst := congrArg Prod.fst h
    change 2 * (k : ℤ) = 2 * (j : ℤ) at hfst
    omega

/-- Any exact channel supplies a lower bound on the full relation dimension. -/
theorem channelMultiplicity_sub_one_le_relationRho
    {K x y L a b : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hheight : h = (b : ℤ) * y - (a : ℤ) * x) :
    (channelCells L a b h).card - 1 ≤ relationRho (twoStartSystem K x y L) := by
  rw [← card_rationalChannelUnits_eq_channelCells,
    ← finrank_rationalCode_all ha hb hx hy hheight]
  exact Submodule.finrank_le _

/-- The channel `(t,2t)` already contains the lower-bound code in (3.23). -/
theorem half_length_sub_one_le_relationRho
    (K L t : ℕ) (ht : 2 ≤ t) :
    (L + 1) / 2 - 1 ≤ relationRho (twoStartSystem K t (2 * t) L) := by
  have hcode := channelMultiplicity_sub_one_le_relationRho (K := K) (L := L)
    (x := t) (y := 2 * t)
    (a := 2) (b := 1) (h := 0) (by omega) (by omega) ht (by omega) (by push_cast; ring)
  simpa only [card_channelCells_two_one_zero] using hcode

/-- The channel `(2t,3t)` already contains the lower-bound code in (3.22). -/
theorem third_length_sub_one_le_relationRho
    (K L t : ℕ) (ht : 1 ≤ t) :
    (L + 2) / 3 - 1 ≤ relationRho (twoStartSystem K (2 * t) (3 * t) L) := by
  have hcode := channelMultiplicity_sub_one_le_relationRho (K := K) (L := L)
    (x := 2 * t) (y := 3 * t)
    (a := 3) (b := 2) (h := 0) (by omega) (by omega) (by omega) (by omega)
    (by push_cast; ring)
  simpa only [card_channelCells_three_two_zero] using hcode

/-- Reversing a zero-height channel preserves its exact multiplicity. -/
theorem card_channelCells_zero_swap (L a b : ℕ) :
    (channelCells L a b 0).card = (channelCells L b a 0).card := by
  apply Finset.card_bij (fun xy _ => xy.swap)
  · rintro ⟨i, j⟩ hxy
    simp only [mem_channelCells, mem_offsetBox, OnChannel, Prod.swap_prod_mk] at *
    omega
  · intro xy _ zw _ heq
    exact Prod.swap_injective heq
  · rintro ⟨i, j⟩ hxy
    refine ⟨(j, i), ?_, rfl⟩
    simp only [mem_channelCells, mem_offsetBox, OnChannel] at *
    omega

/-- The reversed half-length family contributes the same lower-bound dimension. -/
theorem half_length_sub_one_le_relationRho_reverse
    (K L t : ℕ) (ht : 2 ≤ t) :
    (L + 1) / 2 - 1 ≤ relationRho (twoStartSystem K (2 * t) t L) := by
  have hcode := channelMultiplicity_sub_one_le_relationRho (K := K) (L := L)
    (x := 2 * t) (y := t) (a := 1) (b := 2) (h := 0)
    (by omega) (by omega) (by omega) ht (by push_cast; ring)
  rw [card_channelCells_zero_swap L 1 2, card_channelCells_two_one_zero] at hcode
  exact hcode

/-- The reversed one-third family contributes the same lower-bound dimension. -/
theorem third_length_sub_one_le_relationRho_reverse
    (K L t : ℕ) (ht : 1 ≤ t) :
    (L + 2) / 3 - 1 ≤ relationRho (twoStartSystem K (3 * t) (2 * t) L) := by
  have hcode := channelMultiplicity_sub_one_le_relationRho (K := K) (L := L)
    (x := 3 * t) (y := 2 * t) (a := 2) (b := 3) (h := 0)
    (by omega) (by omega) (by omega) (by omega) (by push_cast; ring)
  rw [card_channelCells_zero_swap L 2 3, card_channelCells_three_two_zero] at hcode
  exact hcode

end
end PaperC.V282.RationalLowerBounds
