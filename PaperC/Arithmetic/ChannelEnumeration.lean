import PaperC.Arithmetic.ChannelGeometry
import Mathlib.Data.Int.Interval

/-!
# Finite enumeration of primitive channel geometries

This file supplies the finite counting interface used in Proposition 5.4
and Lemma 5.5.  At a fixed height `q = max a b` there are at most `2q`
positive reduced pairs.  For a fixed pair `(a,b)`, all channel parameters
met by the offset box lie in one explicit integer interval of cardinality
`(a+b)L+1`.
-/

namespace PaperC

open Finset

/-- Positive coprime coefficient pairs whose height is exactly `q`. -/
def reducedRatiosAtHeight (q : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 q) ×ˢ (Icc 1 q)).filter fun c ↦
    c.1.Coprime c.2 ∧ Nat.max c.1 c.2 = q

@[simp]
theorem mem_reducedRatiosAtHeight
    {q a b : ℕ} :
    (a, b) ∈ reducedRatiosAtHeight q ↔
      0 < a ∧ 0 < b ∧ a.Coprime b ∧ Nat.max a b = q := by
  simp only [reducedRatiosAtHeight, mem_filter, mem_product, mem_Icc]
  constructor
  · rintro ⟨⟨⟨ha, _haq⟩, ⟨hb, _hbq⟩⟩, hab, hmax⟩
    exact ⟨by omega, by omega, hab, hmax⟩
  · rintro ⟨ha, hb, hab, hmax⟩
    have haq : a ≤ q := by
      rw [← hmax]
      exact Nat.le_max_left _ _
    have hbq : b ≤ q := by
      rw [← hmax]
      exact Nat.le_max_right _ _
    exact ⟨⟨⟨by omega, haq⟩, ⟨by omega, hbq⟩⟩, hab, hmax⟩

/--
Every positive pair of height `q` lies on one of the two boundary faces of
the square `[1,q]²`.
-/
theorem reducedRatiosAtHeight_subset_faces (q : ℕ) :
    reducedRatiosAtHeight q ⊆
      ((Icc 1 q) ×ˢ {q}) ∪ ({q} ×ˢ (Icc 1 q)) := by
  intro c hc
  obtain ⟨ha, hb, _hab, hmax⟩ :=
    mem_reducedRatiosAtHeight.mp hc
  have haq : c.1 ≤ q := by
    rw [← hmax]
    exact Nat.le_max_left _ _
  have hbq : c.2 ≤ q := by
    rw [← hmax]
    exact Nat.le_max_right _ _
  by_cases hfirst : c.1 = q
  · rw [mem_union]
    right
    rw [mem_product]
    exact ⟨by simp [hfirst], by
      rw [mem_Icc]
      exact ⟨by omega, hbq⟩⟩
  · have hsecond : c.2 = q := by
      by_cases hle : c.1 ≤ c.2
      · calc
          c.2 = Nat.max c.1 c.2 :=
            (Nat.max_eq_right hle).symm
          _ = q := hmax
      · have hrev : c.2 ≤ c.1 := le_of_not_ge hle
        have heq : c.1 = q := by
          calc
            c.1 = Nat.max c.1 c.2 :=
              (Nat.max_eq_left hrev).symm
            _ = q := hmax
        exact (hfirst heq).elim
    rw [mem_union]
    left
    rw [mem_product]
    exact ⟨by
      rw [mem_Icc]
      exact ⟨by omega, haq⟩, by simp [hsecond]⟩

/-- The `O(q)` reduced-ratio count, with explicit constant `2`. -/
theorem card_reducedRatiosAtHeight_le (q : ℕ) :
    (reducedRatiosAtHeight q).card ≤ 2 * q := by
  calc
    (reducedRatiosAtHeight q).card ≤
        (((Icc 1 q) ×ˢ {q}) ∪
          ({q} ×ˢ (Icc 1 q))).card :=
      card_le_card (reducedRatiosAtHeight_subset_faces q)
    _ ≤ ((Icc 1 q) ×ˢ {q}).card +
          ({q} ×ˢ (Icc 1 q)).card :=
      card_union_le _ _
    _ = 2 * q := by
      simp [Nat.card_Icc]
      omega

/--
The finite set of affine parameters attained by cells of the offset box.
-/
def channelHeights (L a b : ℕ) : Finset ℤ :=
  (offsetBox L).image fun cell ↦
    (a : ℤ) * cell.1 - (b : ℤ) * cell.2

@[simp]
theorem mem_channelHeights
    {L a b : ℕ} {h : ℤ} :
    h ∈ channelHeights L a b ↔
      ∃ cell ∈ offsetBox L, OnChannel a b h cell := by
  simp only [channelHeights, mem_image]
  constructor
  · rintro ⟨cell, hcell, rfl⟩
    exact ⟨cell, hcell, rfl⟩
  · rintro ⟨cell, hcell, hchannel⟩
    refine ⟨cell, hcell, ?_⟩
    exact hchannel

/-- A channel is nonempty exactly when its parameter is attained in the box. -/
theorem channelCells_nonempty_iff_mem_channelHeights
    {L a b : ℕ} {h : ℤ} :
    (channelCells L a b h).Nonempty ↔
      h ∈ channelHeights L a b := by
  constructor
  · rintro ⟨cell, hcell⟩
    rw [mem_channelHeights]
    exact ⟨cell, (mem_channelCells.mp hcell).1,
      (mem_channelCells.mp hcell).2⟩
  · intro hh
    rw [mem_channelHeights] at hh
    obtain ⟨cell, hbox, hchannel⟩ := hh
    exact ⟨cell, mem_channelCells.mpr ⟨hbox, hchannel⟩⟩

/-- Smallest possible value of `a*i-b*j` on the offset box. -/
def channelHeightLower (L a b : ℕ) : ℤ :=
  -(a : ℤ) - (b : ℤ) * ((L : ℤ) - 1)

/-- Largest possible value of `a*i-b*j` on the offset box. -/
def channelHeightUpper (L a b : ℕ) : ℤ :=
  (a : ℤ) * ((L : ℤ) - 1) + (b : ℤ)

/-- Every attained parameter lies in the sharp enclosing interval. -/
theorem channelHeights_subset_interval (L a b : ℕ) :
    channelHeights L a b ⊆
      Icc (channelHeightLower L a b)
        (channelHeightUpper L a b) := by
  intro h hh
  rw [mem_channelHeights] at hh
  obtain ⟨cell, hbox, rfl⟩ := hh
  rw [mem_Icc]
  have hbounds := mem_offsetBox.mp hbox
  have ha0 : (0 : ℤ) ≤ (a : ℤ) := by positivity
  have hb0 : (0 : ℤ) ≤ (b : ℤ) := by positivity
  have haiLower :
      -(a : ℤ) ≤ (a : ℤ) * cell.1 := by
    calc
      -(a : ℤ) = (a : ℤ) * (-1) := by ring
      _ ≤ (a : ℤ) * cell.1 :=
        mul_le_mul_of_nonneg_left hbounds.1.1 ha0
  have haiUpper :
      (a : ℤ) * cell.1 ≤
        (a : ℤ) * ((L : ℤ) - 1) :=
    mul_le_mul_of_nonneg_left hbounds.1.2 ha0
  have hbjLower :
      -(b : ℤ) * ((L : ℤ) - 1) ≤
        -(b : ℤ) * cell.2 :=
    mul_le_mul_of_nonpos_left hbounds.2.2 (by omega)
  have hbjUpper :
      -(b : ℤ) * cell.2 ≤ (b : ℤ) := by
    calc
      -(b : ℤ) * cell.2 ≤ -(b : ℤ) * (-1) :=
        mul_le_mul_of_nonpos_left hbounds.2.1 (by omega)
      _ = (b : ℤ) := by ring
  constructor
  · unfold channelHeightLower
    linarith
  · unfold channelHeightUpper
    linarith

/--
For fixed `(a,b)`, the number of nonempty affine channels is at most
`(a+b)L+1`; this is the precise finite form of the paper's `O(qB)` count.
-/
theorem channelHeights_card_le (L a b : ℕ) :
    (channelHeights L a b).card ≤ (a + b) * L + 1 := by
  have hmono :
      (channelHeights L a b).card ≤
        (Icc (channelHeightLower L a b)
          (channelHeightUpper L a b)).card :=
    card_le_card (channelHeights_subset_interval L a b)
  have horder :
      channelHeightLower L a b ≤
        channelHeightUpper L a b + 1 := by
    unfold channelHeightLower channelHeightUpper
    have ha0 : (0 : ℤ) ≤ (a : ℤ) := by positivity
    have hb0 : (0 : ℤ) ≤ (b : ℤ) := by positivity
    have hL0 : (0 : ℤ) ≤ (L : ℤ) := by positivity
    nlinarith
  have hcardCast :
      ((Icc (channelHeightLower L a b)
          (channelHeightUpper L a b)).card : ℤ) =
        (((a + b) * L + 1 : ℕ) : ℤ) := by
    rw [Int.card_Icc_of_le
      (channelHeightLower L a b)
      (channelHeightUpper L a b) horder]
    unfold channelHeightLower channelHeightUpper
    push_cast
    ring
  have hcard :
      (Icc (channelHeightLower L a b)
          (channelHeightUpper L a b)).card =
        (a + b) * L + 1 := by
    exact_mod_cast hcardCast
  rwa [hcard] at hmono

/-- The channel dimension parameter `max(m-1,0)` in natural-number form. -/
def channelSigma (L a b : ℕ) (h : ℤ) : ℕ :=
  (channelCells L a b h).card - 1

@[simp]
theorem channelSigma_eq
    (L a b : ℕ) (h : ℤ) :
    channelSigma L a b h =
      (channelCells L a b h).card - 1 :=
  rfl

end PaperC
