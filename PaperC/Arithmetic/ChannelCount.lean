import PaperC.Arithmetic.ChannelGeometry
import PaperC.Arithmetic.IntervalCongruence

/-!
# Counting cells on one primitive channel

This file combines the primitive direction from Lemma 5.1 with the interval
congruence count.  Projecting a channel to the coordinate whose step is
`max a b` gives the `1 + B / q` lattice-point estimate used in Lemma 7.2.
-/

namespace PaperC

open Finset

/-- First-coordinate projection of the cells on one channel. -/
def channelFirstCoordinates (L a b : ℕ) (h : ℤ) : Finset ℤ :=
  (channelCells L a b h).image Prod.fst

/-- Second-coordinate projection of the cells on one channel. -/
def channelSecondCoordinates (L a b : ℕ) (h : ℤ) : Finset ℤ :=
  (channelCells L a b h).image Prod.snd

theorem fst_injOn_channelCells
    {L a b : ℕ} (hb : 0 < b) {h : ℤ} :
    Set.InjOn Prod.fst (↑(channelCells L a b h) : Set (ℤ × ℤ)) := by
  intro cell₁ h₁ cell₂ h₂ hfst
  apply Prod.ext hfst
  have hc₁ := (mem_channelCells.mp h₁).2
  have hc₂ := (mem_channelCells.mp h₂).2
  have hdiff := channel_difference_identity hc₁ hc₂
  have hzero :
      (b : ℤ) * (cell₁.2 - cell₂.2) = 0 := by
    rw [← hdiff, hfst]
    ring
  have hb0 : (b : ℤ) ≠ 0 := by exact_mod_cast hb.ne'
  have : cell₁.2 - cell₂.2 = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hb0
  omega

theorem snd_injOn_channelCells
    {L a b : ℕ} (ha : 0 < a) {h : ℤ} :
    Set.InjOn Prod.snd (↑(channelCells L a b h) : Set (ℤ × ℤ)) := by
  intro cell₁ h₁ cell₂ h₂ hsnd
  apply Prod.ext
  · have hc₁ := (mem_channelCells.mp h₁).2
    have hc₂ := (mem_channelCells.mp h₂).2
    have hdiff := channel_difference_identity hc₁ hc₂
    have hzero :
        (a : ℤ) * (cell₁.1 - cell₂.1) = 0 := by
      rw [hdiff, hsnd]
      ring
    have ha0 : (a : ℤ) ≠ 0 := by exact_mod_cast ha.ne'
    have : cell₁.1 - cell₂.1 = 0 :=
      (mul_eq_zero.mp hzero).resolve_left ha0
    omega
  · exact hsnd

theorem channelFirstCoordinates_subset_modClass
    {L a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    {h : ℤ} {cell₀ : ℤ × ℤ}
    (hcell₀ : cell₀ ∈ channelCells L a b h) :
    channelFirstCoordinates L a b h ⊆
      {i ∈ Ico (-1 : ℤ) (L : ℤ) |
        i ≡ cell₀.1 [ZMOD (b : ℤ)]} := by
  intro i hi
  rw [channelFirstCoordinates, mem_image] at hi
  obtain ⟨cell, hcell, rfl⟩ := hi
  have hbox := (mem_channelCells.mp hcell).1
  have hinterval := (mem_offsetBox.mp hbox).1
  have hcongruence :
      cell.1 ≡ cell₀.1 [ZMOD (b : ℤ)] := by
    obtain ⟨t, ht, _⟩ :=
      channel_difference_eq_multiple ha hb hab
        (mem_channelCells.mp hcell).2
        (mem_channelCells.mp hcell₀).2
    rw [Int.modEq_iff_dvd]
    refine ⟨-t, ?_⟩
    rw [← neg_sub, ht]
    ring
  simp only [mem_filter, mem_Ico]
  exact ⟨⟨hinterval.1, by omega⟩, hcongruence⟩

theorem channelSecondCoordinates_subset_modClass
    {L a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    {h : ℤ} {cell₀ : ℤ × ℤ}
    (hcell₀ : cell₀ ∈ channelCells L a b h) :
    channelSecondCoordinates L a b h ⊆
      {j ∈ Ico (-1 : ℤ) (L : ℤ) |
        j ≡ cell₀.2 [ZMOD (a : ℤ)]} := by
  intro j hj
  rw [channelSecondCoordinates, mem_image] at hj
  obtain ⟨cell, hcell, rfl⟩ := hj
  have hbox := (mem_channelCells.mp hcell).1
  have hinterval := (mem_offsetBox.mp hbox).2
  have hcongruence :
      cell.2 ≡ cell₀.2 [ZMOD (a : ℤ)] := by
    obtain ⟨t, _, ht⟩ :=
      channel_difference_eq_multiple ha hb hab
        (mem_channelCells.mp hcell).2
        (mem_channelCells.mp hcell₀).2
    rw [Int.modEq_iff_dvd]
    refine ⟨-t, ?_⟩
    rw [← neg_sub, ht]
    ring
  simp only [mem_filter, mem_Ico]
  exact ⟨⟨hinterval.1, by omega⟩, hcongruence⟩

/-- Count a channel by its first coordinate, whose primitive step is `b`. -/
theorem channelCells_card_cast_le_firstStep
    (L a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (h : ℤ) :
    ((channelCells L a b h).card : ℚ) ≤
      (((((L : ℤ) - (-1 : ℤ)) : ℤ) : ℚ) / (b : ℚ)) + 1 := by
  classical
  by_cases hempty : channelCells L a b h = ∅
  · simp [hempty]
    positivity
  · obtain ⟨cell₀, hcell₀⟩ :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    have hcard :
        (channelFirstCoordinates L a b h).card =
          (channelCells L a b h).card :=
      card_image_of_injOn (fst_injOn_channelCells hb)
    have hsubset :=
      channelFirstCoordinates_subset_modClass ha hb hab hcell₀
    have hmono :
        (channelCells L a b h).card ≤
          {i ∈ Ico (-1 : ℤ) (L : ℤ) |
            i ≡ cell₀.1 [ZMOD (b : ℤ)]}.card := by
      rw [← hcard]
      exact card_mono hsubset
    have hcount :=
      card_Ico_modEq_cast_le_div_add_one
        (-1 : ℤ) (L : ℤ) cell₀.1 (b : ℤ)
        (by exact_mod_cast hb) (by omega)
    have hmonoQ :
        ((channelCells L a b h).card : ℚ) ≤
          ({i ∈ Ico (-1 : ℤ) (L : ℤ) |
            i ≡ cell₀.1 [ZMOD (b : ℤ)]}.card : ℚ) := by
      exact_mod_cast hmono
    exact hmonoQ.trans hcount

/-- Count a channel by its second coordinate, whose primitive step is `a`. -/
theorem channelCells_card_cast_le_secondStep
    (L a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (h : ℤ) :
    ((channelCells L a b h).card : ℚ) ≤
      (((((L : ℤ) - (-1 : ℤ)) : ℤ) : ℚ) / (a : ℚ)) + 1 := by
  classical
  by_cases hempty : channelCells L a b h = ∅
  · simp [hempty]
    positivity
  · obtain ⟨cell₀, hcell₀⟩ :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    have hcard :
        (channelSecondCoordinates L a b h).card =
          (channelCells L a b h).card :=
      card_image_of_injOn (snd_injOn_channelCells ha)
    have hsubset :=
      channelSecondCoordinates_subset_modClass ha hb hab hcell₀
    have hmono :
        (channelCells L a b h).card ≤
          {j ∈ Ico (-1 : ℤ) (L : ℤ) |
            j ≡ cell₀.2 [ZMOD (a : ℤ)]}.card := by
      rw [← hcard]
      exact card_mono hsubset
    have hcount :=
      card_Ico_modEq_cast_le_div_add_one
        (-1 : ℤ) (L : ℤ) cell₀.2 (a : ℤ)
        (by exact_mod_cast ha) (by omega)
    have hmonoQ :
        ((channelCells L a b h).card : ℚ) ≤
          ({j ∈ Ico (-1 : ℤ) (L : ℤ) |
            j ≡ cell₀.2 [ZMOD (a : ℤ)]}.card : ℚ) := by
      exact_mod_cast hmono
    exact hmonoQ.trans hcount

/--
Primitive-channel lattice-point bound with step `q = max a b`, matching the
geometric factor in Lemma 7.2.
-/
theorem channelCells_card_cast_le_maxStep
    (L a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (h : ℤ) :
    ((channelCells L a b h).card : ℚ) ≤
      (((((L : ℤ) - (-1 : ℤ)) : ℤ) : ℚ) /
          (Nat.max a b : ℚ)) + 1 := by
  by_cases habOrder : a ≤ b
  · simpa [Nat.max_eq_right habOrder] using
      channelCells_card_cast_le_firstStep L a b ha hb hab h
  · have hba : b ≤ a := le_of_not_ge habOrder
    simpa [Nat.max_eq_left hba] using
      channelCells_card_cast_le_secondStep L a b ha hb hab h

end PaperC
