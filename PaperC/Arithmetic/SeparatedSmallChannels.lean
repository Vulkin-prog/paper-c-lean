import PaperC.Arithmetic.CanonicalChannel
import Mathlib.Data.Nat.Dist

/-!
# The first two primitive channel heights

The small-height cases in Proposition 5.4 have a particularly rigid
arithmetic form.  At height one the only positive pair is `(1,1)`, and an
exact channel with its canonical parameter can occur only when the two starts
are at distance at most the offset length.  At height two, primitivity leaves
only the two oriented pairs `(2,1)` and `(1,2)`.
-/

namespace PaperC

/-- A positive pair of height one is necessarily `(1,1)`. -/
theorem positive_pair_eq_one_of_max_eq_one
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hmax : Nat.max a b = 1) :
    a = 1 ∧ b = 1 := by
  have hale : a ≤ 1 := by
    rw [← hmax]
    exact Nat.le_max_left _ _
  have hble : b ≤ 1 := by
    rw [← hmax]
    exact Nat.le_max_right _ _
  omega

/--
For the unit direction `(1,1)`, one cell with canonical parameter
`y-x` already forces the starts to be separated by at most `L`.
-/
theorem dist_le_length_of_mem_unit_channel
    {x y L : ℕ} {h : ℤ} {cell : ℤ × ℤ}
    (hparameter : pairChannelError x y 1 1 = h)
    (hcell : cell ∈ channelCells L 1 1 h) :
    Nat.dist x y ≤ L := by
  have hdata := mem_channelCells.mp hcell
  have hbox := mem_offsetBox.mp hdata.1
  have hchannel := hdata.2
  rw [← hparameter] at hchannel
  simp only [OnChannel, pairChannelError, Nat.cast_one, one_mul] at hchannel
  by_cases hxy : x ≤ y
  · rw [Nat.dist_eq_sub_of_le hxy]
    omega
  · have hyx : y ≤ x := Nat.le_of_not_ge hxy
    rw [Nat.dist_eq_sub_of_le_right hyx]
    omega

/--
Height-one primitive channels carrying at least two cells have unit
coefficients, and their two starts are at distance at most `L`.
-/
theorem height_one_primitive_channel_forces_unit_and_nearby
    {x y L a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (_hab : a.Coprime b)
    (hmax : Nat.max a b = 1)
    {h : ℤ}
    (hparameter : pairChannelError x y a b = h)
    (hm : 2 ≤ (channelCells L a b h).card) :
    a = 1 ∧ b = 1 ∧ Nat.dist x y ≤ L := by
  obtain ⟨rfl, rfl⟩ :=
    positive_pair_eq_one_of_max_eq_one ha hb hmax
  have hcard : 0 < (channelCells L 1 1 h).card := by
    omega
  obtain ⟨cell, hcell⟩ :=
    Finset.card_pos.mp hcard
  exact ⟨rfl, rfl,
    dist_le_length_of_mem_unit_channel hparameter hcell⟩

/--
The only positive coprime pairs of height two are the two orientations
`(2,1)` and `(1,2)`.
-/
theorem positive_coprime_pair_of_max_eq_two
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) (hmax : Nat.max a b = 2) :
    (a = 2 ∧ b = 1) ∨ (a = 1 ∧ b = 2) := by
  have hale : a ≤ 2 := by
    rw [← hmax]
    exact Nat.le_max_left _ _
  have hble : b ≤ 2 := by
    rw [← hmax]
    exact Nat.le_max_right _ _
  have hacases : a = 1 ∨ a = 2 := by
    omega
  have hbcases : b = 1 ∨ b = 2 := by
    omega
  rcases hacases with rfl | rfl <;>
    rcases hbcases with rfl | rfl
  · norm_num at hmax
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · norm_num at hab

end PaperC
