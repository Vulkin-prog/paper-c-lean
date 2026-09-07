import PaperC.Arithmetic.WeightedChannelMass

/-!
# Base-two mass of rational channel geometries

This is the geometry-only sum in equation (3.13), with `B = L + 1`.
It uses the actual positive reduced coefficient pairs and all integer
channel parameters with at least two cells. Such a geometry automatically
has height at most `L`. Each weight is `2^(m-1)`, with no translation
parameter and no subtraction of one from that weight.

The retained base-four weighted mass is a different quantity. Here the
finite counting and multiplicity lemmas directly give a base-two bound.
-/

namespace PaperC.V282.RationalGeometryMass

open Finset

/-- The exact finite geometry-only mass, with binary weight `2^(m-1)`. -/
def geometryMass (L : ℕ) : ℕ :=
  ∑ q ∈ Icc 2 L, ∑ c ∈ reducedRatiosAtHeight q,
    ∑ h ∈ nontrivialChannelHeights L c.1 c.2,
      2 ^ channelSigma L c.1 c.2 h

/-- The finite support is exactly all positive primitive geometries with
height at least two and multiplicity at least two. -/
theorem geometry_mem_sum_iff {L a b : ℕ} {h : ℤ} :
    (Nat.max a b ∈ Icc 2 L ∧
      (a, b) ∈ reducedRatiosAtHeight (Nat.max a b) ∧
      h ∈ nontrivialChannelHeights L a b) ↔
    0 < a ∧ 0 < b ∧ a.Coprime b ∧ 2 ≤ Nat.max a b ∧
      2 ≤ (channelCells L a b h).card := by
  constructor
  · rintro ⟨hq, hab, hh⟩
    obtain ⟨ha, hb, hcop, _⟩ := mem_reducedRatiosAtHeight.mp hab
    exact ⟨ha, hb, hcop, (mem_Icc.mp hq).1,
      mem_nontrivialChannelHeights_iff_two_le_card.mp hh⟩
  · rintro ⟨ha, hb, hcop, hq, hm⟩
    have hh := mem_nontrivialChannelHeights_iff_two_le_card.mpr hm
    exact ⟨mem_Icc.mpr ⟨hq,
        max_coeff_le_length_of_mem_nontrivialChannelHeights ha hb hcop hh⟩,
      mem_reducedRatiosAtHeight.mpr ⟨ha, hb, hcop, rfl⟩, hh⟩

/-- An explicit contribution bound at every height, before summing heights. -/
theorem geometryMass_le_height_envelope (L : ℕ) :
    geometryMass L ≤
      ∑ q ∈ Icc 2 L, (2 * q) * (((2 * q) * L + 1) * 2 ^ (L / q)) := by
  unfold geometryMass
  apply Finset.sum_le_sum
  intro q _hq
  let W := ((2 * q) * L + 1) * 2 ^ (L / q)
  have hpair : ∀ c ∈ reducedRatiosAtHeight q,
      (∑ h ∈ nontrivialChannelHeights L c.1 c.2,
        2 ^ channelSigma L c.1 c.2 h) ≤ W := by
    intro c hc
    obtain ⟨ha, hb, hcop, hmax⟩ := mem_reducedRatiosAtHeight.mp hc
    have hsum : c.1 + c.2 ≤ 2 * q := by
      have ha' : c.1 ≤ q := by
        rw [← hmax]
        exact Nat.le_max_left _ _
      have hb' : c.2 ≤ q := by
        rw [← hmax]
        exact Nat.le_max_right _ _
      omega
    calc
      (∑ h ∈ nontrivialChannelHeights L c.1 c.2,
          2 ^ channelSigma L c.1 c.2 h) ≤
          ∑ _h ∈ nontrivialChannelHeights L c.1 c.2, 2 ^ (L / q) := by
        apply Finset.sum_le_sum
        intro h _hh
        simpa only [hmax] using
          two_pow_channelSigma_le_div_maxStep L c.1 c.2 ha hb hcop h
      _ = (nontrivialChannelHeights L c.1 c.2).card * 2 ^ (L / q) := by simp
      _ ≤ (channelHeights L c.1 c.2).card * 2 ^ (L / q) :=
        Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)
      _ ≤ ((c.1 + c.2) * L + 1) * 2 ^ (L / q) :=
        Nat.mul_le_mul_right _ (channelHeights_card_le L c.1 c.2)
      _ ≤ ((2 * q) * L + 1) * 2 ^ (L / q) :=
        Nat.mul_le_mul_right _
          (Nat.add_le_add_right (Nat.mul_le_mul_right L hsum) 1)
      _ = W := rfl
  calc
    (∑ c ∈ reducedRatiosAtHeight q,
        ∑ h ∈ nontrivialChannelHeights L c.1 c.2,
          2 ^ channelSigma L c.1 c.2 h) ≤
        ∑ _c ∈ reducedRatiosAtHeight q, W :=
      Finset.sum_le_sum hpair
    _ = (reducedRatiosAtHeight q).card * W := by simp
    _ ≤ (2 * q) * W :=
      Nat.mul_le_mul_right W (card_reducedRatiosAtHeight_le q)

/-- A common finite envelope for every nontrivial height `q ≥ 2`. -/
theorem geometryMass_le_uniform_height_envelope (L : ℕ) :
    geometryMass L ≤
      L * (2 * L) * ((2 * L) * L + 1) * 2 ^ (L / 2) := by
  let W := (2 * L) * (((2 * L) * L + 1) * 2 ^ (L / 2))
  have hterm : ∀ q ∈ Icc 2 L,
      (2 * q) * (((2 * q) * L + 1) * 2 ^ (L / q)) ≤ W := by
    intro q hq
    obtain ⟨hqTwo, hqL⟩ := mem_Icc.mp hq
    have htwo : 2 * q ≤ 2 * L := Nat.mul_le_mul_left 2 hqL
    have hheight : (2 * q) * L + 1 ≤ (2 * L) * L + 1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_right L htwo) 1
    have hpower : 2 ^ (L / q) ≤ 2 ^ (L / 2) :=
      Nat.pow_le_pow_right (by norm_num)
        (Nat.div_le_div_left hqTwo (by omega))
    exact Nat.mul_le_mul htwo (Nat.mul_le_mul hheight hpower)
  have hcard : (Icc 2 L).card ≤ L := by
    simp [Nat.card_Icc]
  calc
    geometryMass L ≤
        ∑ q ∈ Icc 2 L, (2 * q) * (((2 * q) * L + 1) * 2 ^ (L / q)) :=
      geometryMass_le_height_envelope L
    _ ≤ ∑ _q ∈ Icc 2 L, W := Finset.sum_le_sum hterm
    _ = (Icc 2 L).card * W := by simp
    _ ≤ L * W := Nat.mul_le_mul_right W hcard
    _ = L * (2 * L) * ((2 * L) * L + 1) * 2 ^ (L / 2) := by
      dsimp [W]
      ring

/-- The base-two finite majorant underlying equation (3.13). -/
theorem geometryMass_le_poly_two_pow_half (L : ℕ) :
    geometryMass L ≤ 6 * (L + 1) ^ 4 * 2 ^ (L / 2) := by
  have hLB : L ≤ L + 1 := Nat.le_succ L
  have htwo : 2 * L ≤ 2 * (L + 1) := Nat.mul_le_mul_left 2 hLB
  have hone : 1 ≤ (L + 1) * (L + 1) := by
    exact Nat.mul_pos (Nat.succ_pos L) (Nat.succ_pos L)
  have hinner : (2 * L) * L + 1 ≤
      (2 * (L + 1)) * (L + 1) + (L + 1) * (L + 1) :=
    Nat.add_le_add (Nat.mul_le_mul htwo hLB) hone
  have hfront : L * (2 * L) ≤ (L + 1) * (2 * (L + 1)) :=
    Nat.mul_le_mul hLB htwo
  have hpoly : L * (2 * L) * ((2 * L) * L + 1) ≤ 6 * (L + 1) ^ 4 := by
    calc
      _ ≤ ((L + 1) * (2 * (L + 1))) *
          ((2 * (L + 1)) * (L + 1) + (L + 1) * (L + 1)) :=
        Nat.mul_le_mul hfront hinner
      _ = 6 * (L + 1) ^ 4 := by ring
  exact (geometryMass_le_uniform_height_envelope L).trans
    (Nat.mul_le_mul_right _ hpoly)

end PaperC.V282.RationalGeometryMass
