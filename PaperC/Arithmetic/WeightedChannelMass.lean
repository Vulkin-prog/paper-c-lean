import PaperC.Arithmetic.ChannelMultiplicityBounds

/-!
# Weighted mass of nontrivial rational channels

This module packages the finite sum occurring in Lemma 5.5.  At height
`q = max a b`, it sums over positive reduced pairs `(a,b)`, over attained
affine parameters `h`, and retains only channels containing at least two
cells.  Such a channel receives weight `4 ^ channelSigma`.

The final estimate separates the exceptional height `q = 2` from all
heights `q ≥ 3`.  Its constants are deliberately elementary; the important
feature is the exponential separation between `4^(L/2)` and `4^(L/3)`.
-/

namespace PaperC

open Finset

/-- Attained parameters whose channel contains at least two cells. -/
def nontrivialChannelHeights
    (L a b : ℕ) : Finset ℤ :=
  (channelHeights L a b).filter fun h ↦
    2 ≤ (channelCells L a b h).card

@[simp]
theorem mem_nontrivialChannelHeights
    {L a b : ℕ} {h : ℤ} :
    h ∈ nontrivialChannelHeights L a b ↔
      h ∈ channelHeights L a b ∧
        2 ≤ (channelCells L a b h).card := by
  simp [nontrivialChannelHeights]

/--
The attained-height condition is automatic once the channel contains two
cells.  Thus the finite height filter is extensionally the manuscript's
condition `m(a,b,h) ≥ 2`.
-/
theorem mem_nontrivialChannelHeights_iff_two_le_card
    {L a b : ℕ} {h : ℤ} :
    h ∈ nontrivialChannelHeights L a b ↔
      2 ≤ (channelCells L a b h).card := by
  rw [mem_nontrivialChannelHeights]
  constructor
  · exact And.right
  · intro hm
    refine ⟨?_, hm⟩
    rw [← channelCells_nonempty_iff_mem_channelHeights]
    exact Finset.card_pos.mp (by omega)

/--
Every geometry retained by the weighted sum automatically has
`max(a,b) ≤ L`; this justifies the finite outer range `q ∈ [2,L]`.
-/
theorem max_coeff_le_length_of_mem_nontrivialChannelHeights
    {L a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) {h : ℤ}
    (hh : h ∈ nontrivialChannelHeights L a b) :
    Nat.max a b ≤ L := by
  have hm :
      2 ≤ (channelCells L a b h).card :=
    (mem_nontrivialChannelHeights_iff_two_le_card.mp hh)
  obtain ⟨cell₁, hcell₁, cell₂, hcell₂, hne⟩ :
      ∃ cell₁ ∈ channelCells L a b h,
        ∃ cell₂ ∈ channelCells L a b h, cell₁ ≠ cell₂ :=
    Finset.one_lt_card.mp hm
  have hbounds :=
    channel_coefficients_le_length_of_mem
      ha hb hab hcell₁ hcell₂ hne
  exact (Nat.max_le).2 hbounds

/-- Weighted contribution of one reduced coefficient pair. -/
def weightedChannelMassAtPair
    (L a b : ℕ) : ℕ :=
  ∑ h ∈ nontrivialChannelHeights L a b,
    4 ^ channelSigma L a b h

/-- Weighted contribution of all reduced pairs at the fixed height `q`. -/
def weightedChannelMassAtHeight
    (L q : ℕ) : ℕ :=
  ∑ c ∈ reducedRatiosAtHeight q,
    weightedChannelMassAtPair L c.1 c.2

/--
The exact finite weighted mass from Lemma 5.5, with heights restricted to
`2 ≤ q ≤ L`.
-/
def weightedChannelMass (L : ℕ) : ℕ :=
  ∑ q ∈ Icc 2 L, weightedChannelMassAtHeight L q

/-- One pair contributes at most its number of attained heights times the
uniform multiplicity weight. -/
theorem weightedChannelMassAtPair_le
    (L a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) :
    weightedChannelMassAtPair L a b ≤
      ((a + b) * L + 1) *
        4 ^ (L / Nat.max a b) := by
  unfold weightedChannelMassAtPair
  let W := 4 ^ (L / Nat.max a b)
  calc
    (∑ h ∈ nontrivialChannelHeights L a b,
        4 ^ channelSigma L a b h) ≤
        ∑ _h ∈ nontrivialChannelHeights L a b, W := by
      apply Finset.sum_le_sum
      intro h _hh
      exact
        four_pow_channelSigma_le_div_maxStep
          L a b ha hb hab h
    _ = (nontrivialChannelHeights L a b).card * W := by
      simp
    _ ≤ (channelHeights L a b).card * W := by
      exact Nat.mul_le_mul_right W
        (Finset.card_filter_le _ _)
    _ ≤ ((a + b) * L + 1) * W := by
      exact Nat.mul_le_mul_right W
        (channelHeights_card_le L a b)

/--
At height `q`, there are at most `2q` reduced pairs, at most `2qL+1`
attained affine parameters per pair, and every weight is at most
`4^(L/q)`.
-/
theorem weightedChannelMassAtHeight_le
    (L q : ℕ) (_hq : 0 < q) :
    weightedChannelMassAtHeight L q ≤
      (2 * q) * (((2 * q) * L + 1) * 4 ^ (L / q)) := by
  unfold weightedChannelMassAtHeight
  let W := ((2 * q) * L + 1) * 4 ^ (L / q)
  have hpair :
      ∀ c ∈ reducedRatiosAtHeight q,
        weightedChannelMassAtPair L c.1 c.2 ≤ W := by
    intro c hc
    obtain ⟨ha, hb, hab, hmax⟩ :=
      mem_reducedRatiosAtHeight.mp hc
    have hacoeff : c.1 ≤ q := by
      rw [← hmax]
      exact Nat.le_max_left _ _
    have hbcoeff : c.2 ≤ q := by
      rw [← hmax]
      exact Nat.le_max_right _ _
    have habSum : c.1 + c.2 ≤ 2 * q := by omega
    have hheight :
        (c.1 + c.2) * L + 1 ≤ (2 * q) * L + 1 :=
      Nat.add_le_add_right
        (Nat.mul_le_mul_right L habSum) 1
    have hbase :=
      weightedChannelMassAtPair_le
        L c.1 c.2 ha hb hab
    calc
      weightedChannelMassAtPair L c.1 c.2 ≤
          ((c.1 + c.2) * L + 1) *
            4 ^ (L / Nat.max c.1 c.2) :=
        hbase
      _ = ((c.1 + c.2) * L + 1) * 4 ^ (L / q) := by
        rw [hmax]
      _ ≤ ((2 * q) * L + 1) * 4 ^ (L / q) :=
        Nat.mul_le_mul_right _ hheight
      _ = W := rfl
  calc
    (∑ c ∈ reducedRatiosAtHeight q,
        weightedChannelMassAtPair L c.1 c.2) ≤
        ∑ _c ∈ reducedRatiosAtHeight q, W := by
      apply Finset.sum_le_sum
      intro c hc
      exact hpair c hc
    _ = (reducedRatiosAtHeight q).card * W := by
      simp
    _ ≤ (2 * q) * W :=
      Nat.mul_le_mul_right W
        (card_reducedRatiosAtHeight_le q)

/-- Explicit bound for the exceptional height `q = 2`. -/
theorem weightedChannelMassAtHeight_two_le
    (L : ℕ) :
    weightedChannelMassAtHeight L 2 ≤
      4 * ((4 * L + 1) * 4 ^ (L / 2)) := by
  simpa using weightedChannelMassAtHeight_le L 2 (by omega)

/-- Every height `q ≥ 3` is bounded by one common large-height envelope. -/
theorem weightedChannelMassAtHeight_ge_three_le
    {L q : ℕ} (hq : 3 ≤ q) (hqL : q ≤ L) :
    weightedChannelMassAtHeight L q ≤
      (2 * L) * (((2 * L) * L + 1) * 4 ^ (L / 3)) := by
  have htwo : 2 * q ≤ 2 * L :=
    Nat.mul_le_mul_left 2 hqL
  have hheight :
      (2 * q) * L + 1 ≤ (2 * L) * L + 1 :=
    Nat.add_le_add_right
      (Nat.mul_le_mul_right L htwo) 1
  have hquotient : L / q ≤ L / 3 :=
    Nat.div_le_div_left hq (by omega)
  have hpower :
      4 ^ (L / q) ≤ 4 ^ (L / 3) :=
    Nat.pow_le_pow_right (by norm_num) hquotient
  calc
    weightedChannelMassAtHeight L q ≤
        (2 * q) * (((2 * q) * L + 1) * 4 ^ (L / q)) :=
      weightedChannelMassAtHeight_le L q (by omega)
    _ ≤ (2 * L) * (((2 * L) * L + 1) * 4 ^ (L / 3)) :=
      Nat.mul_le_mul htwo (Nat.mul_le_mul hheight hpower)

/-- Sum of all heights at least three. -/
theorem sum_weightedChannelMassAtHeight_ge_three_le
    (L : ℕ) :
    (∑ q ∈ Icc 3 L, weightedChannelMassAtHeight L q) ≤
      L * ((2 * L) *
        (((2 * L) * L + 1) * 4 ^ (L / 3))) := by
  let W :=
    (2 * L) * (((2 * L) * L + 1) * 4 ^ (L / 3))
  have hterm :
      ∀ q ∈ Icc 3 L,
        weightedChannelMassAtHeight L q ≤ W := by
    intro q hq
    obtain ⟨hq3, hqL⟩ := Finset.mem_Icc.mp hq
    exact weightedChannelMassAtHeight_ge_three_le hq3 hqL
  have hcard : (Icc 3 L).card ≤ L := by
    simp [Nat.card_Icc]
  calc
    (∑ q ∈ Icc 3 L, weightedChannelMassAtHeight L q) ≤
        ∑ _q ∈ Icc 3 L, W := by
      apply Finset.sum_le_sum
      intro q hq
      exact hterm q hq
    _ = (Icc 3 L).card * W := by
      simp
    _ ≤ L * W :=
      Nat.mul_le_mul_right W hcard

/-- Exact separation of `q = 2` from the range `q ≥ 3`. -/
theorem weightedChannelMass_eq_two_add_ge_three
    {L : ℕ} (hL : 2 ≤ L) :
    weightedChannelMass L =
      weightedChannelMassAtHeight L 2 +
        ∑ q ∈ Icc 3 L, weightedChannelMassAtHeight L q := by
  have hsplit : Icc 2 L = insert 2 (Icc 3 L) := by
    ext q
    simp only [mem_Icc, mem_insert]
    omega
  unfold weightedChannelMass
  rw [hsplit]
  simp

/--
Finite weighted-mass estimate for Lemma 5.5.  The first term is the
height-two contribution; every remaining height gains the stronger
`4^(L/3)` exponential factor.
-/
theorem weightedChannelMass_le_small_add_large
    (L : ℕ) :
    weightedChannelMass L ≤
      8 * ((4 * L + 1) * 4 ^ (L / 2)) +
        L * ((2 * L) *
          (((2 * L) * L + 1) * 4 ^ (L / 3))) := by
  by_cases hL : 2 ≤ L
  · rw [weightedChannelMass_eq_two_add_ge_three hL]
    apply Nat.add_le_add
    · exact
        (weightedChannelMassAtHeight_two_le L).trans
          (Nat.mul_le_mul_right
            ((4 * L + 1) * 4 ^ (L / 2)) (by omega))
    · exact sum_weightedChannelMassAtHeight_ge_three_le L
  · have hempty : Icc 2 L = ∅ := by
      ext q
      simp only [mem_Icc, Finset.notMem_empty, iff_false]
      omega
    simp [weightedChannelMass, hempty]

end PaperC
