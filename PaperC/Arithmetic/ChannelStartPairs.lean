import PaperC.Arithmetic.CanonicalChannel
import PaperC.Arithmetic.ChannelMultiplicityBounds
import PaperC.Model.FiniteRademacher

set_option maxHeartbeats 1200000

/-!
# Counting dyadic start pairs on one exact channel

For fixed positive coprime coefficients `(a,b)` and fixed channel error `h`,
the dyadic start pairs

`(x,y) ∈ [N,2N)²`, `b*y - a*x = h`

lie on a translate of the primitive lattice direction `(b,a)`.  Projection
to either coordinate is injective.  The first coordinates occupy one residue
class modulo `b`, the second coordinates one residue class modulo `a`, and
therefore a channel contains at most

`1 + N / max a b`

dyadic start pairs.  This is the geometric `O(N/q+1)` factor used in
Proposition 5.4.
-/

namespace PaperC

open Finset

/-- Dyadic start pairs having exact reduced-channel error `h`. -/
def channelStartPairs (N a b : ℕ) (h : ℤ) :
    Finset (ℕ × ℕ) :=
  ((dyadicBlock N) ×ˢ (dyadicBlock N)).filter fun pair =>
    pairChannelError pair.1 pair.2 a b = h

@[simp]
theorem mem_channelStartPairs
    {N a b x y : ℕ} {h : ℤ} :
    (x, y) ∈ channelStartPairs N a b h ↔
      x ∈ dyadicBlock N ∧ y ∈ dyadicBlock N ∧
        pairChannelError x y a b = h := by
  simp [channelStartPairs, and_assoc]

/--
The start-pair equation is the `ChannelGeometry` equation with parameter
`-h`.
-/
theorem onChannel_neg_of_mem_channelStartPairs
    {N a b : ℕ} {h : ℤ} {pair : ℕ × ℕ}
    (hpair : pair ∈ channelStartPairs N a b h) :
    OnChannel a b (-h) ((pair.1 : ℤ), (pair.2 : ℤ)) := by
  rcases pair with ⟨x, y⟩
  have herr := (mem_channelStartPairs.mp hpair).2.2
  simp only [OnChannel, pairChannelError] at herr ⊢
  linarith

/-! ## Coordinate projections -/

/-- First-coordinate projection of the start pairs on a channel. -/
def channelStartFirstCoordinates
    (N a b : ℕ) (h : ℤ) : Finset ℕ :=
  (channelStartPairs N a b h).image Prod.fst

/-- Second-coordinate projection of the start pairs on a channel. -/
def channelStartSecondCoordinates
    (N a b : ℕ) (h : ℤ) : Finset ℕ :=
  (channelStartPairs N a b h).image Prod.snd

/-- For `b>0`, the first coordinate determines a start pair on the channel. -/
theorem fst_injOn_channelStartPairs
    {N a b : ℕ} (hb : 0 < b) {h : ℤ} :
    Set.InjOn Prod.fst
      (↑(channelStartPairs N a b h) : Set (ℕ × ℕ)) := by
  intro pair₁ hpair₁ pair₂ hpair₂ hfst
  apply Prod.ext hfst
  have herr₁ := (mem_channelStartPairs.mp hpair₁).2.2
  have herr₂ := (mem_channelStartPairs.mp hpair₂).2.2
  simp only [pairChannelError] at herr₁ herr₂
  have hzero :
      (b : ℤ) * ((pair₁.2 : ℤ) - (pair₂.2 : ℤ)) = 0 := by
    rw [hfst] at herr₁
    linarith
  have hb0 : (b : ℤ) ≠ 0 := by
    exact_mod_cast hb.ne'
  have hy :
      (pair₁.2 : ℤ) - (pair₂.2 : ℤ) = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hb0
  exact_mod_cast (sub_eq_zero.mp hy)

/-- For `a>0`, the second coordinate determines a start pair on the channel. -/
theorem snd_injOn_channelStartPairs
    {N a b : ℕ} (ha : 0 < a) {h : ℤ} :
    Set.InjOn Prod.snd
      (↑(channelStartPairs N a b h) : Set (ℕ × ℕ)) := by
  intro pair₁ hpair₁ pair₂ hpair₂ hsnd
  apply Prod.ext
  · have herr₁ := (mem_channelStartPairs.mp hpair₁).2.2
    have herr₂ := (mem_channelStartPairs.mp hpair₂).2.2
    simp only [pairChannelError] at herr₁ herr₂
    have hzero :
        (a : ℤ) * ((pair₁.1 : ℤ) - (pair₂.1 : ℤ)) = 0 := by
      rw [hsnd] at herr₁
      linarith
    have ha0 : (a : ℤ) ≠ 0 := by
      exact_mod_cast ha.ne'
    have hx :
        (pair₁.1 : ℤ) - (pair₂.1 : ℤ) = 0 :=
      (mul_eq_zero.mp hzero).resolve_left ha0
    exact_mod_cast (sub_eq_zero.mp hx)
  · exact hsnd

/-! ## Congruence classes -/

/--
First coordinates on one primitive channel all belong to one residue class
modulo `b`.
-/
theorem channelStartFirstCoordinates_subset_modClass
    {N a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    {h : ℤ} {pair₀ : ℕ × ℕ}
    (hpair₀ : pair₀ ∈ channelStartPairs N a b h) :
    channelStartFirstCoordinates N a b h ⊆
      {x ∈ dyadicBlock N | x ≡ pair₀.1 [MOD b]} := by
  intro x hx
  rw [channelStartFirstCoordinates, mem_image] at hx
  obtain ⟨pair, hpair, rfl⟩ := hx
  have hbox := (mem_channelStartPairs.mp hpair).1
  have hcongruenceInt :
      (pair.1 : ℤ) ≡ (pair₀.1 : ℤ) [ZMOD (b : ℤ)] := by
    obtain ⟨t, ht, _⟩ :=
      channel_difference_eq_multiple ha hb hab
        (onChannel_neg_of_mem_channelStartPairs hpair)
        (onChannel_neg_of_mem_channelStartPairs hpair₀)
    rw [Int.modEq_iff_dvd]
    refine ⟨-t, ?_⟩
    rw [← neg_sub, ht]
    ring
  simp only [mem_filter]
  exact ⟨hbox, Int.natCast_modEq_iff.mp hcongruenceInt⟩

/--
Second coordinates on one primitive channel all belong to one residue class
modulo `a`.
-/
theorem channelStartSecondCoordinates_subset_modClass
    {N a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    {h : ℤ} {pair₀ : ℕ × ℕ}
    (hpair₀ : pair₀ ∈ channelStartPairs N a b h) :
    channelStartSecondCoordinates N a b h ⊆
      {y ∈ dyadicBlock N | y ≡ pair₀.2 [MOD a]} := by
  intro y hy
  rw [channelStartSecondCoordinates, mem_image] at hy
  obtain ⟨pair, hpair, rfl⟩ := hy
  have hbox := (mem_channelStartPairs.mp hpair).2.1
  have hcongruenceInt :
      (pair.2 : ℤ) ≡ (pair₀.2 : ℤ) [ZMOD (a : ℤ)] := by
    obtain ⟨t, _, ht⟩ :=
      channel_difference_eq_multiple ha hb hab
        (onChannel_neg_of_mem_channelStartPairs hpair)
        (onChannel_neg_of_mem_channelStartPairs hpair₀)
    rw [Int.modEq_iff_dvd]
    refine ⟨-t, ?_⟩
    rw [← neg_sub, ht]
    ring
  simp only [mem_filter]
  exact ⟨hbox, Int.natCast_modEq_iff.mp hcongruenceInt⟩

/-! ## One-dimensional dyadic residue count -/

/--
One residue class modulo `q` has at most `1 + N/q` representatives in the
dyadic interval `[N,2N)`.
-/
theorem card_dyadicBlock_modClass_le_one_add_div
    (N v q : ℕ) (hq : 0 < q) :
    {x ∈ dyadicBlock N | x ≡ v [MOD q]}.card ≤
      1 + N / q := by
  have hcast :=
    congrArg Finset.card
      (Nat.Ico_filter_modEq_cast
        N (2 * N) (r := q) (v := v))
  have hcardEq :
      {x ∈ dyadicBlock N | x ≡ v [MOD q]}.card =
        {x ∈ Ico (N : ℤ) (2 * N : ℤ) |
          x ≡ (v : ℤ) [ZMOD (q : ℤ)]}.card := by
    simpa [dyadicBlock] using hcast
  have hcount :=
    card_Ico_modEq_le_ceil_length
      (N : ℤ) (2 * N : ℤ) (v : ℤ) (q : ℤ)
      (by exact_mod_cast hq) (by omega)
  have hdivision :
      N ≤ (N / q + 1) * q := by
    have hstrict := Nat.lt_div_mul_add (a := N) hq
    have hstrict' :
        N < (N / q + 1) * q := by
      simpa [Nat.add_mul] using hstrict
    exact Nat.le_of_lt hstrict'
  have hquotient :
      (N : ℚ) / (q : ℚ) ≤
        (N / q + 1 : ℕ) := by
    apply (div_le_iff₀ (by exact_mod_cast hq)).2
    exact_mod_cast hdivision
  have hceil :
      ⌈(((((2 * N : ℕ) : ℤ) - (N : ℤ)) : ℤ) : ℚ) /
          (q : ℚ)⌉ ≤
        ((N / q + 1 : ℕ) : ℤ) :=
    Int.ceil_le.mpr (by
      have hcast :
          ((((N / q + 1 : ℕ) : ℤ) : ℚ)) =
            ((N / q + 1 : ℕ) : ℚ) := by
        norm_cast
      rw [hcast]
      simpa only [Int.cast_sub, Int.cast_natCast,
        Int.cast_mul, Int.cast_ofNat, Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_add, Nat.cast_one, two_mul, add_sub_cancel_left]
        using hquotient)
  have hcardInt :
      ({x ∈ dyadicBlock N | x ≡ v [MOD q]}.card : ℤ) ≤
        ((N / q + 1 : ℕ) : ℤ) := by
    rw [hcardEq]
    exact hcount.trans hceil
  have hcardNat :
      {x ∈ dyadicBlock N | x ≡ v [MOD q]}.card ≤
        N / q + 1 := by
    exact_mod_cast hcardInt
  simpa [Nat.add_comm] using hcardNat

/-! ## Channel-pair count -/

/-- Count a channel by its first-coordinate step `b`. -/
theorem channelStartPairs_card_le_one_add_div_firstStep
    (N a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (h : ℤ) :
    (channelStartPairs N a b h).card ≤ 1 + N / b := by
  classical
  by_cases hempty : channelStartPairs N a b h = ∅
  · simp [hempty]
  · obtain ⟨pair₀, hpair₀⟩ :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    have hcard :
        (channelStartFirstCoordinates N a b h).card =
          (channelStartPairs N a b h).card :=
      card_image_of_injOn (fst_injOn_channelStartPairs hb)
    calc
      (channelStartPairs N a b h).card =
          (channelStartFirstCoordinates N a b h).card :=
        hcard.symm
      _ ≤ {x ∈ dyadicBlock N |
            x ≡ pair₀.1 [MOD b]}.card :=
        card_mono
          (channelStartFirstCoordinates_subset_modClass
            ha hb hab hpair₀)
      _ ≤ 1 + N / b :=
        card_dyadicBlock_modClass_le_one_add_div
          N pair₀.1 b hb

/-- Count a channel by its second-coordinate step `a`. -/
theorem channelStartPairs_card_le_one_add_div_secondStep
    (N a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (h : ℤ) :
    (channelStartPairs N a b h).card ≤ 1 + N / a := by
  classical
  by_cases hempty : channelStartPairs N a b h = ∅
  · simp [hempty]
  · obtain ⟨pair₀, hpair₀⟩ :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    have hcard :
        (channelStartSecondCoordinates N a b h).card =
          (channelStartPairs N a b h).card :=
      card_image_of_injOn (snd_injOn_channelStartPairs ha)
    calc
      (channelStartPairs N a b h).card =
          (channelStartSecondCoordinates N a b h).card :=
        hcard.symm
      _ ≤ {y ∈ dyadicBlock N |
            y ≡ pair₀.2 [MOD a]}.card :=
        card_mono
          (channelStartSecondCoordinates_subset_modClass
            ha hb hab hpair₀)
      _ ≤ 1 + N / a :=
        card_dyadicBlock_modClass_le_one_add_div
          N pair₀.2 a ha

/-- Sharp natural `O(N/q+1)` count with `q = max a b`. -/
theorem channelStartPairs_card_le_one_add_div_maxStep
    (N a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (h : ℤ) :
    (channelStartPairs N a b h).card ≤
      1 + N / Nat.max a b := by
  by_cases habOrder : a ≤ b
  · simpa [Nat.max_eq_right habOrder] using
      channelStartPairs_card_le_one_add_div_firstStep
        N a b ha hb hab h
  · have hba : b ≤ a := le_of_not_ge habOrder
    simpa [Nat.max_eq_left hba] using
      channelStartPairs_card_le_one_add_div_secondStep
        N a b ha hb hab h

/-- Equivalent subtraction-free packing form. -/
theorem maxStep_mul_channelStartPairs_card_sub_one_le
    (N a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (h : ℤ) :
    Nat.max a b * ((channelStartPairs N a b h).card - 1) ≤ N := by
  let q := Nat.max a b
  have hcard :=
    channelStartPairs_card_le_one_add_div_maxStep
      N a b ha hb hab h
  have hpred :
      (channelStartPairs N a b h).card - 1 ≤ N / q := by
    rw [Nat.sub_le_iff_le_add]
    simpa [q, Nat.add_comm] using hcard
  calc
    q * ((channelStartPairs N a b h).card - 1) ≤
        q * (N / q) :=
      Nat.mul_le_mul_left q hpred
    _ ≤ N := Nat.mul_div_le N q

end PaperC
