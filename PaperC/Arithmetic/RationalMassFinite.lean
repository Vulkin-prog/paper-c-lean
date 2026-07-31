import PaperC.Affine.CanonicalRationalCode
import PaperC.Arithmetic.ChannelStartPairs
import PaperC.Arithmetic.HeightTwoPairCount
import PaperC.Arithmetic.WeightedChannelMass

set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000

/-!
# Finite mass of the canonical rational code

This file gives the elementary finite counting estimate behind Proposition
5.4.  We sum the weight `base^σ - 1` over ordered, separated dyadic pairs.
Pairs with positive canonical multiplicity expose their selected reduced
channel.  Height one is incompatible with separation; height two lies in
the frontal rectangle counted by `HeightTwoPairCount`; heights at least
three are covered by the finite channel geometry

`q`, `(a,b)`, `h`, `(x,y)`.

The resulting deliberately coarse bound is

`2(6(L+1)+1)^2 base^(L/2)
  + L(2L)(2L^2+1)(N+1) base^(L/3)`.
-/

namespace PaperC
namespace RationalMassFinite

open scoped BigOperators
open Finset
open Affine
open Affine.CanonicalRationalCode

noncomputable section

/-! ## Pairwise definitions -/

/-- Ordered separated pairs in the dyadic block. -/
def separatedDyadicPairs (N L : ℕ) : Finset (ℕ × ℕ) :=
  ((dyadicBlock N) ×ˢ (dyadicBlock N)).filter fun pair =>
    L < Nat.dist pair.1 pair.2

@[simp]
theorem mem_separatedDyadicPairs
    {N L x y : ℕ} :
    (x, y) ∈ separatedDyadicPairs N L ↔
      x ∈ dyadicBlock N ∧ y ∈ dyadicBlock N ∧
        L < Nat.dist x y := by
  simp [separatedDyadicPairs, and_assoc]

/-- Combinatorial canonical exponent `max(m_ex-1,0)`. -/
noncomputable def canonicalPairSigma
    (A L x y : ℕ) : ℕ :=
  canonicalMultiplicity A L x y - 1

/-- Height of the selected candidate, and zero when no candidate is chosen. -/
noncomputable def canonicalPairHeight
    (A L x y : ℕ) : ℕ :=
  match canonicalReducedCandidate?
      x y (L + 1) ((L + 1) ^ A) with
  | none => 0
  | some c => Nat.max c.1.1 c.1.2

/-- Finite rational mass over separated ordered pairs. -/
noncomputable def rationalMass
    (N A L base : ℕ) : ℕ :=
  ∑ pair ∈ separatedDyadicPairs N L,
    (base ^ canonicalPairSigma A L pair.1 pair.2 - 1)

/-- The combinatorial exponent is exactly the dimension of `S_rat`. -/
theorem canonicalPairSigma_eq_rationalSigma
    (M A L x y : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y) :
    canonicalPairSigma A L x y =
      rationalSigma M A x y L hx hy := by
  symm
  exact
    rationalSigma_eq_canonicalMultiplicity_sub_one
      M A x y L hx hy

theorem two_le_canonicalMultiplicity_of_sigma_pos
    {A L x y : ℕ}
    (hsigma : 0 < canonicalPairSigma A L x y) :
    2 ≤ canonicalMultiplicity A L x y := by
  unfold canonicalPairSigma at hsigma
  omega

/-- Identify the combinatorial sigma with the selected channel's sigma. -/
theorem canonicalPairSigma_eq_channelSigma_of_choice
    {A L x y : ℕ}
    {c : ReducedCandidate
      x y (L + 1) ((L + 1) ^ A)}
    (hchoice :
      canonicalReducedCandidate?
          x y (L + 1) ((L + 1) ^ A) =
        some c) :
    canonicalPairSigma A L x y =
      channelSigma L c.1.1 c.1.2
        (pairChannelError x y c.1.1 c.1.2) := by
  simp [canonicalPairSigma, canonicalMultiplicity,
    hchoice, candidateMultiplicity, channelSigma]

theorem canonicalPairHeight_eq_of_choice
    {A L x y : ℕ}
    {c : ReducedCandidate
      x y (L + 1) ((L + 1) ^ A)}
    (hchoice :
      canonicalReducedCandidate?
          x y (L + 1) ((L + 1) ^ A) =
        some c) :
    canonicalPairHeight A L x y =
      Nat.max c.1.1 c.1.2 := by
  simp [canonicalPairHeight, hchoice]

/-! ## The large-height geometric cover -/

/-- Start pairs covered by one reduced coefficient pair and all its
nontrivial affine parameters. -/
def largeChannelPairCoverAtRatio
    (N L a b : ℕ) : Finset (ℕ × ℕ) :=
  (nontrivialChannelHeights L a b).biUnion fun h =>
    channelStartPairs N a b h

/-- Start pairs covered by all reduced ratios of one height. -/
def largeChannelPairCoverAtHeight
    (N L q : ℕ) : Finset (ℕ × ℕ) :=
  (reducedRatiosAtHeight q).biUnion fun c =>
    largeChannelPairCoverAtRatio N L c.1 c.2

/-- All nontrivial channel geometries of height `3 ≤ q ≤ L`. -/
def largeChannelPairCover
    (N L : ℕ) : Finset (ℕ × ℕ) :=
  (Icc 3 L).biUnion fun q =>
    largeChannelPairCoverAtHeight N L q

/-! ## Cardinality of the large-height cover -/

theorem card_largeChannelPairCoverAtRatio_le
    {N L q a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hmax : Nat.max a b = q) (hqL : q ≤ L) :
    (largeChannelPairCoverAtRatio N L a b).card ≤
      (((2 * L) * L + 1) * (N + 1)) := by
  unfold largeChannelPairCoverAtRatio
  have hstart :
      ∀ h ∈ nontrivialChannelHeights L a b,
        (channelStartPairs N a b h).card ≤ N + 1 := by
    intro h _hh
    have hcard :=
      channelStartPairs_card_le_one_add_div_maxStep
        N a b ha hb hab h
    rw [hmax] at hcard
    have hdiv : N / q ≤ N := Nat.div_le_self N q
    omega
  have hunion :
      ((nontrivialChannelHeights L a b).biUnion fun h =>
          channelStartPairs N a b h).card ≤
        (nontrivialChannelHeights L a b).card * (N + 1) :=
    Finset.card_biUnion_le_card_mul
      (nontrivialChannelHeights L a b)
      (fun h => channelStartPairs N a b h)
      (N + 1) hstart
  have habSum : a + b ≤ 2 * L := by
    have haL : a ≤ L := by
      exact (Nat.le_max_left a b).trans
        (hmax.le.trans hqL)
    have hbL : b ≤ L := by
      exact (Nat.le_max_right a b).trans
        (hmax.le.trans hqL)
    omega
  have hheights :
      (nontrivialChannelHeights L a b).card ≤
        (2 * L) * L + 1 := by
    calc
      (nontrivialChannelHeights L a b).card ≤
          (channelHeights L a b).card :=
        Finset.card_filter_le _ _
      _ ≤ (a + b) * L + 1 :=
        channelHeights_card_le L a b
      _ ≤ (2 * L) * L + 1 :=
        Nat.add_le_add_right
          (Nat.mul_le_mul_right L habSum) 1
  exact hunion.trans
    (Nat.mul_le_mul_right (N + 1) hheights)

theorem card_largeChannelPairCoverAtHeight_le
    {N L q : ℕ} (_hq : 3 ≤ q) (hqL : q ≤ L) :
    (largeChannelPairCoverAtHeight N L q).card ≤
      (2 * L) * ((((2 * L) * L + 1) * (N + 1))) := by
  unfold largeChannelPairCoverAtHeight
  let W := ((2 * L) * L + 1) * (N + 1)
  have hratio :
      ∀ c ∈ reducedRatiosAtHeight q,
        (largeChannelPairCoverAtRatio N L c.1 c.2).card ≤ W := by
    intro c hc
    obtain ⟨ha, hb, hab, hmax⟩ :=
      mem_reducedRatiosAtHeight.mp hc
    exact card_largeChannelPairCoverAtRatio_le
      ha hb hab hmax hqL
  have hunion :
      ((reducedRatiosAtHeight q).biUnion fun c =>
          largeChannelPairCoverAtRatio N L c.1 c.2).card ≤
        (reducedRatiosAtHeight q).card * W :=
    Finset.card_biUnion_le_card_mul
      (reducedRatiosAtHeight q)
      (fun c => largeChannelPairCoverAtRatio N L c.1 c.2)
      W hratio
  have hratios :
      (reducedRatiosAtHeight q).card ≤ 2 * L :=
    (card_reducedRatiosAtHeight_le q).trans
      (Nat.mul_le_mul_left 2 hqL)
  exact hunion.trans
    (Nat.mul_le_mul_right W hratios)

theorem card_largeChannelPairCover_le
    (N L : ℕ) :
    (largeChannelPairCover N L).card ≤
      L * (2 * L) * ((2 * L) * L + 1) * (N + 1) := by
  unfold largeChannelPairCover
  let W := (2 * L) * (((2 * L) * L + 1) * (N + 1))
  have hheight :
      ∀ q ∈ Icc 3 L,
        (largeChannelPairCoverAtHeight N L q).card ≤ W := by
    intro q hq
    obtain ⟨hq3, hqL⟩ := Finset.mem_Icc.mp hq
    exact card_largeChannelPairCoverAtHeight_le hq3 hqL
  have hunion :
      ((Icc 3 L).biUnion fun q =>
          largeChannelPairCoverAtHeight N L q).card ≤
        (Icc 3 L).card * W :=
    Finset.card_biUnion_le_card_mul
      (Icc 3 L)
      (fun q => largeChannelPairCoverAtHeight N L q)
      W hheight
  have hcard : (Icc 3 L).card ≤ L := by
    simp [Nat.card_Icc]
  calc
    ((Icc 3 L).biUnion fun q =>
        largeChannelPairCoverAtHeight N L q).card ≤
        (Icc 3 L).card * W :=
      hunion
    _ ≤ L * W :=
      Nat.mul_le_mul_right W hcard
    _ = L * (2 * L) * ((2 * L) * L + 1) * (N + 1) := by
      simp [W, Nat.mul_assoc]

/-! ## Coverage of a positive canonical weight -/

theorem pair_mem_heightTwoBoundaryPairs_of_choice
    {N A L x y : ℕ}
    {c : ReducedCandidate
      x y (L + 1) ((L + 1) ^ A)}
    (hpair : (x, y) ∈ separatedDyadicPairs N L)
    (hmax : Nat.max c.1.1 c.1.2 = 2) :
    (x, y) ∈ heightTwoBoundaryPairs N (L + 1) := by
  obtain ⟨hx, hy, _hsep⟩ :=
    mem_separatedDyadicPairs.mp hpair
  obtain ⟨ha, hb, _haH, _hbH, hab, hclose⟩ :=
    mem_reducedChannelCandidates.mp c.2
  rcases positive_coprime_pair_of_max_eq_two
      ha hb hab hmax with
    hforward | hbackward
  · rw [mem_heightTwoBoundaryPairs]
    exact Or.inl
      ⟨hx, hy, by
        simpa [hforward.1, hforward.2] using hclose⟩
  · rw [mem_heightTwoBoundaryPairs]
    exact Or.inr
      ⟨hx, hy, by
        simpa [hbackward.1, hbackward.2] using hclose⟩

theorem pair_mem_largeChannelPairCover_of_choice
    {N A L x y : ℕ}
    {c : ReducedCandidate
      x y (L + 1) ((L + 1) ^ A)}
    (hpair : (x, y) ∈ separatedDyadicPairs N L)
    (hm : 2 ≤ candidateMultiplicity L c)
    (hq3 : 3 ≤ Nat.max c.1.1 c.1.2)
    (hqL : Nat.max c.1.1 c.1.2 ≤ L) :
    (x, y) ∈ largeChannelPairCover N L := by
  obtain ⟨hx, hy, _hsep⟩ :=
    mem_separatedDyadicPairs.mp hpair
  obtain ⟨ha, hb, _haH, _hbH, hab, _hclose⟩ :=
    mem_reducedChannelCandidates.mp c.2
  let q := Nat.max c.1.1 c.1.2
  let h := pairChannelError x y c.1.1 c.1.2
  have hc :
      (c.1.1, c.1.2) ∈ reducedRatiosAtHeight q :=
    mem_reducedRatiosAtHeight.mpr
      ⟨ha, hb, hab, rfl⟩
  have hcells :
      2 ≤ (channelCells L c.1.1 c.1.2 h).card := by
    simpa [candidateMultiplicity, h] using hm
  have hheight :
      h ∈ nontrivialChannelHeights L c.1.1 c.1.2 := by
    rw [mem_nontrivialChannelHeights]
    refine ⟨?_, hcells⟩
    apply channelCells_nonempty_iff_mem_channelHeights.mp
    exact Finset.card_pos.mp (by omega)
  have hstart :
      (x, y) ∈ channelStartPairs N c.1.1 c.1.2 h :=
    mem_channelStartPairs.mpr ⟨hx, hy, rfl⟩
  simp only [largeChannelPairCover,
    largeChannelPairCoverAtHeight,
    largeChannelPairCoverAtRatio,
    Finset.mem_biUnion]
  refine ⟨q, ?_, c.1, hc, h, hheight, hstart⟩
  exact Finset.mem_Icc.mpr ⟨hq3, hqL⟩

/-- Weight of a selected nontrivial candidate at its exact height. -/
theorem canonicalPairWeight_le_pow_div_of_choice
    {A L base x y : ℕ}
    {c : ReducedCandidate
      x y (L + 1) ((L + 1) ^ A)}
    (hbase : 1 ≤ base)
    (hchoice :
      canonicalReducedCandidate?
          x y (L + 1) ((L + 1) ^ A) =
        some c) :
    base ^ canonicalPairSigma A L x y - 1 ≤
      base ^ (L / Nat.max c.1.1 c.1.2) := by
  have hsigma :
      canonicalPairSigma A L x y =
        channelSigma L c.1.1 c.1.2
          (pairChannelError x y c.1.1 c.1.2) :=
    canonicalPairSigma_eq_channelSigma_of_choice hchoice
  have hsigmaLe :
      canonicalPairSigma A L x y ≤
        L / Nat.max c.1.1 c.1.2 := by
    rw [hsigma]
    exact channelSigma_le_div_maxStep
      L c.1.1 c.1.2
      (candidate_fst_pos c) (candidate_snd_pos c)
      (candidate_coprime c)
      (pairChannelError x y c.1.1 c.1.2)
  exact (Nat.sub_le _ _).trans
    (Nat.pow_le_pow_right hbase hsigmaLe)

/--
Pointwise weighted coverage: every positive canonical weight is charged
either to the frontal height-two set or to the enumerated `q ≥ 3` cover.
-/
theorem canonicalPairWeight_le_coverWeights
    {N A L base x y : ℕ}
    (hbase : 1 ≤ base)
    (hpair : (x, y) ∈ separatedDyadicPairs N L) :
    base ^ canonicalPairSigma A L x y - 1 ≤
      (if (x, y) ∈ heightTwoBoundaryPairs N (L + 1) then
          base ^ (L / 2)
        else 0) +
      (if (x, y) ∈ largeChannelPairCover N L then
          base ^ (L / 3)
        else 0) := by
  by_cases hsigma : canonicalPairSigma A L x y = 0
  · simp [hsigma]
  · have hsigmaPos : 0 < canonicalPairSigma A L x y :=
      Nat.pos_of_ne_zero hsigma
    have hmCanonical :
        2 ≤ canonicalMultiplicity A L x y :=
      two_le_canonicalMultiplicity_of_sigma_pos hsigmaPos
    obtain ⟨c, hchoice, hm⟩ :=
      exists_canonical_candidate_of_two_le_multiplicity
        hmCanonical
    let q := Nat.max c.1.1 c.1.2
    have hqPos : 0 < q :=
      (candidate_fst_pos c).trans_le
        (Nat.le_max_left c.1.1 c.1.2)
    have hqL : q ≤ L :=
      candidate_max_le_length_of_two_units c hm
    have hweight :
        base ^ canonicalPairSigma A L x y - 1 ≤
          base ^ (L / q) := by
      simpa [q] using
        canonicalPairWeight_le_pow_div_of_choice
          hbase hchoice
    by_cases hqTwo : q = 2
    · have hmem :
          (x, y) ∈ heightTwoBoundaryPairs N (L + 1) :=
        pair_mem_heightTwoBoundaryPairs_of_choice
          hpair (by simpa [q] using hqTwo)
      have hweightTwo :
          base ^ canonicalPairSigma A L x y - 1 ≤
            base ^ (L / 2) := by
        simpa [hqTwo] using hweight
      rw [if_pos hmem]
      omega
    · have hqOneNe : q ≠ 1 := by
        intro hqOne
        have hcells :
            2 ≤ (channelCells L c.1.1 c.1.2
              (pairChannelError x y c.1.1 c.1.2)).card := by
          simpa [candidateMultiplicity] using hm
        have hnear :=
          height_one_primitive_channel_forces_unit_and_nearby
            (candidate_fst_pos c) (candidate_snd_pos c)
            (candidate_coprime c)
            (by simpa [q] using hqOne)
            (h := pairChannelError x y c.1.1 c.1.2)
            rfl hcells
        have hsep :=
          (mem_separatedDyadicPairs.mp hpair).2.2
        omega
      have hq3 : 3 ≤ q := by omega
      have hmem :
          (x, y) ∈ largeChannelPairCover N L :=
        pair_mem_largeChannelPairCover_of_choice
          hpair hm (by simpa [q] using hq3)
            (by simpa [q] using hqL)
      have hquotient : L / q ≤ L / 3 :=
        Nat.div_le_div_left hq3 (by omega)
      have hweightThree :
          base ^ canonicalPairSigma A L x y - 1 ≤
            base ^ (L / 3) :=
        hweight.trans
          (Nat.pow_le_pow_right hbase hquotient)
      rw [if_pos hmem]
      omega

/-! ## Summing the pointwise cover -/

private theorem sum_ite_mem_le_card_mul
    {α : Type*} [DecidableEq α]
    (s t : Finset α) (W : ℕ) :
    (∑ x ∈ s, if x ∈ t then W else 0) ≤ t.card * W := by
  classical
  have hsubset :
      s.filter (fun x => x ∈ t) ⊆ t := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  calc
    (∑ x ∈ s, if x ∈ t then W else 0) =
        ∑ x ∈ s.filter (fun x => x ∈ t), W := by
      rw [Finset.sum_filter]
    _ = (s.filter (fun x => x ∈ t)).card * W := by
      simp
    _ ≤ t.card * W :=
      Nat.mul_le_mul_right W (Finset.card_le_card hsubset)

/--
Finite rational-mass bound with the exceptional height two separated from
all heights at least three.
-/
theorem rationalMass_le
    (N A L base : ℕ) (_hA : 1 ≤ A) (hbase : 1 ≤ base) :
    rationalMass N A L base ≤
      2 * (6 * (L + 1) + 1) ^ 2 * base ^ (L / 2) +
        L * (2 * L) * ((2 * L) * L + 1) * (N + 1) *
          base ^ (L / 3) := by
  let W₂ := base ^ (L / 2)
  let W₃ := base ^ (L / 3)
  have hpoint :
      ∀ pair ∈ separatedDyadicPairs N L,
        base ^ canonicalPairSigma A L pair.1 pair.2 - 1 ≤
          (if pair ∈ heightTwoBoundaryPairs N (L + 1) then
              W₂ else 0) +
          (if pair ∈ largeChannelPairCover N L then
              W₃ else 0) := by
    intro pair hpair
    rcases pair with ⟨x, y⟩
    exact canonicalPairWeight_le_coverWeights hbase hpair
  have hsum :
      rationalMass N A L base ≤
        (∑ pair ∈ separatedDyadicPairs N L,
          if pair ∈ heightTwoBoundaryPairs N (L + 1) then
            W₂ else 0) +
        ∑ pair ∈ separatedDyadicPairs N L,
          if pair ∈ largeChannelPairCover N L then
            W₃ else 0 := by
    unfold rationalMass
    calc
      (∑ pair ∈ separatedDyadicPairs N L,
          (base ^ canonicalPairSigma A L pair.1 pair.2 - 1)) ≤
          ∑ pair ∈ separatedDyadicPairs N L,
            ((if pair ∈ heightTwoBoundaryPairs N (L + 1) then
                W₂ else 0) +
              (if pair ∈ largeChannelPairCover N L then
                W₃ else 0)) :=
        by
          simpa only using
            (Finset.sum_le_sum fun pair hpair =>
              hpoint pair hpair)
      _ = (∑ pair ∈ separatedDyadicPairs N L,
            if pair ∈ heightTwoBoundaryPairs N (L + 1) then
              W₂ else 0) +
          ∑ pair ∈ separatedDyadicPairs N L,
            if pair ∈ largeChannelPairCover N L then
              W₃ else 0 := by
        rw [Finset.sum_add_distrib]
  have htwo :
      (∑ pair ∈ separatedDyadicPairs N L,
        if pair ∈ heightTwoBoundaryPairs N (L + 1) then
          W₂ else 0) ≤
        2 * (6 * (L + 1) + 1) ^ 2 * W₂ := by
    exact
      (sum_ite_mem_le_card_mul
        (separatedDyadicPairs N L)
        (heightTwoBoundaryPairs N (L + 1)) W₂).trans
      (Nat.mul_le_mul_right W₂
        (card_heightTwoBoundaryPairs_le N (L + 1)))
  have hlarge :
      (∑ pair ∈ separatedDyadicPairs N L,
        if pair ∈ largeChannelPairCover N L then
          W₃ else 0) ≤
        (L * (2 * L) * ((2 * L) * L + 1) * (N + 1)) *
          W₃ := by
    exact
      (sum_ite_mem_le_card_mul
        (separatedDyadicPairs N L)
        (largeChannelPairCover N L) W₃).trans
      (Nat.mul_le_mul_right W₃
        (card_largeChannelPairCover_le N L))
  calc
    rationalMass N A L base ≤
        (∑ pair ∈ separatedDyadicPairs N L,
          if pair ∈ heightTwoBoundaryPairs N (L + 1) then
            W₂ else 0) +
        ∑ pair ∈ separatedDyadicPairs N L,
          if pair ∈ largeChannelPairCover N L then
            W₃ else 0 :=
      hsum
    _ ≤ 2 * (6 * (L + 1) + 1) ^ 2 * W₂ +
          (L * (2 * L) * ((2 * L) * L + 1) * (N + 1)) *
            W₃ :=
      Nat.add_le_add htwo hlarge
    _ = 2 * (6 * (L + 1) + 1) ^ 2 * base ^ (L / 2) +
          L * (2 * L) * ((2 * L) * L + 1) * (N + 1) *
            base ^ (L / 3) := by
      simp [W₂, W₃, Nat.mul_assoc]

end

end RationalMassFinite
end PaperC
