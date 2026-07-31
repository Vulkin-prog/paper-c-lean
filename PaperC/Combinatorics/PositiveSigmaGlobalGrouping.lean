import PaperC.Combinatorics.PositiveSigmaFixedChannelBound
import PaperC.Arithmetic.WeightedResidualChannelMass

set_option maxHeartbeats 2400000

/-!
# Global finite grouping of the positive-systematic population

This file performs the finite bookkeeping needed between the fixed-channel
CRT estimate and the channel mass of Lemma 5.5.  Every active pair with
positive systematic dimension has one canonical key `(q,a,b,h,r)`, where
`q=max(a,b)` and `r=c#`.  The key belongs to an explicit finite set, and
membership in two fixed-channel fibers forces the keys to agree.

The final inequality extracts an explicit uniform envelope `D` for the
corrected-defect count and groups the remaining factors exactly as

`4^D * sum_channels 4^sigma * sum_r 4^r * #(fixed fiber)`.
-/

namespace PaperC
namespace PositiveSigmaGlobalGrouping

open Finset
open scoped BigOperators
open Affine
open Affine.CanonicalRationalCode
open RationalMassFinite
open ResidualMasses
open ResidualComponentCounts
open PositiveSigmaFixedChannelCover

noncomputable section

/-- A plain-data key for a positive canonical channel and a residual size. -/
structure PositiveChannelKey where
  q : ℕ
  a : ℕ
  b : ℕ
  h : ℤ
  r : ℕ
deriving DecidableEq

/-- All channel-size keys which can occur for a separated pair of length `L`. -/
noncomputable def positiveChannelKeys (L : ℕ) :
    Finset PositiveChannelKey :=
  (Icc 2 L).biUnion fun q ↦
    (reducedRatiosAtHeight q).biUnion fun c ↦
      (nontrivialChannelHeights L c.1 c.2).biUnion fun h ↦
        (range (L + 2)).image fun r ↦
          { q := q, a := c.1, b := c.2, h := h, r := r }

@[simp]
theorem mem_positiveChannelKeys
    {L : ℕ} {key : PositiveChannelKey} :
    key ∈ positiveChannelKeys L ↔
      key.q ∈ Icc 2 L ∧
      (key.a, key.b) ∈ reducedRatiosAtHeight key.q ∧
      key.h ∈ nontrivialChannelHeights L key.a key.b ∧
      key.r ∈ range (L + 2) := by
  constructor
  · intro hkey
    simp only [positiveChannelKeys, mem_biUnion, mem_image] at hkey
    obtain ⟨q, hq, c, hc, h, hh, r, hr, hEq⟩ := hkey
    rw [← hEq]
    exact ⟨hq, hc, hh, hr⟩
  · rintro ⟨hq, hc, hh, hr⟩
    simp only [positiveChannelKeys, mem_biUnion, mem_image]
    exact
      ⟨key.q, hq, (key.a, key.b), hc, key.h, hh, key.r, hr, rfl⟩

/-- The fixed population associated with a finite positive-channel key. -/
noncomputable def fixedChannelFiber
    (N A L : ℕ) (hN : 2 ≤ N) (key : PositiveChannelKey) :
    Finset (SeparatedDyadicPair N L) :=
  fixedChannelPairs N A L key.a key.b key.h key.r hN

/--
Two fixed-channel memberships determine exactly the same plain-data key.
Thus the global grouping has no double counting.
-/
theorem key_eq_of_pair_mem_fixedChannelFiber
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L}
    {key₁ key₂ : PositiveChannelKey}
    (hk₁ : key₁ ∈ positiveChannelKeys L)
    (hk₂ : key₂ ∈ positiveChannelKeys L)
    (h₁ : pair ∈ fixedChannelFiber N A L hN key₁)
    (h₂ : pair ∈ fixedChannelFiber N A L hN key₂) :
    key₁ = key₂ := by
  obtain ⟨w₁⟩ := (mem_fixedChannelPairs.mp h₁).2
  obtain ⟨w₂⟩ := (mem_fixedChannelPairs.mp h₂).2
  have hc : w₁.candidate = w₂.candidate := by
    exact Option.some.inj (w₁.choice.symm.trans w₂.choice)
  have hab : (key₁.a, key₁.b) = (key₂.a, key₂.b) :=
    congrArg Subtype.val hc
  have ha : key₁.a = key₂.a := congrArg Prod.fst hab
  have hb : key₁.b = key₂.b := congrArg Prod.snd hab
  have hh : key₁.h = key₂.h := by
    rw [← w₁.error_eq, ← w₂.error_eq, ha, hb]
  have hr : key₁.r = key₂.r := by
    rw [← w₁.count_eq, ← w₂.count_eq]
  have hk₁Data := mem_positiveChannelKeys.mp hk₁
  have hk₂Data := mem_positiveChannelKeys.mp hk₂
  have hq₁ :=
    (mem_reducedRatiosAtHeight.mp hk₁Data.2.1).2.2.2
  have hq₂ :=
    (mem_reducedRatiosAtHeight.mp hk₂Data.2.1).2.2.2
  have hq : key₁.q = key₂.q := by
    rw [← hq₁, ← hq₂, ha, hb]
  cases key₁
  cases key₂
  simp_all

private theorem canonical_key_data
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L}
    (hpair : pair ∈ positiveSigmaSmallProductPairs N A L hN) :
    ∃ c :
        ReducedCandidate pair.1.1 pair.1.2
          (L + 1) ((L + 1) ^ A),
      let q := Nat.max c.1.1 c.1.2
      let h :=
        pairChannelError pair.1.1 pair.1.2 c.1.1 c.1.2
      let r :=
        canonicalResidualComponentCount A pair.1.1 pair.1.2 L
      canonicalReducedCandidate?
          pair.1.1 pair.1.2 (L + 1) ((L + 1) ^ A) = some c ∧
      2 ≤ candidateMultiplicity L c ∧
      ({ q := q, a := c.1.1, b := c.1.2, h := h, r := r } :
          PositiveChannelKey) ∈ positiveChannelKeys L ∧
      pair ∈
        fixedChannelFiber N A L hN
          { q := q, a := c.1.1, b := c.1.2, h := h, r := r } := by
  obtain ⟨c, hchoice, hm, hfixed⟩ :=
    exists_fixedChannelPairs_of_mem_positiveSigmaSmallProductPairs hpair
  let q := Nat.max c.1.1 c.1.2
  let h := pairChannelError pair.1.1 pair.1.2 c.1.1 c.1.2
  let r := canonicalResidualComponentCount A pair.1.1 pair.1.2 L
  have hqPos : 0 < q :=
    (candidate_fst_pos c).trans_le
      (Nat.le_max_left c.1.1 c.1.2)
  have hqL : q ≤ L :=
    candidate_max_le_length_of_two_units c hm
  have hqOneNe : q ≠ 1 := by
    intro hqOne
    have hcells :
        2 ≤
          (channelCells L c.1.1 c.1.2 h).card := by
      simpa [candidateMultiplicity, h] using hm
    have hnear :=
      height_one_primitive_channel_forces_unit_and_nearby
        (candidate_fst_pos c) (candidate_snd_pos c)
        (candidate_coprime c)
        (by simpa [q] using hqOne)
        (h := h) rfl hcells
    have hsep :=
      (mem_separatedDyadicPairs.mp pair.2).2.2
    have hsep' :
        L < Nat.dist pair.1.1 pair.1.2 := by
      simpa only using hsep
    have hnear' :
        Nat.dist pair.1.1 pair.1.2 ≤ L := by
      simpa only using hnear.2.2
    exact (not_le_of_gt hsep') hnear'
  have hqTwo : 2 ≤ q := by omega
  have hc :
      (c.1.1, c.1.2) ∈ reducedRatiosAtHeight q :=
    mem_reducedRatiosAtHeight.mpr
      ⟨candidate_fst_pos c, candidate_snd_pos c,
        candidate_coprime c, rfl⟩
  have hh :
      h ∈ nontrivialChannelHeights L c.1.1 c.1.2 := by
    rw [mem_nontrivialChannelHeights_iff_two_le_card]
    simpa [candidateMultiplicity, h] using hm
  have hxy := pair_coordinates_two_le hN pair
  have hbudget :=
    canonicalCorrected_add_twice_residual_le
      A pair.1.1 pair.1.2 L (by omega) (by omega)
  have hr : r ∈ range (L + 2) := by
    rw [mem_range]
    dsimp [r]
    omega
  refine ⟨c, hchoice, hm, ?_, ?_⟩
  · rw [mem_positiveChannelKeys]
    exact ⟨mem_Icc.mpr ⟨hqTwo, hqL⟩, hc, hh, hr⟩
  · simpa [fixedChannelFiber, q, h, r] using hfixed

/--
Every positive-systematic pair has a unique key in the explicit finite key
set, and belongs to that key's fixed-channel fiber.
-/
theorem existsUnique_key_of_mem_positiveSigmaSmallProductPairs
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L}
    (hpair : pair ∈ positiveSigmaSmallProductPairs N A L hN) :
    ∃! key : PositiveChannelKey,
      key ∈ positiveChannelKeys L ∧
        pair ∈ fixedChannelFiber N A L hN key := by
  obtain ⟨c, _hchoice, _hm, hkey, hfixed⟩ :=
    canonical_key_data hpair
  let key : PositiveChannelKey :=
    { q := Nat.max c.1.1 c.1.2
      a := c.1.1
      b := c.1.2
      h := pairChannelError pair.1.1 pair.1.2 c.1.1 c.1.2
      r := canonicalResidualComponentCount A pair.1.1 pair.1.2 L }
  refine ⟨key, ⟨hkey, hfixed⟩, ?_⟩
  intro other hother
  exact (
    key_eq_of_pair_mem_fixedChannelFiber
      (pair := pair) (key₁ := key) (key₂ := other)
      hkey hother.1 hfixed hother.2).symm

/--
The exact nested channel/certificate mass left after extracting a uniform
corrected-defect factor.
-/
noncomputable def positiveSigmaChannelCertificateMass
    (N A L : ℕ) (hN : 2 ≤ N) : ℕ :=
  ∑ key ∈ positiveChannelKeys L,
    4 ^ channelSigma L key.a key.b key.h *
      4 ^ key.r *
        (fixedChannelFiber N A L hN key).card

private theorem sum_indicator_fixedChannelPairs
    {N A L a b r : ℕ} {h : ℤ} (hN : 2 ≤ N) (W : ℕ) :
    (∑ pair ∈ positiveSigmaSmallProductPairs N A L hN,
        if pair ∈ fixedChannelPairs N A L a b h r hN
          then W else 0) =
      W * (fixedChannelPairs N A L a b h r hN).card := by
  classical
  rw [← Finset.sum_filter]
  have hfilter :
      (positiveSigmaSmallProductPairs N A L hN).filter
          (fun pair ↦
            pair ∈ fixedChannelPairs N A L a b h r hN) =
        fixedChannelPairs N A L a b h r hN := by
    ext pair
    simp only [mem_filter, mem_fixedChannelPairs]
    tauto
  rw [hfilter]
  simp [mul_comm]

/--
Finite global positive-`σ` grouping.  The hypothesis `hD` is the explicit
uniform envelope for `D#`; all systematic and residual-certificate factors
are then summed over the canonical finite channel partition.
-/
theorem positiveSigmaQuadraticResidualMass_le_channelCertificateMass
    {N A L D : ℕ} (hN : 2 ≤ N)
    (hD :
      ∀ pair ∈ positiveSigmaSmallProductPairs N A L hN,
        canonicalCorrectedDefectCount
          A pair.1.1 pair.1.2 L ≤ D) :
    positiveSigmaQuadraticResidualMass N A L hN ≤
      4 ^ D * positiveSigmaChannelCertificateMass N A L hN := by
  classical
  unfold positiveSigmaQuadraticResidualMass quadraticResidualMass
  calc
    (∑ pair ∈ positiveSigmaSmallProductPairs N A L hN,
        quadraticResidualWeight A hN pair) ≤
        ∑ pair ∈ positiveSigmaSmallProductPairs N A L hN,
          ∑ key ∈ positiveChannelKeys L,
            if pair ∈ fixedChannelFiber N A L hN key
              then
                4 ^ D *
                  (4 ^ channelSigma L key.a key.b key.h *
                    4 ^ key.r)
              else 0 := by
      apply Finset.sum_le_sum
      intro pair hpair
      obtain ⟨c, _hchoice, _hm, hkey, hfixed⟩ :=
        canonical_key_data hpair
      let h :=
        pairChannelError pair.1.1 pair.1.2 c.1.1 c.1.2
      let r :=
        canonicalResidualComponentCount A pair.1.1 pair.1.2 L
      have hweight :
          quadraticResidualWeight A hN pair ≤
            4 ^ D * (4 ^ channelSigma L c.1.1 c.1.2 h * 4 ^ r) := by
        have hraw :=
          quadraticResidualWeight_le_systematic_mul_corrected_mul_certificate
            (A := A) hN pair
        have hsigma :=
          pairSigma_eq_channelSigma_of_mem_fixedChannelPairs hfixed
        have hcorrected :
            4 ^ canonicalCorrectedDefectCount
                A pair.1.1 pair.1.2 L ≤ 4 ^ D :=
          Nat.pow_le_pow_right (by norm_num) (hD pair hpair)
        calc
          quadraticResidualWeight A hN pair ≤
              4 ^ pairSigma A pair *
                4 ^ canonicalCorrectedDefectCount
                    A pair.1.1 pair.1.2 L *
                  4 ^ r := by simpa [r] using hraw
          _ ≤
              4 ^ pairSigma A pair * 4 ^ D * 4 ^ r :=
            Nat.mul_le_mul_right _
              (Nat.mul_le_mul_left _ hcorrected)
          _ =
              4 ^ D *
                (4 ^ channelSigma L c.1.1 c.1.2 h * 4 ^ r) := by
            rw [hsigma]
            ring
      refine hweight.trans ?_
      have hsingle :=
        Finset.single_le_sum
          (s := positiveChannelKeys L)
          (f := fun key ↦
            if pair ∈ fixedChannelFiber N A L hN key
              then
                4 ^ D *
                  (4 ^ channelSigma L key.a key.b key.h *
                    4 ^ key.r)
              else 0)
          (fun _ _ ↦ Nat.zero_le _) hkey
      simpa only [hfixed, if_true] using hsingle
    _ =
        4 ^ D * positiveSigmaChannelCertificateMass N A L hN := by
      rw [Finset.sum_comm]
      simp only [fixedChannelFiber]
      simp_rw [sum_indicator_fixedChannelPairs hN]
      unfold positiveSigmaChannelCertificateMass
      simp only [fixedChannelFiber, Finset.mul_sum]
      ring

end

end PositiveSigmaGlobalGrouping
end PaperC
