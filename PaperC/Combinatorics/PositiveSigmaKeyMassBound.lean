import PaperC.Combinatorics.PositiveSigmaGlobalGrouping
import PaperC.Asymptotics.ResidualCertificateMassCritical

set_option maxHeartbeats 2400000

/-!
# Bounding the positive-channel key mass

This file closes the finite reindexing step after
`PositiveSigmaGlobalGrouping`.  The explicit key set stores all five
coordinates `(q,a,b,h,r)`, so its systematic-weight sum is exactly
`(L+2) * weightedChannelMass L`.  The fixed-channel certificate estimate
then bounds the full key mass by the same factor times the uniform residual
envelope.
-/

namespace PaperC
namespace PositiveSigmaKeyMassBound

open Finset
open scoped BigOperators
open ResidualComponentCounts
open PositiveSigmaFixedChannelCover
open PositiveSigmaGlobalGrouping

noncomputable section

private def keysAtChannel
    (L q a b : ℕ) (h : ℤ) : Finset PositiveChannelKey :=
  (range (L + 2)).image fun r ↦
    { q := q, a := a, b := b, h := h, r := r }

private def keysAtRatio
    (L q : ℕ) (c : ℕ × ℕ) : Finset PositiveChannelKey :=
  (nontrivialChannelHeights L c.1 c.2).biUnion fun h ↦
    keysAtChannel L q c.1 c.2 h

private def keysAtHeight
    (L q : ℕ) : Finset PositiveChannelKey :=
  (reducedRatiosAtHeight q).biUnion fun c ↦
    keysAtRatio L q c

private theorem positiveChannelKeys_eq (L : ℕ) :
    positiveChannelKeys L =
      (Icc 2 L).biUnion fun q ↦ keysAtHeight L q := by
  rfl

private theorem pairwiseDisjoint_keysAtChannel
    (L q a b : ℕ) :
    (↑(nontrivialChannelHeights L a b) : Set ℤ).PairwiseDisjoint
      (fun h ↦ keysAtChannel L q a b h) := by
  intro h _hh h' _hh' hne
  change Disjoint
    (keysAtChannel L q a b h) (keysAtChannel L q a b h')
  rw [Finset.disjoint_left]
  intro key hkey hkey'
  simp only [keysAtChannel, Finset.mem_image] at hkey hkey'
  obtain ⟨r, _hr, hEq⟩ := hkey
  obtain ⟨r', _hr', hEq'⟩ := hkey'
  have := congrArg PositiveChannelKey.h (hEq.trans hEq'.symm)
  exact hne (by simpa using this)

private theorem pairwiseDisjoint_keysAtRatio
    (L q : ℕ) :
    (↑(reducedRatiosAtHeight q) : Set (ℕ × ℕ)).PairwiseDisjoint
      (fun c ↦ keysAtRatio L q c) := by
  intro c _hc c' _hc' hne
  change Disjoint (keysAtRatio L q c) (keysAtRatio L q c')
  rw [Finset.disjoint_left]
  intro key hkey hkey'
  simp only [keysAtRatio, Finset.mem_biUnion] at hkey hkey'
  obtain ⟨h, _hh, hk⟩ := hkey
  obtain ⟨h', _hh', hk'⟩ := hkey'
  simp only [keysAtChannel, Finset.mem_image] at hk hk'
  obtain ⟨r, _hr, hEq⟩ := hk
  obtain ⟨r', _hr', hEq'⟩ := hk'
  have ha :=
    congrArg PositiveChannelKey.a (hEq.trans hEq'.symm)
  have hb :=
    congrArg PositiveChannelKey.b (hEq.trans hEq'.symm)
  apply hne
  apply Prod.ext
  · simpa using ha
  · simpa using hb

private theorem pairwiseDisjoint_keysAtHeight
    (L : ℕ) :
    (↑(Icc 2 L) : Set ℕ).PairwiseDisjoint
      (keysAtHeight L) := by
  intro q _hq q' _hq' hne
  change Disjoint (keysAtHeight L q) (keysAtHeight L q')
  rw [Finset.disjoint_left]
  intro key hkey hkey'
  simp only [keysAtHeight, Finset.mem_biUnion,
    keysAtRatio, keysAtChannel, Finset.mem_image] at hkey hkey'
  obtain ⟨c, _hc, h, _hh, r, _hr, hEq⟩ := hkey
  obtain ⟨c', _hc', h', _hh', r', _hr', hEq'⟩ := hkey'
  have hqEq :=
    congrArg PositiveChannelKey.q (hEq.trans hEq'.symm)
  exact hne (by simpa using hqEq)

private theorem sum_keysAtChannel_weight
    (L q a b : ℕ) (h : ℤ) :
    (∑ key ∈ keysAtChannel L q a b h,
        4 ^ channelSigma L key.a key.b key.h) =
      (L + 2) * 4 ^ channelSigma L a b h := by
  unfold keysAtChannel
  rw [Finset.sum_image]
  · simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    change (L + 2) * 4 ^ channelSigma L a b h =
      (L + 2) * 4 ^ channelSigma L a b h
    rfl
  · intro r _hr r' _hr' hEq
    exact congrArg PositiveChannelKey.r hEq

/-- The finite `r`-multiplicity of the key set is exactly `L+2`. -/
theorem sum_four_pow_channelSigma_positiveChannelKeys
    (L : ℕ) :
    (∑ key ∈ positiveChannelKeys L,
        4 ^ channelSigma L key.a key.b key.h) =
      (L + 2) * weightedChannelMass L := by
  rw [positiveChannelKeys_eq]
  rw [Finset.sum_biUnion (pairwiseDisjoint_keysAtHeight L)]
  unfold keysAtHeight
  simp_rw [Finset.sum_biUnion (pairwiseDisjoint_keysAtRatio L _)]
  unfold keysAtRatio
  simp_rw [Finset.sum_biUnion
    (pairwiseDisjoint_keysAtChannel L _ _ _)]
  simp_rw [sum_keysAtChannel_weight]
  unfold weightedChannelMass weightedChannelMassAtHeight
    weightedChannelMassAtPair
  simp only [Finset.mul_sum]

private theorem fixed_key_certificate_cast_le_envelope
    {N A L : ℕ} (hN : 2 ≤ N) (hB : 4 ≤ L + 1)
    {key : PositiveChannelKey}
    (hkey : key ∈ positiveChannelKeys L) :
    (((4 : ℚ) ^ key.r *
        ((fixedChannelFiber N A L hN key).card : ℚ) : ℚ) : ℝ) ≤
      residualCertificateChannelEnvelope N L := by
  have hdata := mem_positiveChannelKeys.mp hkey
  have hqBounds := Finset.mem_Icc.mp hdata.1
  obtain ⟨ha, hb, hab, hmax⟩ :=
    mem_reducedRatiosAtHeight.mp hdata.2.1
  have hm :
      2 ≤ channelUnitCount L key.a key.b key.h := by
    rw [channelUnitCount_eq_card_channelCells]
    exact
      mem_nontrivialChannelHeights_iff_two_le_card.mp
        hdata.2.2.1
  have hterm :
      ((4 : ℚ) ^ key.r *
          ((fixedChannelPairs N A L key.a key.b key.h key.r hN).card : ℚ)) ≤
        ∑ r ∈ range (L + 2),
          (4 : ℚ) ^ r *
            ((fixedChannelPairs N A L key.a key.b key.h r hN).card : ℚ) := by
    exact
      Finset.single_le_sum
        (s := range (L + 2))
        (f := fun r ↦
          (4 : ℚ) ^ r *
            ((fixedChannelPairs N A L key.a key.b key.h r hN).card : ℚ))
        (fun _ _ ↦ by positivity) hdata.2.2.2
  have htermCast :
      (((4 : ℚ) ^ key.r *
          ((fixedChannelPairs N A L key.a key.b key.h key.r hN).card : ℚ) :
            ℚ) : ℝ) ≤
        ((∑ r ∈ range (L + 2),
          (4 : ℚ) ^ r *
            ((fixedChannelPairs N A L key.a key.b key.h r hN).card : ℚ) :
              ℚ) : ℝ) := by
    exact_mod_cast hterm
  refine htermCast.trans ?_
  have heffective :=
    sum_four_pow_mul_card_fixedChannelPairs_cast_le_exp
      (N := N) (A := A) (L := L)
      (a := key.a) (b := key.b) (R := L + 2) (h := key.h)
      hN ha hb hab (by simpa [hmax] using hqBounds.1) hB hm
  push_cast at heffective ⊢
  simpa [residualCertificateChannelEnvelope] using heffective

/--
The global key mass costs at most one factor `L+2` beyond the systematic
channel mass; every key receives the uniform one-channel residual envelope.
-/
theorem positiveSigmaChannelCertificateMass_cast_le
    {N A L : ℕ} (hN : 2 ≤ N) (hB : 4 ≤ L + 1) :
    (positiveSigmaChannelCertificateMass N A L hN : ℝ) ≤
      ((L : ℝ) + 2) *
        (weightedChannelMass L : ℝ) *
          residualCertificateChannelEnvelope N L := by
  unfold positiveSigmaChannelCertificateMass
  push_cast
  calc
    (∑ key ∈ positiveChannelKeys L,
        (4 : ℝ) ^ channelSigma L key.a key.b key.h *
          (4 : ℝ) ^ key.r *
            ((fixedChannelFiber N A L hN key).card : ℝ)) ≤
        ∑ key ∈ positiveChannelKeys L,
          (4 : ℝ) ^ channelSigma L key.a key.b key.h *
            residualCertificateChannelEnvelope N L := by
      apply Finset.sum_le_sum
      intro key hkey
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left
      · have hkbound :=
          fixed_key_certificate_cast_le_envelope
            (A := A) hN hB hkey
        push_cast at hkbound
        simpa only [fixedChannelFiber] using hkbound
      · positivity
    _ =
        ((L : ℝ) + 2) *
          (weightedChannelMass L : ℝ) *
            residualCertificateChannelEnvelope N L := by
      rw [← Finset.sum_mul]
      have hsumReal :
          (∑ key ∈ positiveChannelKeys L,
              (4 : ℝ) ^ channelSigma L key.a key.b key.h) =
            ((L : ℝ) + 2) * (weightedChannelMass L : ℝ) := by
        exact_mod_cast
          sum_four_pow_channelSigma_positiveChannelKeys L
      rw [hsumReal]

end

end PositiveSigmaKeyMassBound
end PaperC
