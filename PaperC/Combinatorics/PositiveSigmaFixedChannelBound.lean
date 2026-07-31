import PaperC.Combinatorics.PositiveSigmaFixedChannelCover
import PaperC.Combinatorics.CanonicalResidualCertificateMassBound

set_option maxHeartbeats 1800000

/-!
# Effective residual bound on one positive canonical channel

This file composes the actual-population cover with the quantitative
Lemma 7.1--7.2 certificate estimate.  For a fixed channel and a fixed
certificate size `r`, it bounds

`4^r · #(pairs)`

by the explicit factorial term.  Summing over sizes gives the finite
exponential majorant used in the `σ>0` branch of Proposition 7.3.
-/

namespace PaperC
namespace PositiveSigmaFixedChannelCover

open scoped BigOperators
open CanonicalResidualComponents
open ResidualComponentCounts

noncomputable section

/-- Explicit fixed-size bound for the actual fixed-channel population. -/
theorem four_pow_mul_card_fixedChannelPairs_le_effective
    {N A L a b r : ℕ} {h : ℤ} (hN : 2 ≤ N)
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hqTwo : 2 ≤ Nat.max a b)
    (hB : 4 ≤ L + 1)
    (hm : 2 ≤ channelUnitCount L a b h) :
    (4 : ℚ) ^ r *
        ((fixedChannelPairs N A L a b h r hN).card : ℚ) ≤
      (((2 * N : ℕ) : ℚ) *
        (((3584 : ℚ) * (L + 1 : ℚ) /
            (Nat.log 2 (L + 1) : ℚ)) ^ r /
          (r.factorial : ℚ))) := by
  refine
    (four_pow_mul_card_fixedChannelPairs_le_solutionMass
      hN hb hm).trans ?_
  apply
    canonicalResidualAmbient_admissibleCertificateSolutionMass_le
      ha hb hab hqTwo hB
  simpa only [channelUnitCount_eq_card_channelCells] using hm

/-- Sum of the effective fixed-channel bounds for all `r < R`. -/
theorem sum_four_pow_mul_card_fixedChannelPairs_le_effective
    {N A L a b R : ℕ} {h : ℤ} (hN : 2 ≤ N)
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hqTwo : 2 ≤ Nat.max a b)
    (hB : 4 ≤ L + 1)
    (hm : 2 ≤ channelUnitCount L a b h) :
    (∑ r ∈ Finset.range R,
        (4 : ℚ) ^ r *
          ((fixedChannelPairs N A L a b h r hN).card : ℚ)) ≤
      (((2 * N : ℕ) : ℚ) *
        ∑ r ∈ Finset.range R,
          ((3584 : ℚ) * (L + 1 : ℚ) /
              (Nat.log 2 (L + 1) : ℚ)) ^ r /
            (r.factorial : ℚ)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r _hr
  exact
    four_pow_mul_card_fixedChannelPairs_le_effective
      hN ha hb hab hqTwo hB hm

/-- Real-exponential form of the summed fixed-channel population bound. -/
theorem sum_four_pow_mul_card_fixedChannelPairs_cast_le_exp
    {N A L a b R : ℕ} {h : ℤ} (hN : 2 ≤ N)
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hqTwo : 2 ≤ Nat.max a b)
    (hB : 4 ≤ L + 1)
    (hm : 2 ≤ channelUnitCount L a b h) :
    ((∑ r ∈ Finset.range R,
        (4 : ℚ) ^ r *
          ((fixedChannelPairs N A L a b h r hN).card : ℚ) : ℚ) : ℝ) ≤
      ((((2 * N : ℕ) : ℚ) : ℝ) *
        Real.exp
          (((3584 : ℚ) * (L + 1 : ℚ) /
            (Nat.log 2 (L + 1) : ℚ) : ℚ) : ℝ)) := by
  have hcover :
      (∑ r ∈ Finset.range R,
          (4 : ℚ) ^ r *
            ((fixedChannelPairs N A L a b h r hN).card : ℚ)) ≤
        ∑ r ∈ Finset.range R,
          CRT.admissibleCertificateSolutionMass
            (Finset.univ :
              Finset (CanonicalResidualAmbientCell L a b h))
            r
            canonicalResidualAmbientLeftResidue
            canonicalResidualAmbientCellModulus
            N (2 * N) N 4 := by
    apply Finset.sum_le_sum
    intro r _hr
    exact
      four_pow_mul_card_fixedChannelPairs_le_solutionMass
        hN hb hm
  have hcoverCast :
      ((∑ r ∈ Finset.range R,
          (4 : ℚ) ^ r *
            ((fixedChannelPairs N A L a b h r hN).card : ℚ) : ℚ) : ℝ) ≤
        ((∑ r ∈ Finset.range R,
          CRT.admissibleCertificateSolutionMass
            (Finset.univ :
              Finset (CanonicalResidualAmbientCell L a b h))
            r
            canonicalResidualAmbientLeftResidue
            canonicalResidualAmbientCellModulus
            N (2 * N) N 4 : ℚ) : ℝ) := by
    exact_mod_cast hcover
  exact hcoverCast.trans
    (sum_canonicalResidualAmbient_admissibleCertificateSolutionMass_cast_le_exp
      (N := N) (R := R) ha hb hab hqTwo hB
      (by simpa only [channelUnitCount_eq_card_channelCells] using hm))

end

end PositiveSigmaFixedChannelCover
end PaperC
