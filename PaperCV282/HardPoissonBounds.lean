import PaperCV282.FullBandArithmetic
import PaperCV282.DyadicPoissonDistance
import PaperCV282.PoissonIntensityBounds

/-!
# Hard deletion with the actual full-block and retained intensities

A small fraction of deleted starts bounds the retained Stein factor.
The finite algebra preserves the factor lambda on both the exponential
and the polynomial errors, including intensities below one.
-/

namespace PaperC.V282.HardPoissonBounds

open ArratiaGoldsteinGordonInput ConditionalStartProbability ConditionalAGGInstantiation
open ConditionalAGGAverage SectionThirteenFiniteBound SectionTwelveMoments
open MaskedPoissonCritical MaskedArithmeticGeometry MaskedPairGeometry
open MaskedScalarRetained MaskedScalarTransfer MaskedScalarCoupling
open ScalarSteinInput PoissonIntensityBounds AllStartSoftPoisson
open FullBandArithmetic DyadicPoissonDistance TwoWindowParity
open scoped NNReal

noncomputable section

/-- The removed portion of the whole block is precisely the full-support bad set. -/
theorem fullBadMask_block_eq (N L Y : ℕ) :
    fullBadMask N L Y (dyadicBlock N) = fullBadStarts N L Y :=
  Finset.inter_eq_right.mpr (fullBadStarts_subset_block N L Y)

/-- Deleting at most half the block keeps at least half its own target intensity. -/
theorem half_rate_le_retainedRate {N L Y : ℕ} (hN : 0 < N)
    (hbad : ((fullBadStarts N L Y).card : ℝ) / N ≤ 1 / 2) :
    (fullRate N L : ℝ) / 2 ≤ retainedRate N L Y (dyadicBlock N) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hc := card_fullGood_add_card_fullBad N L Y (dyadicBlock N)
  rw [fullBadMask_block_eq, TouchingPairs.card_dyadicBlock] at hc
  have hcr : ((fullGoodMask N L Y (dyadicBlock N)).card : ℝ) +
      (fullBadStarts N L Y).card = N := by exact_mod_cast hc
  have hd : ((fullBadStarts N L Y).card : ℝ) ≤ (N : ℝ) / 2 := by
    have hh := (div_le_iff₀ hn).mp hbad
    linarith
  rw [fullRate_coe, retainedRate_coe]
  have hgood : (N : ℝ) / 2 ≤ (fullGoodMask N L Y (dyadicBlock N)).card := by linarith
  calc
    _ = ((N : ℝ) / 2) / (2 : ℝ) ^ L := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hgood (by positivity)

/-- Numerical reduction after normalizing the genuine four arithmetic costs. -/
theorem hard_normalized_budget_le {rate retained : ℝ≥0} {m d e r u b t : ℝ}
    (hhalf : (rate : ℝ) / 2 ≤ retained) (hb : 0 ≤ b) (ht : 0 ≤ t)
    (hm : m ≤ t) (hd : d ≤ b) (he : e ≤ b) (hu : u ≤ t)
    (hr : r ≤ t * ((rate : ℝ) ^ 2 + 2 * (rate : ℝ))) :
    (rate : ℝ) * (m + 2 * d) +
      2 * firstSteinFactor retained * ((rate : ℝ) ^ 2 * (u + e) + r) ≤
        20 * (rate : ℝ) * (b + t) := by
  have hf0 := firstSteinFactor_nonneg retained
  have hrate0 := rate.coe_nonneg
  have hf := firstSteinFactor_le_twice_of_half_le hhalf
  have hs := firstSteinFactor_mul_square_le rate
  have hrho := firstSteinFactor_mul_square_add_twice_le_three_mul rate
  have hrough : (rate : ℝ) * (m + 2 * d) +
      2 * firstSteinFactor retained * ((rate : ℝ) ^ 2 * (u + e) + r) ≤
      (rate : ℝ) * (t + 2 * b) +
        4 * firstSteinFactor rate *
          ((rate : ℝ) ^ 2 * (t + b) + t * ((rate : ℝ) ^ 2 + 2 * (rate : ℝ))) := by
    calc
      _ ≤ (rate : ℝ) * (t + 2 * b) +
          2 * firstSteinFactor retained *
            ((rate : ℝ) ^ 2 * (t + b) + t * ((rate : ℝ) ^ 2 + 2 * (rate : ℝ))) := by gcongr
      _ ≤ _ := by
        have hbign : 0 ≤ (rate : ℝ) ^ 2 * (t + b) + t * ((rate : ℝ) ^ 2 + 2 * (rate : ℝ)) := by positivity
        have hh := mul_le_mul_of_nonneg_right hf hbign
        nlinarith
  have hs' := mul_le_mul_of_nonneg_right hs (add_nonneg ht hb)
  have hr' := mul_le_mul_of_nonneg_right hrho ht
  have hbt := mul_nonneg hrate0 hb
  have htt := mul_nonneg hrate0 ht
  nlinarith

/-- Exact change of denominator keeps the complete target intensity in the hard budget. -/
theorem hard_budget_normalization (N L Y : ℕ) (hN : 0 < N) :
    ((fullDefectMass L (dyadicBlock N) : ℝ) + 2 * (fullBadStarts N L Y).card) / (2 : ℝ) ^ L +
      2 * firstSteinFactor (retainedRate N L Y (dyadicBlock N)) *
        (((N : ℝ) + (maskedSupportEdges L Y (dyadicBlock N)).card +
          (jointDefectMass N L (separatedPairs (dyadicBlock N) L) : ℝ)) / (2 : ℝ) ^ (2 * L)) =
    (fullRate N L : ℝ) *
        ((fullDefectMass L (dyadicBlock N) : ℝ) / N + 2 * ((fullBadStarts N L Y).card : ℝ) / N) +
      2 * firstSteinFactor (retainedRate N L Y (dyadicBlock N)) *
        ((fullRate N L : ℝ) ^ 2 *
          (1 / (N : ℝ) + ((maskedSupportEdges L Y (dyadicBlock N)).card : ℝ) / (N : ℝ) ^ 2) +
          (jointDefectMass N L (separatedPairs (dyadicBlock N) L) : ℝ) / (2 : ℝ) ^ (2 * L)) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  have hp : (2 : ℝ) ^ L ≠ 0 := by positivity
  rw [fullRate_coe, show 2 * L = L * 2 by omega, pow_mul]
  field_simp

/-- Actual conditional hard transfer from normalized arithmetic estimates. -/
theorem conditionalDistance_le_of_arithmetic (hStein : ScalarSteinFactorsStatement)
    {N L Y : ℕ} {b t : ℝ} (hN : 2 ≤ N) (hL : 0 < L) (hY : 2 * L ≤ Y)
    (hb : 0 ≤ b) (ht : 0 ≤ t)
    (hbad : ((fullBadStarts N L Y).card : ℝ) / N ≤ 1 / 2)
    (hm : (fullDefectMass L (dyadicBlock N) : ℝ) / N ≤ t)
    (hd : ((fullBadStarts N L Y).card : ℝ) / N ≤ b)
    (he : ((maskedSupportEdges L Y (dyadicBlock N)).card : ℝ) / (N : ℝ) ^ 2 ≤ b)
    (hu : 1 / (N : ℝ) ≤ t)
    (hr : (jointDefectMass N L (separatedPairs (dyadicBlock N) L) : ℝ) / (2 : ℝ) ^ (2 * L) ≤
      t * ((fullRate N L : ℝ) ^ 2 + 2 * (fullRate N L : ℝ))) :
    conditionalDistance N L Y ≤ 20 * (fullRate N L : ℝ) * (b + t) := by
  have hh := theorem_four_one_scalar_conditional hStein (dyadicBlock N)
    (Finset.Subset.refl _) hN hL hY
  rw [fullBadMask_block_eq, TouchingPairs.card_dyadicBlock, maskedTargetPoissonRate_block_eq] at hh
  change conditionalDistance N L Y ≤ _ at hh
  rw [hard_budget_normalization N L Y (by omega)] at hh
  apply hh.trans
  have hn : 0 < N := by omega
  simpa only [mul_div_assoc] using hard_normalized_budget_le
    (half_rate_le_retainedRate hn hbad) hb ht hm hd he hu hr

end
end PaperC.V282.HardPoissonBounds
