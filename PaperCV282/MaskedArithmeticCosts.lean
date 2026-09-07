import PaperCV282.MaskedBadMass
import PaperCV282.MaskedPairBounds
import PaperCV282.MaskedArithmeticAverages

/-!
# The manuscript-facing masked arithmetic costs

These are real bounds for the actual conditional indicator family used by
the scalar and field transfers. The mask, support edges, relation weights
and own good-site mean remain literal. Only fixed numerical constants are
combined; no full-block replacement or critical-window premise is used.
-/

namespace PaperC.V282.MaskedArithmeticCosts

open MaskedArithmeticGeometry MaskedPairGeometry MaskedPairBounds MaskedBadMass
open MaskedArithmeticAverages LargePrimeDependencyGraph MaskedPoissonCritical
open ConditionalStartProbability ConditionalAGGInstantiation ArratiaGoldsteinGordonInput
open SectionThirteenFiniteBound SectionTwelveMoments TwoWindowParity

noncomputable section

/-- Pointwise conditional b1 with the original mask cardinality and its ordered support edges. -/
theorem bOne_fullGoodMask_le {N L Y : ℕ} (mask : Finset ℕ)
    (hmask : mask ⊆ dyadicBlock N) (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (sigma : SmallSample (dyadicCutoff N L) Y) :
    bOne (largeUniformPMF (dyadicCutoff N L) Y)
      (maskedConditionedGoodIndicator N L Y (fullGoodMask N L Y mask) sigma)
      (largePrimeDependencyGraph N L Y) ≤
        ((mask.card : ℝ) + (maskedSupportEdges L Y mask).card) / (2 : ℝ) ^ (2 * L) := by
  rw [bOne_fullGoodMask_eq mask hmask hN hL hLY sigma]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h := card_closedPairs_le_mask_support N L Y mask
  rw [card_fullMaskedClosedPairs] at h
  exact_mod_cast h

/-- Averaging b1 does not change its exact induced-pair cardinal formula. -/
theorem average_bOne_fullGoodMask_eq {N L Y : ℕ} (mask : Finset ℕ)
    (hmask : mask ⊆ dyadicBlock N) (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y) :
    finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
      bOne (largeUniformPMF (dyadicCutoff N L) Y)
        (maskedConditionedGoodIndicator N L Y (fullGoodMask N L Y mask) sigma)
        (largePrimeDependencyGraph N L Y)) =
      ((fullGoodMask N L Y mask).card + (fullMaskedEdges N L Y mask).card : ℝ) / (2 : ℝ) ^ (2 * L) := by
  simp_rw [bOne_fullGoodMask_eq mask hmask hN hL hLY]
  simp [finiteUniformAverage]

/-- The exact averaged b2 pays only E_Y(mask)+R2(mask), including the touching baseline. -/
theorem average_bTwo_fullGoodMask_le {N L Y : ℕ} (mask : Finset ℕ)
    (hmask : mask ⊆ dyadicBlock N) (hN : 2 ≤ N) (hL : 0 < L) (hY : 2 * L ≤ Y) :
    finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
      bTwo (largeUniformPMF (dyadicCutoff N L) Y)
        (maskedConditionedGoodIndicator N L Y (fullGoodMask N L Y mask) sigma)
        (largePrimeDependencyGraph N L Y)) ≤
      ((maskedSupportEdges L Y mask).card +
        (jointDefectMass N L (separatedPairs mask L) : ℕ) : ℝ) / (2 : ℝ) ^ (2 * L) := by
  rw [average_bTwo_fullGoodMask_eq mask hmask]
  have h := (Rat.cast_le (K := ℝ)).mpr
    (jointPairMass_fullEdges_le_support mask hN hL hY hmask)
  simpa only [Rat.cast_div, Rat.cast_add, Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat] using h

/-- Combined exact arithmetic budget for the genuine conditional Stein terms. -/
theorem average_stein_terms_le {N L Y : ℕ} (mask : Finset ℕ)
    (hmask : mask ⊆ dyadicBlock N) (hN : 2 ≤ N) (hL : 0 < L) (hY : 2 * L ≤ Y) :
    finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
      bOne (largeUniformPMF (dyadicCutoff N L) Y)
        (maskedConditionedGoodIndicator N L Y (fullGoodMask N L Y mask) sigma)
        (largePrimeDependencyGraph N L Y) +
      bTwo (largeUniformPMF (dyadicCutoff N L) Y)
        (maskedConditionedGoodIndicator N L Y (fullGoodMask N L Y mask) sigma)
        (largePrimeDependencyGraph N L Y)) ≤
      ((mask.card : ℝ) + 2 * (maskedSupportEdges L Y mask).card +
        (jointDefectMass N L (separatedPairs mask L) : ℝ)) / (2 : ℝ) ^ (2 * L) := by
  have hLY : L + 1 ≤ Y := by omega
  have hsplit (f g : SmallSample (dyadicCutoff N L) Y → ℝ) :
      finiteUniformAverage (fun sigma => f sigma + g sigma) = finiteUniformAverage f + finiteUniformAverage g := by
    unfold finiteUniformAverage
    rw [Finset.sum_add_distrib,add_div]
  rw [hsplit,average_bOne_fullGoodMask_eq mask hmask hN hL hLY]
  have hfirst := bOne_fullGoodMask_le mask hmask hN hL hLY 0
  rw [bOne_fullGoodMask_eq mask hmask hN hL hLY 0] at hfirst
  have hsecond := average_bTwo_fullGoodMask_le mask hmask hN hL hY
  have hh := add_le_add hfirst hsecond
  convert hh using 1 <;> first | rfl | ring

/-- The source's three-term numerator follows by one harmless universal factor. -/
theorem average_stein_terms_le_twice {N L Y : ℕ} (mask : Finset ℕ)
    (hmask : mask ⊆ dyadicBlock N) (hN : 2 ≤ N) (hL : 0 < L) (hY : 2 * L ≤ Y) :
    finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
      bOne (largeUniformPMF (dyadicCutoff N L) Y)
        (maskedConditionedGoodIndicator N L Y (fullGoodMask N L Y mask) sigma)
        (largePrimeDependencyGraph N L Y) +
      bTwo (largeUniformPMF (dyadicCutoff N L) Y)
        (maskedConditionedGoodIndicator N L Y (fullGoodMask N L Y mask) sigma)
        (largePrimeDependencyGraph N L Y)) ≤
      2 * (((mask.card : ℝ) + (maskedSupportEdges L Y mask).card +
        (jointDefectMass N L (separatedPairs mask L) : ℝ)) / (2 : ℝ) ^ (2 * L)) := by
  apply (average_stein_terms_le mask hmask hN hL hY).trans
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have ha : (0 : ℝ) ≤ mask.card := by positivity
  have hr : (0 : ℝ) ≤ jointDefectMass N L (separatedPairs mask L) := by positivity
  nlinarith

/-- Actual infinite probability deletion plus target deletion, with the mask preserved. -/
theorem infinite_deletion_cost_le {N L Y : ℕ} (mask : Finset ℕ)
    (hmask : mask ⊆ dyadicBlock N) (hN : 2 ≤ N) (hL : 0 < L) :
    (∑ x ∈ fullBadMask N L Y mask, InfiniteStartProbabilityTransfer.infiniteStartProbability x L) +
      (fullBadMask N L Y mask).card / (2 : ℝ) ^ L ≤
        ((fullDefectMass L mask : ℝ) + 2 * (fullBadMask N L Y mask).card) / (2 : ℝ) ^ L := by
  rw [infinite_bad_probability_sum_eq mask hmask]
  have h := (Rat.cast_le (K := ℝ)).mpr
    (masked_total_deletion_cost_le (Y := Y) hN hL mask hmask)
  simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat] using h

end
end PaperC.V282.MaskedArithmeticCosts
