import PaperCV282.MaskedArithmeticGeometry
import PaperCV282.PointwiseStartBounds

/-!
# Exact masked deletion cost

The defect weight uses all B=L+1 vertices. The removed set uses the larger
cutoff Y on that same support. The actual probability and target-parameter
loss retain the chosen mask before any domination by the dyadic block.
-/

namespace PaperC.V282.MaskedBadMass

open Affine WindowValues PointwiseStartBounds MaskedArithmeticGeometry
open InfiniteStartProbabilityTransfer
open scoped BigOperators

noncomputable section

/-- Actual finite probability mass removed by the whole-support deletion rule. -/
def maskedBadStartMass (N L Y : ℕ) (mask : Finset ℕ) : ℚ :=
  ∑ x ∈ fullBadMask N L Y mask, startProbability N L x

theorem fullDefectMass_cast (L : ℕ) (mask : Finset ℕ) :
    (fullDefectMass L mask : ℚ) =
      ∑ x ∈ mask, ((2 : ℚ) ^ (defectIndices (L + 1) x (L + 1)).card - 1) := by
  classical
  unfold fullDefectMass
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Nat.cast_sub (one_le_pow₀ (by omega : 1 ≤ (2 : ℕ)))]
  norm_num

theorem fullDefectMass_mono {L : ℕ} {s t : Finset ℕ} (h : s ⊆ t) :
    fullDefectMass L s ≤ fullDefectMass L t := by
  unfold fullDefectMass
  exact Finset.sum_le_sum_of_subset h

theorem startProbability_le_fullDefect {N L x : ℕ} (hN : 2 ≤ N)
    (hL : 0 < L) (hx : x ∈ dyadicBlock N) :
    startProbability N L x ≤ (2 : ℚ) ^ (defectIndices (L + 1) x (L + 1)).card / (2 : ℚ) ^ L := by
  rw [startProbability_eq_uniformSolutionProbability N L x hL]
  have hx2 := two_le_of_mem_dyadicBlock hN hx
  have hcut : x + L ≤ dyadicCutoff N L := by
    have hxb := Finset.mem_Ico.mp hx
    unfold dyadicCutoff
    omega
  exact (corollary_two_five_upper_finite hx2 hcut (startRhs L)).trans
    (div_le_div_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) (Nat.sub_le _ _)) (by positivity))

/-- A finite arbitrary mask retains its own defect sum and its own cardinality. -/
theorem startProbabilityMass_le_mask_defects {N L : ℕ} (hN : 2 ≤ N)
    (hL : 0 < L) (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N) :
    (∑ x ∈ mask, startProbability N L x) ≤
      ((fullDefectMass L mask : ℚ) + mask.card) / (2 : ℚ) ^ L := by
  calc
    _ ≤ ∑ x ∈ mask, (2 : ℚ) ^ (defectIndices (L + 1) x (L + 1)).card / (2 : ℚ) ^ L :=
      Finset.sum_le_sum fun x hx => startProbability_le_fullDefect hN hL (hmask hx)
    _ = _ := by
      rw [← Finset.sum_div, fullDefectMass_cast]
      congr 1
      have h : (∑ x ∈ mask, ((2 : ℚ) ^ (defectIndices (L + 1) x (L + 1)).card - 1)) =
          (∑ x ∈ mask, (2 : ℚ) ^ (defectIndices (L + 1) x (L + 1)).card) - mask.card := by
        rw [Finset.sum_sub_distrib]
        simp
      linarith

/-- The sharp deletion estimate before enlarging either of the actual masked sets. -/
theorem maskedBadStartMass_le_mask_defects {N L Y : ℕ} (hN : 2 ≤ N)
    (hL : 0 < L) (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N) :
    maskedBadStartMass N L Y mask ≤
      ((fullDefectMass L (fullBadMask N L Y mask) : ℚ) +
        (fullBadMask N L Y mask).card) / (2 : ℚ) ^ L :=
  startProbabilityMass_le_mask_defects hN hL _
    (fun _ hx => hmask (fullBadMask_subset_mask N L Y mask hx))

/-- The manuscript deletion cost p*(M_B+card(A intersect D_Y)). -/
theorem maskedBadStartMass_le {N L Y : ℕ} (hN : 2 ≤ N)
    (hL : 0 < L) (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N) :
    maskedBadStartMass N L Y mask ≤
      ((fullDefectMass L mask : ℚ) + (fullBadMask N L Y mask).card) / (2 : ℚ) ^ L := by
  apply (maskedBadStartMass_le_mask_defects hN hL mask hmask).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hh : (fullDefectMass L (fullBadMask N L Y mask) : ℚ) ≤ (fullDefectMass L mask : ℚ) := by
    exact_mod_cast fullDefectMass_mono (L := L) (fullBadMask_subset_mask N L Y mask)
  simpa only [add_comm] using add_le_add_right hh ((fullBadMask N L Y mask).card : ℚ)

/-- Full-block presentation of the same true masked deletion cost. -/
theorem maskedBadStartMass_le_full_block {N L Y : ℕ} (hN : 2 ≤ N)
    (hL : 0 < L) (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N) :
    maskedBadStartMass N L Y mask ≤
      ((fullDefectMass L (dyadicBlock N) : ℚ) + (fullBadStarts N L Y).card) / (2 : ℚ) ^ L := by
  apply (maskedBadStartMass_le hN hL mask hmask).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact add_le_add (by exact_mod_cast fullDefectMass_mono (L := L) hmask)
    (by exact_mod_cast Finset.card_le_card (Finset.inter_subset_right : fullBadMask N L Y mask ⊆ fullBadStarts N L Y))

/-- This is the actual infinite removed probability sum, by exact cylinder invariance. -/
theorem infinite_bad_probability_sum_eq {N L Y : ℕ} (mask : Finset ℕ)
    (hmask : mask ⊆ dyadicBlock N) :
    (∑ x ∈ fullBadMask N L Y mask, infiniteStartProbability x L) =
      (maskedBadStartMass N L Y mask : ℝ) := by
  unfold maskedBadStartMass
  push_cast
  apply Finset.sum_congr rfl
  intro x hx
  exact infiniteStartProbability_eq_startProbability
    (hmask (fullBadMask_subset_mask N L Y mask hx))

/-- Exact own-mask intensity difference between all sites and retained sites. -/
theorem target_parameter_sub_good (N L Y : ℕ) (mask : Finset ℕ) :
    (mask.card : ℚ) / (2 : ℚ) ^ L -
      (fullGoodMask N L Y mask).card / (2 : ℚ) ^ L =
        (fullBadMask N L Y mask).card / (2 : ℚ) ^ L := by
  have h : (mask.card : ℚ) = (fullGoodMask N L Y mask).card + (fullBadMask N L Y mask).card := by
    exact_mod_cast (card_fullGood_add_card_fullBad N L Y mask).symm
  rw [h]
  ring

/-- Actual deletion and target deletion together cost p*(M_B+2*card(A intersect D_Y)). -/
theorem masked_total_deletion_cost_le {N L Y : ℕ} (hN : 2 ≤ N)
    (hL : 0 < L) (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N) :
    maskedBadStartMass N L Y mask + (fullBadMask N L Y mask).card / (2 : ℚ) ^ L ≤
      ((fullDefectMass L mask : ℚ) + 2 * (fullBadMask N L Y mask).card) / (2 : ℚ) ^ L := by
  have h := add_le_add_right (maskedBadStartMass_le (Y := Y) hN hL mask hmask)
    ((fullBadMask N L Y mask).card / (2 : ℚ) ^ L)
  convert h using 1 <;> ring

end
end PaperC.V282.MaskedBadMass
