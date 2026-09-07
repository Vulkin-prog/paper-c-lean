import PaperCV282.MaskedPairGeometry
import PaperCV282.GoodTouchingProbability

/-!
# Exact mask-level pair costs for Theorem 4.1

The overlapping contribution vanishes, good touching probabilities equal
p squared, and only separated pairs pay their true relation defect. Both
the support-edge count and the relation mass retain the input mask.
-/

namespace PaperC.V282.MaskedPairBounds

open MaskedArithmeticGeometry MaskedPairGeometry GoodTouchingProbability
open LargePrimeDependencyGraph SectionTwelveMoments TwoWindowParity
open scoped BigOperators

noncomputable section

/-- A good distinct pair only pays a relation defect when it is separated. -/
theorem jointProbability_le_separated_weight {N L Y x y : ℕ} {mask : Finset ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hY : 2 * L ≤ Y) (hmask : mask ⊆ dyadicBlock N)
    (hx : x ∈ fullGoodMask N L Y mask) (hy : y ∈ fullGoodMask N L Y mask) (hxy : x ≠ y) :
    jointStartProbability N L x y ≤
      (1 + if L < Nat.dist x y then (jointDefectWeight N L (x,y) : ℚ) else 0) / (2 : ℚ) ^ (2 * L) := by
  by_cases hs : L < Nat.dist x y
  · rw [if_pos hs]
    have h := (le_abs_self _).trans (abs_jointStartProbability_sub_baseline_le N L x y hL)
    have heq : ((1 : ℚ) + jointDefectWeight N L (x,y)) / 2 ^ (2 * L) =
        1 / 2 ^ (2 * L) + (jointDefectWeight N L (x,y) : ℚ) / 2 ^ (2 * L) := by ring
    rw [heq]
    linarith
  · rw [if_neg hs]
    by_cases ho : Nat.dist x y < L
    · rw [jointStartProbability_eq_zero_of_overlap hxy ho]
      positivity
    · have hd : Nat.dist x y = L := by omega
      rw [jointStartProbability_eq_baseline_of_full_good_touching hN hL hY hmask hx hy hd]
      simp

/-- The retained separated edges are included in the literal separated mask. -/
theorem separated_fullMaskedEdges_subset (N L Y : ℕ) (mask : Finset ℕ) :
    (fullMaskedEdges N L Y mask).filter (fun p => L < Nat.dist p.1 p.2) ⊆ separatedPairs mask L := by
  intro p hp
  obtain ⟨he,hd⟩ := Finset.mem_filter.mp hp
  obtain ⟨hx,hy,_⟩ := mem_fullMaskedEdges.mp he
  exact (mem_separatedPairs _ _ _ _).mpr ⟨(mem_fullGoodMask.mp hx).1,(mem_fullGoodMask.mp hy).1,hd⟩

/-- Exact finite aggregation before replacing the separated edge submask by all separated mask pairs. -/
theorem jointPairMass_fullEdges_le_filtered {N L Y : ℕ} (mask : Finset ℕ)
    (hN : 2 ≤ N) (hL : 0 < L) (hY : 2 * L ≤ Y) (hmask : mask ⊆ dyadicBlock N) :
    jointPairMass N L (fullMaskedEdges N L Y mask) ≤
      ((fullMaskedEdges N L Y mask).card +
        (jointDefectMass N L ((fullMaskedEdges N L Y mask).filter
          (fun p => L < Nat.dist p.1 p.2)) : ℕ) : ℚ) / (2 : ℚ) ^ (2 * L) := by
  classical
  unfold jointPairMass
  calc
    _ ≤ ∑ p ∈ fullMaskedEdges N L Y mask,
      ((1 : ℚ) + if L < Nat.dist p.1 p.2 then (jointDefectWeight N L p : ℚ) else 0) / 2 ^ (2 * L) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hx,hy,ha⟩ := mem_fullMaskedEdges.mp hp
      exact jointProbability_le_separated_weight hN hL hY hmask hx hy ha.1
    _ = _ := by
      rw [← Finset.sum_div]
      congr 1
      rw [Finset.sum_add_distrib,← Finset.sum_filter]
      simp [jointDefectMass]

/-- The sharp averaged-pair cost on retained edges, with the original mask relation mass. -/
theorem jointPairMass_fullEdges_le {N L Y : ℕ} (mask : Finset ℕ)
    (hN : 2 ≤ N) (hL : 0 < L) (hY : 2 * L ≤ Y) (hmask : mask ⊆ dyadicBlock N) :
    jointPairMass N L (fullMaskedEdges N L Y mask) ≤
      ((fullMaskedEdges N L Y mask).card +
        (jointDefectMass N L (separatedPairs mask L) : ℕ) : ℚ) / (2 : ℚ) ^ (2 * L) := by
  apply (jointPairMass_fullEdges_le_filtered mask hN hL hY hmask).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hm : jointDefectMass N L ((fullMaskedEdges N L Y mask).filter
      (fun p => L < Nat.dist p.1 p.2)) ≤ jointDefectMass N L (separatedPairs mask L) := by
    unfold jointDefectMass
    exact Finset.sum_le_sum_of_subset (separated_fullMaskedEdges_subset N L Y mask)
  exact_mod_cast Nat.add_le_add_left hm (fullMaskedEdges N L Y mask).card

/-- The paper's E_Y(A)+R2(A) numerator, counting edges on all masked sites. -/
theorem jointPairMass_fullEdges_le_support {N L Y : ℕ} (mask : Finset ℕ)
    (hN : 2 ≤ N) (hL : 0 < L) (hY : 2 * L ≤ Y) (hmask : mask ⊆ dyadicBlock N) :
    jointPairMass N L (fullMaskedEdges N L Y mask) ≤
      ((maskedSupportEdges L Y mask).card +
        (jointDefectMass N L (separatedPairs mask L) : ℕ) : ℚ) / (2 : ℚ) ^ (2 * L) := by
  apply (jointPairMass_fullEdges_le mask hN hL hY hmask).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.add_le_add_right (card_fullMaskedEdges_le_support N L Y mask) _

/-- Closed retained pairs pay only the original mask cardinality and its actual support edges. -/
theorem card_closedPairs_le_mask_support (N L Y : ℕ) (mask : Finset ℕ) :
    (fullMaskedClosedPairs N L Y mask).card ≤ mask.card + (maskedSupportEdges L Y mask).card := by
  rw [card_fullMaskedClosedPairs]
  exact Nat.add_le_add (Finset.card_le_card (fullGoodMask_subset_mask N L Y mask))
    (card_fullMaskedEdges_le_support N L Y mask)

end
end PaperC.V282.MaskedPairBounds
