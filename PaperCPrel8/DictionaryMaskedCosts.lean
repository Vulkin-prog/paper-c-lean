import PaperCV282.DictionaryFieldFirstCost
import PaperCV282.DictionaryFieldSecondCost

/-! # Local dictionary costs proportional to the actual deterministic mask -/
namespace PaperC.Prel8.DictionaryMaskedCosts
open PaperC PaperC.V282
open DictionaryFieldModel DictionaryFieldDependency DictionaryFieldTransfer
open ArratiaGoldsteinGordonInput ConditionalStartProbability ConditionalAGGInstantiation
open SectionThirteenFiniteBound SectionTwelveMoments LargePrimeDependencyGraph
open MaskedArithmeticGeometry MaskedPairGeometry AllStartFieldCosts DictionaryFieldFirstCost
open DictionaryFieldSecondCost WordOverlapSum
open DictionaryFieldDeletion PrescribedValues WindowValues InfiniteWordTransfer
open scoped BigOperators
noncomputable section

theorem card_closed_pairs_le {L Y : ℕ} (mask : Finset ℕ) :
    (closedDictionarySitePairs L Y mask).card ≤
      2 * mask.card * (L + 1) + (maskedSupportEdges L Y mask).card := by
  classical
  let candidates := mask ×ˢ Finset.range (L + 1)
  let forward := candidates.image (fun z : ℕ × ℕ => (z.1,z.1+z.2))
  let backward := candidates.image (fun z : ℕ × ℕ => (z.1+z.2,z.1))
  have hs : closedDictionarySitePairs L Y mask ⊆
      (forward ∪ backward) ∪ maskedSupportEdges L Y mask := by
    intro xy hxy
    obtain ⟨hx,hy,hd | ha⟩ := (mem_closedDictionarySitePairs L Y mask xy.1 xy.2).mp hxy
    · apply Finset.mem_union_left
      have hm : Nat.dist xy.1 xy.2 ∈ Finset.range (L + 1) := Finset.mem_range.mpr (by omega)
      rcases TouchingPairs.eq_add_or_eq_add_of_dist_eq (L := Nat.dist xy.1 xy.2) rfl with hf | hb
      · apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨(xy.1,Nat.dist xy.1 xy.2),
          Finset.mem_product.mpr ⟨hx,hm⟩,Prod.ext rfl hf.symm⟩
      · apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨(xy.2,Nat.dist xy.1 xy.2),
          Finset.mem_product.mpr ⟨hy,hm⟩,Prod.ext hb.symm rfl⟩
    · exact Finset.mem_union_right _ (mem_maskedSupportEdges.mpr ⟨hx,hy,ha⟩)
  have hf : forward.card ≤ mask.card * (L + 1) := by
    apply (Finset.card_image_le).trans
    simp [candidates]
  have hb : backward.card ≤ mask.card * (L + 1) := by
    apply (Finset.card_image_le).trans
    simp [candidates]
  have h := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  have hu := Finset.card_union_le forward backward
  nlinarith

theorem local_mass_le {N L Y : ℕ} (W : Finset (Fin (L + 1) → F₂))
    (hW : W.Nonempty) (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N)
    (hN : 2 ≤ N) (hY : 2 * (L + 1) ≤ Y)
    (sigma : SmallSample (dyadicCutoff N L) Y) :
    orderedLocalMass (dyadicCutoff N L) Y (L + 1) (fullGoodMask N L Y mask) W sigma ≤
      2 * (mask.card : ℝ) * (dictionaryRate L W : ℝ) * overlapWeight W := by
  have h := orderedLocalMass_le (fullGoodMask N L Y mask) W hW
    (fun x hx => two_le_of_mem_dyadicBlock hN (hmask (fullGoodMask_subset_mask N L Y mask hx)))
    (fun x hx => by
      have hb := Finset.mem_Ico.mp (hmask (fullGoodMask_subset_mask N L Y mask hx))
      unfold dyadicCutoff
      omega) hY
    (fun x hx i => not_defective_of_mem_fullGoodMask hmask hx
      (vertex_mem_startTreeSupport (by
        have hb := two_le_of_mem_dyadicBlock hN (hmask (fullGoodMask_subset_mask N L Y mask hx))
        omega) i)) sigma
  have hc : ((fullGoodMask N L Y mask).card : ℝ) ≤ (mask.card : ℝ) := by
    have hc' := Finset.card_le_card (fullGoodMask_subset_mask N L Y mask)
    exact_mod_cast hc'
  rw [dictionaryRate_coe]
  apply h.trans
  have ho := overlapWeight_nonneg W
  have hp : 0 ≤ (W.card : ℝ) / (2 : ℝ) ^ (L + 1) := by positivity
  calc
    _ = 2 * (((fullGoodMask N L Y mask).card : ℝ) * (((W.card : ℝ) / (2 : ℝ) ^ (L + 1)) * overlapWeight W)) := by ring
    _ ≤ 2 * ((mask.card : ℝ) * (((W.card : ℝ) / (2 : ℝ) ^ (L + 1)) * overlapWeight W)) := by
      gcongr
    _ = _ := by ring


end
end PaperC.Prel8.DictionaryMaskedCosts
