import PaperCV282.DictionaryFieldTransfer
import PaperCV282.AllStartFieldCosts
import PaperCV282.MaskedPairGeometry

/-!
# First graph cost of the retained dictionary field

The true labelled graph is summed over its word coordinates before its
site pairs are counted. Close sites include the diagonal; all remaining
neighbours pay the original mask's large-prime support-edge count.
-/

namespace PaperC.V282.DictionaryFieldFirstCost

open DictionaryFieldModel DictionaryFieldDependency DictionaryFieldTransfer
open ArratiaGoldsteinGordonInput ConditionalStartProbability ConditionalAGGInstantiation
open SectionThirteenFiniteBound SectionTwelveMoments LargePrimeDependencyGraph
open MaskedArithmeticGeometry MaskedPairGeometry AllStartFieldCosts
open scoped BigOperators

noncomputable section

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- Site pairs in the closed dictionary graph, including equal sites. -/
def closedDictionarySitePairs (L Y : ℕ) (mask : Finset ℕ) : Finset (ℕ × ℕ) :=
  (mask ×ˢ mask).filter (fun xy => Nat.dist xy.1 xy.2 ≤ L ∨ LargePrimeAdjacent L Y xy.1 xy.2)

theorem mem_closedDictionarySitePairs (L Y : ℕ) (mask : Finset ℕ) (x y : ℕ) :
    (x,y) ∈ closedDictionarySitePairs L Y mask ↔
      x ∈ mask ∧ y ∈ mask ∧ (Nat.dist x y ≤ L ∨ LargePrimeAdjacent L Y x y) := by
  simp [closedDictionarySitePairs,and_assoc]

/-- Summing a site-pair quantity preserves both dictionary multiplicities. -/
theorem sum_dictionaryIndex_pair_site (N L : ℕ) (W : Finset (Fin (L + 1) → F₂))
    (f : ℕ → ℕ → ℝ) :
    (∑ i : DictionaryIndex N L W, ∑ j : DictionaryIndex N L W, f i.1.val j.1.val) =
      (W.card : ℝ)^2 * ∑ x ∈ dyadicBlock N, ∑ y ∈ dyadicBlock N, f x y := by
  simp_rw [sum_dictionaryIndex_site N L W]
  rw [sum_dictionaryIndex_site N L W (fun x => (W.card : ℝ) * ∑ y ∈ dyadicBlock N, f x y)]
  rw [← Finset.mul_sum]
  ring

/-- Exact aggregation uses the true uniform marginals at every retained site. -/
theorem bOne_dictionary_eq {N L Y : ℕ} (W : Finset (Fin (L + 1) → F₂))
    (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N) (hN : 2 ≤ N) (hLY : L + 1 ≤ Y)
    (sigma : SmallSample (dyadicCutoff N L) Y) :
    bOne (largeUniformPMF (dyadicCutoff N L) Y)
      (maskedWordIndicator N L Y W (fullGoodMask N L Y mask) sigma) (dictionaryGraph N L Y W) =
      (dictionaryRate L W : ℝ)^2 *
        (closedDictionarySitePairs L Y (fullGoodMask N L Y mask)).card := by
  classical
  let g := fullGoodMask N L Y mask
  let p := (wordRate L : ℝ)
  have hg : g ⊆ dyadicBlock N := fun x hx => hmask (fullGoodMask_subset_mask N L Y mask hx)
  have hm (i : DictionaryIndex N L W) :
      marginal (largeUniformPMF (dyadicCutoff N L) Y)
        (maskedWordIndicator N L Y W g sigma) i = if i.1.val ∈ g then p else 0 := by
    rw [marginal_maskedWordIndicator]
    split_ifs with hi
    · exact marginal_conditionedWordIndicator_of_not_fullBad W hN hLY sigma i
        (mem_fullGoodMask.mp hi).2
    · rfl
  have hc (i : DictionaryIndex N L W) : closedNeighborhood (dictionaryGraph N L Y W) i =
      Finset.univ.filter (fun j => Nat.dist i.1.val j.1.val ≤ L ∨ LargePrimeAdjacent L Y i.1.val j.1.val) := by
    ext j
    rw [mem_closedNeighborhood_dictionaryGraph]
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro (he | h)
      · exact Or.inl (by simp [he])
      · exact h
    · exact Or.inr
  let f : ℕ → ℕ → ℝ := fun x y =>
    if x ∈ g ∧ y ∈ g ∧ (Nat.dist x y ≤ L ∨ LargePrimeAdjacent L Y x y) then p^2 else 0
  have hb : bOne (largeUniformPMF (dyadicCutoff N L) Y)
      (maskedWordIndicator N L Y W g sigma) (dictionaryGraph N L Y W) =
      ∑ i : DictionaryIndex N L W, ∑ j : DictionaryIndex N L W, f i.1.val j.1.val := by
    unfold bOne
    apply Finset.sum_congr rfl
    intro i hi
    rw [hc,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hm,hm]
    by_cases hix : i.1.val ∈ g <;> by_cases hjx : j.1.val ∈ g <;>
      by_cases ha : Nat.dist i.1.val j.1.val ≤ L ∨ LargePrimeAdjacent L Y i.1.val j.1.val <;>
      simp [f,hix,hjx,ha,pow_two]
  rw [hb,sum_dictionaryIndex_pair_site]
  have hs : (∑ x ∈ dyadicBlock N, ∑ y ∈ dyadicBlock N, f x y) =
      (closedDictionarySitePairs L Y g).card * p^2 := by
    rw [sum_pair_subset_of_zero hg f (by intro x hx hnot y; simp [f,hnot])
      (by intro y hy hnot x; simp [f,hnot])]
    rw [← Finset.sum_product' ]
    trans ∑ xy ∈ closedDictionarySitePairs L Y g, p^2
    · rw [closedDictionarySitePairs,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro xy hxy
      obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
      simp [f,hx,hy]
    · simp
  rw [hs]
  simp only [dictionaryRate_coe,wordRate_coe,p]
  ring

/-- Two oriented offset lists cover all near pairs, with the diagonal included. -/
theorem card_closedDictionarySitePairs_le {N L Y : ℕ} (mask : Finset ℕ)
    (hmask : mask ⊆ dyadicBlock N) :
    (closedDictionarySitePairs L Y mask).card ≤
      2 * N * (L + 1) + (maskedSupportEdges L Y mask).card := by
  classical
  let candidates := dyadicBlock N ×ˢ Finset.range (L + 1)
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
          Finset.mem_product.mpr ⟨hmask hx,hm⟩,Prod.ext rfl hf.symm⟩
      · apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨(xy.2,Nat.dist xy.1 xy.2),
          Finset.mem_product.mpr ⟨hmask hy,hm⟩,Prod.ext hb.symm rfl⟩
    · exact Finset.mem_union_right _ (mem_maskedSupportEdges.mpr ⟨hx,hy,ha⟩)
  have hf : forward.card ≤ N * (L + 1) := by
    apply (Finset.card_image_le).trans
    simp [candidates,TouchingPairs.card_dyadicBlock]
  have hb : backward.card ≤ N * (L + 1) := by
    apply (Finset.card_image_le).trans
    simp [candidates,TouchingPairs.card_dyadicBlock]
  have h := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  have hu := Finset.card_union_le forward backward
  nlinarith

/-- The first AGG cost on the actual retained labelled field, before averaging. -/
theorem bOne_dictionary_le {N L Y : ℕ} (W : Finset (Fin (L + 1) → F₂))
    (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N) (hN : 2 ≤ N) (hLY : L + 1 ≤ Y)
    (sigma : SmallSample (dyadicCutoff N L) Y) :
    bOne (largeUniformPMF (dyadicCutoff N L) Y)
      (maskedWordIndicator N L Y W (fullGoodMask N L Y mask) sigma) (dictionaryGraph N L Y W) ≤
      (dictionaryRate L W : ℝ)^2 *
        (2 * (N : ℝ) * (L + 1) + (maskedSupportEdges L Y mask).card) := by
  rw [bOne_dictionary_eq W mask hmask hN hLY sigma]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  have hs : closedDictionarySitePairs L Y (fullGoodMask N L Y mask) ⊆
      closedDictionarySitePairs L Y mask := by
    intro xy hxy
    obtain ⟨hx,hy,ha⟩ := (mem_closedDictionarySitePairs _ _ _ _ _).mp hxy
    exact (mem_closedDictionarySitePairs _ _ _ _ _).mpr
      ⟨fullGoodMask_subset_mask N L Y mask hx,fullGoodMask_subset_mask N L Y mask hy,ha⟩
  exact_mod_cast (Finset.card_le_card hs).trans (card_closedDictionarySitePairs_le mask hmask)

end
end PaperC.V282.DictionaryFieldFirstCost
