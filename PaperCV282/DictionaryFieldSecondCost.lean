import PaperCV282.DictionaryFieldDeletion
import PaperCV282.DictionaryPairCosts
import PaperCV282.WordOverlapSum

/-!
# The actual second process cost for a dictionary field

Same-site distinct labels are disjoint. Local pairs retain their prescribed-word
compatibility weights; separated graph pairs use the full-value marginal cap.
-/
namespace PaperC.V282.DictionaryFieldSecondCost

open Affine ConditionalStartProbability ConditionalDependencyGraph ConditionalAGGInstantiation
open ConditionalAGGAverage ArratiaGoldsteinGordonInput SectionTwelveMoments SectionThirteenFiniteBound
open DictionaryFieldModel DictionaryFieldDependency DictionaryFieldTransfer DictionaryFieldDeletion
open DictionaryPairCosts DictionaryMarginalCap MaskedArithmeticGeometry MaskedPairGeometry
open LargePrimeDependencyGraph WordOverlapSum PrescribedValues WindowValues InfiniteWordTransfer
open CappedRelationMass TwoWindowParity
open scoped BigOperators NNReal

noncomputable section

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

set_option maxHeartbeats 1000000

/-- Unpacking the finite labelled carrier does not introduce multiplicities or missing words. -/
theorem sum_dictionaryIndex (N L : ℕ) (W : Finset (Fin (L + 1) → F₂))
    (f : ℕ → (Fin (L + 1) → F₂) → ℝ) :
    (∑ i : DictionaryIndex N L W, f i.1.val i.2.val) =
      ∑ x ∈ dyadicBlock N, ∑ b ∈ W, f x b := by
  change (∑ i : {x : ℕ // x ∈ dyadicBlock N} × {b : Fin (L + 1) → F₂ // b ∈ W}, _) = _
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.sum_subtype W (fun _ => Iff.rfl)]
  exact (Finset.sum_subtype (dyadicBlock N) (fun _ => Iff.rfl) (fun x => ∑ b ∈ W, f x b)).symm

/-- The ordered double sum retains both site and dictionary coordinates exactly. -/
theorem sum_dictionaryIndex_pair (N L : ℕ) (W : Finset (Fin (L + 1) → F₂))
    (f : ℕ → ℕ → (Fin (L + 1) → F₂) → (Fin (L + 1) → F₂) → ℝ) :
    (∑ i : DictionaryIndex N L W, ∑ j : DictionaryIndex N L W,
      f i.1.val j.1.val i.2.val j.2.val) =
      ∑ xy ∈ (dyadicBlock N) ×ˢ (dyadicBlock N), ∑ u ∈ W, ∑ v ∈ W, f xy.1 xy.2 u v := by
  have hinner (i : DictionaryIndex N L W) := sum_dictionaryIndex N L W (fun y v => f i.1.val y i.2.val v)
  simp_rw [hinner]
  rw [sum_dictionaryIndex N L W (fun x u => ∑ y ∈ dyadicBlock N, ∑ v ∈ W, f x y u v)]
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_comm]

/-- Site pairs left after the same-site disjointness cancellation. -/
def dictionaryNeighborPairs (N L Y : ℕ) (mask : Finset ℕ) : Finset (ℕ × ℕ) :=
  (fullGoodMask N L Y mask).offDiag.filter fun xy =>
    Nat.dist xy.1 xy.2 ≤ L ∨ LargePrimeAdjacent L Y xy.1 xy.2

theorem mem_dictionaryNeighborPairs {N L Y x y : ℕ} {mask : Finset ℕ} :
    (x,y) ∈ dictionaryNeighborPairs N L Y mask ↔
      x ∈ fullGoodMask N L Y mask ∧ y ∈ fullGoodMask N L Y mask ∧ x ≠ y ∧
        (Nat.dist x y ≤ L ∨ LargePrimeAdjacent L Y x y) := by
  simp [dictionaryNeighborPairs,Finset.mem_offDiag,and_assoc]

/-- Different dictionary labels at the same site have zero joint mass. -/
theorem jointMarginal_same_site_eq_zero {N L Y : ℕ} (W : Finset (Fin (L + 1) → F₂))
    (sigma : SmallSample (dyadicCutoff N L) Y) (i j : DictionaryIndex N L W)
    (hsite : i.1.val = j.1.val) (hij : i ≠ j) :
    jointMarginal (largeUniformPMF (dyadicCutoff N L) Y)
      (conditionedWordIndicator N L Y W sigma) i j = 0 := by
  have hwords : i.2.val ≠ j.2.val := by
    intro hw
    apply hij
    exact Prod.ext (Subtype.ext hsite) (Subtype.ext hw)
  unfold jointMarginal
  have hevent : (fun eta => conditionedWordIndicator N L Y W sigma i eta = true ∧
      conditionedWordIndicator N L Y W sigma j eta = true) = fun _ => False := by
    funext eta
    apply propext
    simp only [iff_false]
    rw [conditionedWordIndicator_eq_true_iff,conditionedWordIndicator_eq_true_iff,← hsite]
    simpa only [finiteWordIndicator_eq_true_iff] using
      finiteWordIndicator_same_site_disjoint hwords (assemble _ _ sigma eta)
  rw [hevent]
  simp [eventProbability]

/-- The second process cost is exactly the conditional mass on the surviving site pairs. -/
theorem bTwo_dictionary_eq_pairMass {N L Y : ℕ} (W : Finset (Fin (L + 1) → F₂))
    (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N)
    (sigma : SmallSample (dyadicCutoff N L) Y) :
    bTwo (largeUniformPMF (dyadicCutoff N L) Y)
      (maskedWordIndicator N L Y W (fullGoodMask N L Y mask) sigma) (dictionaryGraph N L Y W) =
      conditionalDictionaryPairMass N L Y W (dictionaryNeighborPairs N L Y mask) sigma := by
  have hterm (i j : DictionaryIndex N L W) :
      (if j ∈ (closedNeighborhood (dictionaryGraph N L Y W) i).erase i then
        jointMarginal (largeUniformPMF (dyadicCutoff N L) Y)
          (maskedWordIndicator N L Y W (fullGoodMask N L Y mask) sigma) i j else 0) =
      if (i.1.val,j.1.val) ∈ dictionaryNeighborPairs N L Y mask then
        jointMarginal (largeUniformPMF (dyadicCutoff N L) Y)
          (conditionedWordIndicator N L Y W sigma) i j else 0 := by
    by_cases hi : i.1.val ∈ fullGoodMask N L Y mask
    · by_cases hj : j.1.val ∈ fullGoodMask N L Y mask
      · have hjoint : jointMarginal (largeUniformPMF (dyadicCutoff N L) Y)
            (maskedWordIndicator N L Y W (fullGoodMask N L Y mask) sigma) i j =
            jointMarginal (largeUniformPMF (dyadicCutoff N L) Y) (conditionedWordIndicator N L Y W sigma) i j := by
          simp only [jointMarginal,maskedWordIndicator,if_pos hi,if_pos hj]
        rw [hjoint]
        by_cases hs : i.1.val = j.1.val
        · by_cases heq : i = j
          · subst j
            simp [mem_dictionaryNeighborPairs]
          · rw [jointMarginal_same_site_eq_zero W sigma i j hs heq]
            simp
        · have hsite : i.1 ≠ j.1 := fun h => hs (congrArg Subtype.val h)
          have hne : j ≠ i := fun h => hs (congrArg (fun z : DictionaryIndex N L W => z.1.val) h.symm)
          simp [Finset.mem_erase,dictionaryGraph,
            mem_dictionaryNeighborPairs,hi,hj,hs,hne,Ne.symm hne,hsite]
      · simp [jointMarginal,maskedWordIndicator,hj,mem_dictionaryNeighborPairs,eventProbability]
    · simp [jointMarginal,maskedWordIndicator,hi,mem_dictionaryNeighborPairs,eventProbability]
  unfold bTwo
  have hsum (i : DictionaryIndex N L W) :
      (∑ j ∈ (closedNeighborhood (dictionaryGraph N L Y W) i).erase i,
        jointMarginal (largeUniformPMF (dyadicCutoff N L) Y)
          (maskedWordIndicator N L Y W (fullGoodMask N L Y mask) sigma) i j) =
      ∑ j : DictionaryIndex N L W, if (i.1.val,j.1.val) ∈ dictionaryNeighborPairs N L Y mask then
        jointMarginal (largeUniformPMF (dyadicCutoff N L) Y)
          (conditionedWordIndicator N L Y W sigma) i j else 0 := by
    have hf : Finset.univ.filter (fun j => j ∈ (closedNeighborhood (dictionaryGraph N L Y W) i).erase i) =
        (closedNeighborhood (dictionaryGraph N L Y W) i).erase i := by ext j; simp
    rw [← hf,Finset.sum_filter]
    exact Finset.sum_congr rfl (fun j _ => hterm i j)
  simp_rw [hsum]
  simp only [jointMarginal,conditionedWordIndicator_eq_true_iff]
  rw [sum_dictionaryIndex_pair N L W (fun x y u v => if (x,y) ∈ dictionaryNeighborPairs N L Y mask then
    eventProbability (largeUniformPMF (dyadicCutoff N L) Y) (fun eta =>
      assemble _ _ sigma eta ∈ finiteWordEvent (dyadicCutoff N L) x (L+1) u ∧
      assemble _ _ sigma eta ∈ finiteWordEvent (dyadicCutoff N L) y (L+1) v) else 0)]
  rw [conditionalDictionaryPairMass_eq_labelled_sum]
  simp_rw [Finset.sum_ite_irrel,Finset.sum_const_zero]
  rw [← Finset.sum_filter]
  congr 1
  ext xy
  simp only [Finset.mem_filter]
  constructor
  · exact And.right
  · intro h
    obtain ⟨hx,hy,_,_⟩ := mem_dictionaryNeighborPairs.mp h
    exact ⟨Finset.mem_product.mpr ⟨hmask (fullGoodMask_subset_mask N L Y mask hx),
      hmask (fullGoodMask_subset_mask N L Y mask hy)⟩,h⟩

/-- The local and separated pieces are a genuine disjoint partition of retained graph pairs. -/
theorem dictionary_pairMass_eq_local_add_separated (N L Y : ℕ)
    (W : Finset (Fin (L + 1) → F₂)) (mask : Finset ℕ)
    (sigma : SmallSample (dyadicCutoff N L) Y) :
    conditionalDictionaryPairMass N L Y W (dictionaryNeighborPairs N L Y mask) sigma =
      orderedLocalMass (dyadicCutoff N L) Y (L + 1) (fullGoodMask N L Y mask) W sigma +
      conditionalDictionaryPairMass N L Y W
        ((fullMaskedEdges N L Y mask).filter (fun xy => L < Nat.dist xy.1 xy.2)) sigma := by
  let localPairs := ((fullGoodMask N L Y mask) ×ˢ (fullGoodMask N L Y mask)).filter
    (fun xy => xy.1 ≠ xy.2 ∧ Nat.dist xy.1 xy.2 < L + 1)
  let farPairs := (fullMaskedEdges N L Y mask).filter (fun xy => L < Nat.dist xy.1 xy.2)
  have hunion : dictionaryNeighborPairs N L Y mask = localPairs ∪ farPairs := by
    ext ⟨x,y⟩
    simp only [mem_dictionaryNeighborPairs,Finset.mem_union,localPairs,farPairs,
      Finset.mem_filter,Finset.mem_product,mem_fullMaskedEdges]
    constructor
    · rintro ⟨hx,hy,hne,hd|hp⟩
      · exact Or.inl ⟨⟨hx,hy⟩,hne,by omega⟩
      · by_cases hd : Nat.dist x y ≤ L
        · exact Or.inl ⟨⟨hx,hy⟩,hne,by omega⟩
        · exact Or.inr ⟨⟨hx,hy,hp⟩,by omega⟩
    · rintro (⟨⟨hx,hy⟩,hne,hd⟩ | ⟨⟨hx,hy,hp⟩,hd⟩)
      · exact ⟨hx,hy,hne,Or.inl (by omega)⟩
      · exact ⟨hx,hy,hp.1,Or.inr hp⟩
  have hdis : Disjoint localPairs farPairs := by
    apply Finset.disjoint_left.mpr
    intro xy hl hf
    have hl' := (Finset.mem_filter.mp hl).2.2
    have hf' := (Finset.mem_filter.mp hf).2
    omega
  have hlocal : conditionalDictionaryPairMass N L Y W localPairs sigma =
      orderedLocalMass (dyadicCutoff N L) Y (L + 1) (fullGoodMask N L Y mask) W sigma := by
    rw [conditionalDictionaryPairMass_eq_labelled_sum]
    unfold localPairs orderedLocalMass
    rw [Finset.sum_filter,Finset.sum_product]
  rw [hunion]
  have hsum : conditionalDictionaryPairMass N L Y W (localPairs ∪ farPairs) sigma =
      conditionalDictionaryPairMass N L Y W localPairs sigma +
      conditionalDictionaryPairMass N L Y W farPairs sigma := by
    exact Finset.sum_union hdis
  rw [hsum,hlocal]

/-- Literal local compatibility mass on retained sites, with the ambient dictionary intensity. -/
theorem orderedLocalMass_good_le {N L Y : ℕ} (W : Finset (Fin (L + 1) → F₂))
    (hW : W.Nonempty) (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N)
    (hN : 2 ≤ N) (hY : 2 * (L + 1) ≤ Y)
    (sigma : SmallSample (dyadicCutoff N L) Y) :
    orderedLocalMass (dyadicCutoff N L) Y (L + 1) (fullGoodMask N L Y mask) W sigma ≤
      2 * (N : ℝ) * (dictionaryRate L W : ℝ) * overlapWeight W := by
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
  have hc : ((fullGoodMask N L Y mask).card : ℝ) ≤ (N : ℝ) := by
    have hc' := Finset.card_le_card (fun x hx => hmask (fullGoodMask_subset_mask N L Y mask hx))
    rw [TouchingPairs.card_dyadicBlock] at hc'
    exact_mod_cast hc'
  rw [dictionaryRate_coe]
  apply h.trans
  have ho := overlapWeight_nonneg W
  have hp : 0 ≤ (W.card : ℝ) / (2 : ℝ) ^ (L + 1) := by positivity
  calc
    _ = 2 * (((fullGoodMask N L Y mask).card : ℝ) * (((W.card : ℝ) / (2 : ℝ) ^ (L + 1)) * overlapWeight W)) := by ring
    _ ≤ 2 * ((N : ℝ) * (((W.card : ℝ) / (2 : ℝ) ^ (L + 1)) * overlapWeight W)) := by
      gcongr
    _ = _ := by ring

/-- The averaged actual second cost has exactly the local and capped separated budgets. -/
theorem average_bTwo_dictionary_le {N L Y : ℕ} (W : Finset (Fin (L + 1) → F₂))
    (hW : W.Nonempty) (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N)
    (hN : 2 ≤ N) (hY : 2 * (L + 1) ≤ Y) :
    finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
      bTwo (largeUniformPMF (dyadicCutoff N L) Y)
        (maskedWordIndicator N L Y W (fullGoodMask N L Y mask) sigma) (dictionaryGraph N L Y W)) ≤
      2 * (N : ℝ) * (dictionaryRate L W : ℝ) * overlapWeight W +
      (dictionaryRate L W : ℝ) ^ 2 *
        (((maskedSupportEdges L Y mask).card : ℝ) +
          cappedValueMass (dyadicCutoff N L) L (1 / (dictionaryRate L W : ℝ)) (separatedPairs mask L)) := by
  simp_rw [bTwo_dictionary_eq_pairMass W mask hmask,dictionary_pairMass_eq_local_add_separated]
  have hav {ι : Type} [Fintype ι] (f g : ι → ℝ) :
      finiteUniformAverage (fun i => f i + g i) = finiteUniformAverage f + finiteUniformAverage g := by
    unfold finiteUniformAverage
    rw [Finset.sum_add_distrib,add_div]
  rw [hav (orderedLocalMass (dyadicCutoff N L) Y (L+1) (fullGoodMask N L Y mask) W)
    (conditionalDictionaryPairMass N L Y W
      ((fullMaskedEdges N L Y mask).filter (fun xy => L < Nat.dist xy.1 xy.2))),average_dictionaryPairMass_eq]
  apply add_le_add
  · have h := finiteUniformAverage_mono (fun sigma => orderedLocalMass_good_le W hW mask hmask hN hY sigma)
    simpa [finiteUniformAverage] using h
  · exact separated_fullMaskedEdges_dictionary_cost_le W mask hmask hN (by omega)

end
end PaperC.V282.DictionaryFieldSecondCost
