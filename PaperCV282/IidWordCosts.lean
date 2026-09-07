import PaperCV282.IidWordDependency
import PaperCV282.DictionaryFieldFirstCost
import PaperCV282.DictionaryFieldSecondCost

/-! # Actual local process costs of the iid word field -/
namespace PaperC.V282.IidWordCosts

open IidWordField IidWordDependency DictionaryFieldModel DictionaryFieldTransfer
open DictionaryFieldFirstCost DictionaryFieldSecondCost WordOverlap WordOverlapSum
open ArratiaGoldsteinGordonInput SectionTwelveMoments ConditionalDependencyGraph
open FiniteFieldTotalVariation FiniteFieldPoissonCoupling ProcessAGGInput
open scoped BigOperators NNReal

noncomputable section

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- Actual local joint mass on a deterministic position mask in the iid prefix. -/
def iidOrderedLocalMass (C B : ℕ) (s : Finset ℕ) (W : Finset (Fin B → F₂)) : ℝ :=
  ∑ x ∈ s, ∑ y ∈ s, if x ≠ y ∧ Nat.dist x y < B then
    ∑ u ∈ W, ∑ v ∈ W, eventProbability (iidUniformPMF C) (fun omega =>
      Occurs (iidSequence C omega) x u ∧ Occurs (iidSequence C omega) y v) else 0

theorem iid_local_dictionary_probability {C x B d : ℕ} (hx : 1 ≤ x) (hd : d ≤ B)
    (hcut : x-1+(B+d) ≤ C) (W : Finset (Fin B → F₂)) :
    (∑ u ∈ W, ∑ v ∈ W, eventProbability (iidUniformPMF C) (fun omega =>
      Occurs (iidSequence C omega) x u ∧ Occurs (iidSequence C omega) (x+d) v)) =
      (1 / (2 : ℝ)^B) * ∑ u ∈ W, ∑ v ∈ W, directedOverlapWeight d u v := by
  simp_rw [iid_word_joint_probability hx hd hcut]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  unfold directedOverlapWeight
  split_ifs <;> simp [pow_add,div_eq_mul_inv,mul_comm]

/-- No arithmetic deletion is needed: the exact local overlap formula holds at every site. -/
theorem iidOrderedLocalMass_le {C B : ℕ} (s : Finset ℕ) (W : Finset (Fin B → F₂))
    (hW : W.Nonempty) (hs : ∀ x ∈ s, 1 ≤ x) (hcut : ∀ x ∈ s, x-1+B ≤ C) :
    iidOrderedLocalMass C B s W ≤ 2 * ((s.card : ℝ) * (W.card : ℝ) / (2 : ℝ)^B) * overlapWeight W := by
  let K : ℕ → ℕ → ℝ := fun x y => ∑ u ∈ W, ∑ v ∈ W,
    eventProbability (iidUniformPMF C) (fun omega =>
      Occurs (iidSequence C omega) x u ∧ Occurs (iidSequence C omega) y v)
  have hsymm : ∀ x y, K x y = K y x := by
    intro x y
    dsimp [K]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v hv
    apply Finset.sum_congr rfl
    intro u hu
    congr 1
    funext omega
    exact propext and_comm
  change (∑ x ∈ s, ∑ y ∈ s, if x ≠ y ∧ Nat.dist x y < B then K x y else 0) ≤ _
  rw [sum_ordered_local_eq_two_forward s B K hsymm]
  have hforward : (∑ x ∈ s, ∑ d ∈ Finset.Icc 1 (B-1), if x+d ∈ s then K x (x+d) else 0) ≤
      ∑ x ∈ s, ∑ d ∈ Finset.Icc 1 (B-1),
        (1 / (2 : ℝ)^B) * ∑ u ∈ W, ∑ v ∈ W, directedOverlapWeight d u v := by
    apply Finset.sum_le_sum
    intro x hx
    apply Finset.sum_le_sum
    intro d hdIcc
    obtain ⟨hdpos,hdtop⟩ := Finset.mem_Icc.mp hdIcc
    by_cases hxd : x+d ∈ s
    · simp only [if_pos hxd]
      have hxpos := hs x hx
      have hycut := hcut (x+d) hxd
      exact le_of_eq (iid_local_dictionary_probability hxpos (by omega) (by omega) W)
    · simp only [if_neg hxd]
      apply mul_nonneg (by positivity)
      exact Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => directedOverlapWeight_nonneg d u v
  apply (mul_le_mul_of_nonneg_left hforward (by norm_num : (0 : ℝ) ≤ 2)).trans_eq
  simp_rw [summed_overlap_normalization W hW]
  rw [Finset.sum_const,nsmul_eq_mul]
  ring

/-- Near site pairs, including the diagonal, are covered by two oriented offset lists. -/
theorem card_iid_near_pairs_le (N L : ℕ) :
    (((dyadicBlock N) ×ˢ (dyadicBlock N)).filter (fun xy => Nat.dist xy.1 xy.2 ≤ L)).card ≤
      2 * N * (L+1) := by
  let candidates := dyadicBlock N ×ˢ Finset.range (L+1)
  let forward := candidates.image (fun z : ℕ × ℕ => (z.1,z.1+z.2))
  let backward := candidates.image (fun z : ℕ × ℕ => (z.1+z.2,z.1))
  have hs : ((dyadicBlock N) ×ˢ (dyadicBlock N)).filter (fun xy => Nat.dist xy.1 xy.2 ≤ L) ⊆
      forward ∪ backward := by
    intro xy hxy
    obtain ⟨hmem,hd⟩ := Finset.mem_filter.mp hxy
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hmem
    have hm : Nat.dist xy.1 xy.2 ∈ Finset.range (L+1) := Finset.mem_range.mpr (by omega)
    rcases TouchingPairs.eq_add_or_eq_add_of_dist_eq (L := Nat.dist xy.1 xy.2) rfl with hf | hb
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(xy.1,Nat.dist xy.1 xy.2),
        Finset.mem_product.mpr ⟨hx,hm⟩,Prod.ext rfl hf.symm⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(xy.2,Nat.dist xy.1 xy.2),
        Finset.mem_product.mpr ⟨hy,hm⟩,Prod.ext hb.symm rfl⟩)
  have hf : forward.card ≤ N * (L+1) := by
    apply Finset.card_image_le.trans
    simp [candidates,TouchingPairs.card_dyadicBlock]
  have hb : backward.card ≤ N * (L+1) := by
    apply Finset.card_image_le.trans
    simp [candidates,TouchingPairs.card_dyadicBlock]
  have h := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  nlinarith

/-- The first iid process cost includes all same-site word labels and all local site pairs. -/
theorem bOne_iid_le (N L : ℕ) (W : Finset (Fin (L+1) → F₂)) :
    bOne (iidUniformPMF (dyadicCutoff N L + 1)) (iidFieldIndicator N L W) (iidWordGraph N L W) ≤
      2 * (N : ℝ) * (L+1 : ℝ) * (dictionaryRate L W : ℝ)^2 := by
  have hc (i : DictionaryIndex N L W) : closedNeighborhood (iidWordGraph N L W) i =
      Finset.univ.filter (fun j => Nat.dist i.1.val j.1.val ≤ L) := by
    ext j
    simp only [mem_closedNeighborhood_iidWordGraph,Finset.mem_filter,Finset.mem_univ,true_and]
  unfold bOne
  simp_rw [hc,Finset.sum_filter,iidField_marginal]
  rw [sum_dictionaryIndex_pair_site N L W (fun x y =>
    if Nat.dist x y ≤ L then (wordRate L : ℝ)*(wordRate L : ℝ) else 0)]
  rw [← Finset.sum_product',← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul]
  have hcard : (((((dyadicBlock N) ×ˢ (dyadicBlock N)).filter
      (fun xy => Nat.dist xy.1 xy.2 ≤ L)).card) : ℝ) ≤ 2 * (N : ℝ) * (L+1 : ℝ) := by
    exact_mod_cast card_iid_near_pairs_le N L
  have h := mul_le_mul_of_nonneg_right hcard (sq_nonneg (dictionaryRate L W : ℝ))
  simp only [dictionaryRate_coe,wordRate_coe] at *
  convert h using 1 <;> try ring
  rfl

/-- Distinct words at one site have zero iid joint probability. -/
theorem iid_joint_same_site_zero {N L : ℕ} (W : Finset (Fin (L+1) → F₂))
    (i j : DictionaryIndex N L W) (hs : i.1.val = j.1.val) (hne : i ≠ j) :
    jointMarginal (iidUniformPMF (dyadicCutoff N L + 1)) (iidFieldIndicator N L W) i j = 0 := by
  have hw : i.2.val ≠ j.2.val := by
    intro he
    exact hne (Prod.ext (Subtype.ext hs) (Subtype.ext he))
  unfold jointMarginal iidFieldIndicator
  simp only [iidWordIndicator_eq_true,← hs]
  have hfalse (omega : IidSample (dyadicCutoff N L + 1)) :=
    not_occurs_pair_same_site (x := i.1.val) (iidSequence _ omega) i.2.val j.2.val hw
  simp [eventProbability,hfalse]

/-- The second iid process cost is exactly the ordered local mass; no label was grouped in the law. -/
theorem bTwo_iid_eq_local (N L : ℕ) (W : Finset (Fin (L+1) → F₂)) :
    bTwo (iidUniformPMF (dyadicCutoff N L + 1)) (iidFieldIndicator N L W) (iidWordGraph N L W) =
      iidOrderedLocalMass (dyadicCutoff N L + 1) (L+1) (dyadicBlock N) W := by
  have hterm (i j : DictionaryIndex N L W) :
      (if j ∈ (closedNeighborhood (iidWordGraph N L W) i).erase i then
        jointMarginal (iidUniformPMF (dyadicCutoff N L + 1)) (iidFieldIndicator N L W) i j else 0) =
      if i.1.val ≠ j.1.val ∧ Nat.dist i.1.val j.1.val < L+1 then
        jointMarginal (iidUniformPMF (dyadicCutoff N L + 1)) (iidFieldIndicator N L W) i j else 0 := by
    by_cases hs : i.1.val = j.1.val
    · by_cases he : i = j
      · subst j
        simp
      · rw [iid_joint_same_site_zero W i j hs he]
        simp
    · have hne : j ≠ i := fun he => hs (congrArg (fun z : DictionaryIndex N L W => z.1.val) he.symm)
      have hne' := Ne.symm hne
      simp [Finset.mem_erase,iidWordGraph,hs,hne,hne']
  unfold bTwo
  have hsum (i : DictionaryIndex N L W) :
      (∑ j ∈ (closedNeighborhood (iidWordGraph N L W) i).erase i,
        jointMarginal (iidUniformPMF (dyadicCutoff N L + 1)) (iidFieldIndicator N L W) i j) =
      ∑ j : DictionaryIndex N L W, if i.1.val ≠ j.1.val ∧ Nat.dist i.1.val j.1.val < L+1 then
        jointMarginal (iidUniformPMF (dyadicCutoff N L + 1)) (iidFieldIndicator N L W) i j else 0 := by
    have hf : Finset.univ.filter (fun j => j ∈ (closedNeighborhood (iidWordGraph N L W) i).erase i) =
        (closedNeighborhood (iidWordGraph N L W) i).erase i := by ext j; simp
    rw [← hf,Finset.sum_filter]
    exact Finset.sum_congr rfl (fun j _ => hterm i j)
  simp_rw [hsum]
  simp only [jointMarginal,iidFieldIndicator,iidWordIndicator_eq_true]
  rw [sum_dictionaryIndex_pair N L W (fun x y u v =>
    if x ≠ y ∧ Nat.dist x y < L+1 then eventProbability (iidUniformPMF (dyadicCutoff N L + 1))
      (fun omega => Occurs (iidSequence _ omega) x u ∧ Occurs (iidSequence _ omega) y v) else 0)]
  simp_rw [Finset.sum_ite_irrel,Finset.sum_const_zero]
  rw [Finset.sum_product]
  rfl

/-- The actual second cost is bounded by twice the dictionary intensity times Omega. -/
theorem bTwo_iid_le {N L : ℕ} (W : Finset (Fin (L+1) → F₂)) (hW : W.Nonempty) (hN : 1 ≤ N) :
    bTwo (iidUniformPMF (dyadicCutoff N L + 1)) (iidFieldIndicator N L W) (iidWordGraph N L W) ≤
      2 * ((N : ℝ) * (dictionaryRate L W : ℝ)) * overlapWeight W := by
  rw [bTwo_iid_eq_local]
  have h := iidOrderedLocalMass_le (dyadicBlock N) W hW
    (fun x hx => hN.trans (Finset.mem_Ico.mp hx).1)
    (fun x hx => DictionaryFieldInfinite.dictionary_vertex_cutoff N L ⟨x,hx⟩)
  simpa only [TouchingPairs.card_dyadicBlock,dictionaryRate_coe,mul_div_assoc] using h

end
end PaperC.V282.IidWordCosts
