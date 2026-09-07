import PaperCV282.BulkMarkedDependency

/-! # First signed bulk cost after summing geometric rates -/
namespace PaperC.V282.BulkMarkedFirstCost

open ExactMarkedModel ExactMarkedDependency BulkMarkedDependency BulkSupportGraph BulkProcessCosts
open MacroscopicMaskGeometry MaskedPairGeometry ArratiaGoldsteinGordonInput
open DictionaryFieldFirstCost
open ConditionalStartProbability ConditionalAGGInstantiation ConditionalAGGAverage SectionThirteenFiniteBound
open scoped BigOperators

noncomputable section

/-- Two oriented offset lists cover all near pairs, with the diagonal included. -/
theorem card_closedDictionarySitePairs_le {L Y : ℕ} {sites : Finset ℕ} (mask : Finset ℕ)
    (hmask : mask ⊆ sites) :
    (closedDictionarySitePairs L Y mask).card ≤
      2 * sites.card * (L + 1) + (maskedSupportEdges L Y mask).card := by
  classical
  let candidates := sites ×ˢ Finset.range (L + 1)
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
  have hf : forward.card ≤ sites.card * (L + 1) := by
    apply (Finset.card_image_le).trans
    simp [candidates]
  have hb : backward.card ≤ sites.card * (L + 1) := by
    apply (Finset.card_image_le).trans
    simp [candidates]
  have h := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  have hu := Finset.card_union_le forward backward
  nlinarith

/-- No polynomial factor in the number of labels enters the maximal-support first cost. -/
theorem bOne_labelled_bulk_le {κ S : Type*} [Fintype κ] [DecidableEq κ] [Fintype S]
    (μ : FinitePMF S) (X : ℕ → κ → S → Bool) (sites : Finset ℕ) (Q Y : ℕ)
    (mask : Finset ℕ) (hmask : mask ⊆ sites) (rate : κ → ℝ) {p : ℝ}
    (hr : ∀ a, 0 ≤ rate a) (hs : (∑ a, rate a) ≤ p)
    (hm : ∀ i : LabelledIndex sites κ,
      marginal μ (maskedLabelledFamily sites X mask) i = if i.1.val ∈ mask then rate i.2 else 0) :
    bOne μ (maskedLabelledFamily sites X mask) (labelledGraph sites Q Y κ) ≤
      p^2 * (2 * (sites.card : ℝ) * (Q+1) + (maskedSupportEdges Q Y mask).card) := by
  rw [bOne_labelled_eq μ X sites Q Y mask hmask rate hm]
  have hr0 : 0 ≤ ∑ a, rate a := Finset.sum_nonneg fun a _ => hr a
  have hp : 0 ≤ p := hr0.trans hs
  have hc : ((closedDictionarySitePairs Q Y mask).card : ℝ) ≤
      2 * (sites.card : ℝ) * (Q+1) + (maskedSupportEdges Q Y mask).card := by
    exact_mod_cast card_closedDictionarySitePairs_le mask hmask
  exact mul_le_mul (by nlinarith) hc (by positivity) (sq_nonneg _)

/-- Uniform conditional b1 bound for all retained excess/sign labels. -/
theorem bOne_signed_le {C L E Y : ℕ} {sites : Finset ℕ}
    (hsite : ∀ x ∈ sites, 2 ≤ x) (hL : 1 ≤ L) (hC : ∀ x ∈ sites, x+L+E+1 ≤ C)
    (hY : L+E+2 ≤ Y) (mask : Finset ℕ) (hmask : mask ⊆ sites) (sigma : SmallSample C Y) :
    bOne (largeUniformPMF C Y)
      (maskedLabelledFamily sites (conditionedSignedAt C L E Y sigma) (goodMask (L+E+1) Y mask))
      (labelledGraph sites (L+E+1) Y (Fin (E+1) × F₂)) ≤
      (1/(2 : ℝ)^L)^2 * (2*(sites.card : ℝ)*(L+E+2) + (maskedSupportEdges (L+E+1) Y mask).card) := by
  have hg : goodMask (L+E+1) Y mask ⊆ sites :=
    fun x hx => hmask (goodMask_subset (L+E+1) Y mask hx)
  have h := bOne_labelled_bulk_le (largeUniformPMF C Y) (conditionedSignedAt C L E Y sigma)
    sites (L+E+1) Y (goodMask (L+E+1) Y mask) hg
    (fun a : Fin (E+1) × F₂ => (signedMarkRate L a.1.val : ℝ))
    (fun a => (signedMarkRate L a.1.val).coe_nonneg)
    (by simpa only [Fintype.sum_prod_type] using sum_all_signedMarkRate_le_base L E)
    (signedAt_marginal_masked_good hsite hL hC hY mask sigma)
  have hc : ((maskedSupportEdges (L+E+1) Y (goodMask (L+E+1) Y mask)).card : ℝ) ≤
      (maskedSupportEdges (L+E+1) Y mask).card := by
    exact_mod_cast Finset.card_le_card (maskedSupportEdges_mono (goodMask_subset (L+E+1) Y mask))
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  push_cast
  linarith

/-- Averaging the first cost has the same bound, uniform in the full small-prime assignment. -/
theorem average_bOne_signed_le {C L E Y : ℕ} {sites : Finset ℕ}
    (hsite : ∀ x ∈ sites, 2 ≤ x) (hL : 1 ≤ L) (hC : ∀ x ∈ sites, x+L+E+1 ≤ C)
    (hY : L+E+2 ≤ Y) (mask : Finset ℕ) (hmask : mask ⊆ sites) :
    finiteUniformAverage (fun sigma : SmallSample C Y => bOne (largeUniformPMF C Y)
      (maskedLabelledFamily sites (conditionedSignedAt C L E Y sigma) (goodMask (L+E+1) Y mask))
      (labelledGraph sites (L+E+1) Y (Fin (E+1) × F₂))) ≤
      (1/(2 : ℝ)^L)^2 * (2*(sites.card : ℝ)*(L+E+2) + (maskedSupportEdges (L+E+1) Y mask).card) := by
  have h := finiteUniformAverage_mono (fun sigma => bOne_signed_le hsite hL hC hY mask hmask sigma)
  have hc : (Fintype.card (SmallSample C Y) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simpa only [finiteUniformAverage,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_div_cancel_left₀ _ hc] using h

end
end PaperC.V282.BulkMarkedFirstCost
