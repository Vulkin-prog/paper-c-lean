import PaperCV282.ExactMarkedAggregation
import PaperCV282.BulkMarkedDependency
import PaperCV282.DictionaryFieldTransfer

/-!
# Retention and process comparison of the entire signed exact-mark field

The same full site/mark/sign carrier is used for the source and both targets.
Only the explicit process AGG input is required. Rates vary with the excess.
-/
namespace PaperC.V282.BulkMarkedTransfer

open ExactMarkedModel ExactMarkedDependency ExactMarkedAggregation BulkSupportGraph BulkProcessCosts
open BulkMarkedDependency MacroscopicMaskGeometry
open MaskedArithmeticGeometry ArratiaGoldsteinGordonInput ConditionalStartProbability
open ConditionalAGGInstantiation ConditionalAGGAverage SectionThirteenFiniteBound
open FiniteFieldTotalVariation FiniteFieldPoissonCoupling ProcessAGGInput
open scoped BigOperators NNReal

noncomputable section
@[reducible]
local instance instDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- Geometric rates, with all excesses and both signs still identified. -/
def allSignedRates (sites : Finset ℕ) (L E : ℕ) (mask : Finset ℕ) (i : LabelledIndex sites (Fin (E+1) × F₂)) : ℝ≥0 :=
  if i.1.val ∈ mask then signedMarkRate L i.2.1.val else 0

def retainedSignedIndices (sites : Finset ℕ) (L E Y : ℕ) (mask : Finset ℕ) : Finset (LabelledIndex sites (Fin (E+1) × F₂)) :=
  Finset.univ.filter fun i => i.1.val ∈ goodMask (L+E+1) Y mask

/-- The true probability mass removed at defective maximal supports. -/
def badSignedMass (C L E Y : ℕ) (mask : Finset ℕ) (sigma : SmallSample C Y) : ℝ :=
  ∑ x ∈ badMask (L+E+1) Y mask, ∑ a : Fin (E+1) × F₂,
    eventProbability (largeUniformPMF C Y) (fun eta => conditionedSignedAt C L E Y sigma x a eta = true)

theorem retainedIndicators_signed_eq (C : ℕ) (sites : Finset ℕ) (L E Y : ℕ) (mask : Finset ℕ) (sigma : SmallSample C Y) :
    retainedIndicators (retainedSignedIndices sites L E Y mask)
      (maskedLabelledFamily sites (conditionedSignedAt C L E Y sigma) mask) =
      maskedLabelledFamily sites (conditionedSignedAt C L E Y sigma) (goodMask (L+E+1) Y mask) := by
  funext i eta
  by_cases hi : i.1.val ∈ goodMask (L+E+1) Y mask
  · have hm := goodMask_subset (L+E+1) Y mask hi
    simp [retainedIndicators,retainedSignedIndices,maskedLabelledFamily,maskedLabelIndicator,hi,hm]
  · simp [retainedIndicators,retainedSignedIndices,maskedLabelledFamily,maskedLabelIndicator,hi]

theorem retainedRates_signed_eq (sites : Finset ℕ) (L E Y : ℕ) (mask : Finset ℕ) :
    retainedRates (retainedSignedIndices sites L E Y mask) (allSignedRates sites L E mask) =
      allSignedRates sites L E (goodMask (L+E+1) Y mask) := by
  funext i
  by_cases hi : i.1.val ∈ goodMask (L+E+1) Y mask
  · have hm := goodMask_subset (L+E+1) Y mask hi
    simp [retainedRates,retainedSignedIndices,allSignedRates,hi,hm]
  · simp [retainedRates,retainedSignedIndices,allSignedRates,hi]

theorem fieldRates_good_signed_eq {C L E Y : ℕ} {sites : Finset ℕ}
    (hsite : ∀ x ∈ sites, 2 ≤ x) (hL : 1 ≤ L) (hC : ∀ x ∈ sites, x+L+E+1 ≤ C)
    (hY : L+E+2 ≤ Y) (mask : Finset ℕ) (sigma : SmallSample C Y) :
    fieldRates (largeUniformPMF C Y)
      (maskedLabelledFamily sites (conditionedSignedAt C L E Y sigma) (goodMask (L+E+1) Y mask)) =
      allSignedRates sites L E (goodMask (L+E+1) Y mask) := by
  funext i
  apply NNReal.eq
  change marginal _ _ i = _
  rw [BulkMarkedDependency.signedAt_marginal_masked_good hsite hL hC hY]
  simp only [allSignedRates]
  split_ifs <;> rfl

/-- Reindexing deletion retains the exact total mass of all label alternatives. -/
theorem bad_marginal_sum_signed_eq {C L E Y : ℕ} {sites : Finset ℕ} (mask : Finset ℕ)
    (hmask : mask ⊆ sites) (sigma : SmallSample C Y) :
    (∑ i ∈ badFieldSites (retainedSignedIndices sites L E Y mask),
      marginal (largeUniformPMF C Y) (maskedLabelledFamily sites (conditionedSignedAt C L E Y sigma) mask) i) =
      badSignedMass C L E Y mask sigma := by
  rw [badFieldSites,Finset.sum_filter]
  trans ∑ i : LabelledIndex sites (Fin (E+1) × F₂), if i.1.val ∈ badMask (L+E+1) Y mask then
    eventProbability (largeUniformPMF C Y) (fun eta => conditionedSignedAt C L E Y sigma i.1.val i.2 eta = true) else 0
  · apply Finset.sum_congr rfl
    intro i _
    by_cases hb : i.1.val ∈ badMask (L+E+1) Y mask
    · have hm := badMask_subset (L+E+1) Y mask hb
      simp [retainedSignedIndices,mem_goodMask,hm,hb,marginal,
        maskedLabelledFamily,maskedLabelIndicator,labelledFamily,eventProbability]
      apply Finset.sum_congr rfl
      intro eta _
      by_cases hs : conditionedSignedAt C L E Y sigma i.1.val i.2 eta = true <;> simp [hs]
    · by_cases hm : i.1.val ∈ mask <;>
        simp [retainedSignedIndices,mem_goodMask,hm,hb,marginal,
          maskedLabelledFamily,maskedLabelIndicator,eventProbability]
  rw [sum_labelledIndex (κ := Fin (E+1) × F₂) sites (fun x a => if x ∈ badMask (L+E+1) Y mask then
    eventProbability (largeUniformPMF C Y) (fun eta => conditionedSignedAt C L E Y sigma x a eta = true) else 0)]
  simp_rw [Finset.sum_ite_irrel,Finset.sum_const_zero]
  rw [← Finset.sum_filter]
  have hf : (sites).filter (fun x => x ∈ badMask (L+E+1) Y mask) = badMask (L+E+1) Y mask := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨And.right,fun hx => ⟨hmask (badMask_subset (L+E+1) Y mask hx),hx⟩⟩
  rw [hf]
  rfl

/-- Target deletion costs at most the base probability per removed site. -/
theorem bad_target_sum_signed_le {L E Y : ℕ} {sites : Finset ℕ} (mask : Finset ℕ) (hmask : mask ⊆ sites) :
    (∑ i ∈ badFieldSites (retainedSignedIndices sites L E Y mask), (allSignedRates sites L E mask i : ℝ)) ≤
      (1/(2 : ℝ)^L) * (badMask (L+E+1) Y mask).card := by
  rw [badFieldSites,Finset.sum_filter]
  trans ∑ i : LabelledIndex sites (Fin (E+1) × F₂), if i.1.val ∈ badMask (L+E+1) Y mask then
    (signedMarkRate L i.2.1.val : ℝ) else 0
  · apply le_of_eq
    apply Finset.sum_congr rfl
    intro i _
    by_cases hb : i.1.val ∈ badMask (L+E+1) Y mask
    · have hm := badMask_subset (L+E+1) Y mask hb
      simp [retainedSignedIndices,allSignedRates,mem_goodMask,hm,hb]
    · by_cases hm : i.1.val ∈ mask <;>
        simp [retainedSignedIndices,allSignedRates,mem_goodMask,hm,hb]
  rw [sum_labelledIndex (κ := Fin (E+1) × F₂) sites (fun x a => if x ∈ badMask (L+E+1) Y mask then (signedMarkRate L a.1.val : ℝ) else 0)]
  simp_rw [Finset.sum_ite_irrel,Finset.sum_const_zero]
  rw [← Finset.sum_filter]
  have hf : (sites).filter (fun x => x ∈ badMask (L+E+1) Y mask) = badMask (L+E+1) Y mask := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨And.right,fun hx => ⟨hmask (badMask_subset (L+E+1) Y mask hx),hx⟩⟩
  rw [hf]
  calc
    _ ≤ ∑ _x ∈ badMask (L+E+1) Y mask, 1/(2 : ℝ)^L := by
      apply Finset.sum_le_sum
      intro x hx
      simpa only [Fintype.sum_prod_type] using sum_all_signedMarkRate_le_base L E
    _ = _ := by simp [mul_comm]

/-- Conditional comparison of the full labelled signed field, before arithmetic bounds, on the actual finite population. -/
theorem signed_field_process_with_deletion (hAGG : ProcessAGGStatement)
    {C L E Y : ℕ} {sites : Finset ℕ} (hsite : ∀ x ∈ sites, 2 ≤ x) (hL : 1 ≤ L) (hC : ∀ x ∈ sites, x+L+E+1 ≤ C)
    (hY : L+E+2 ≤ Y) (mask : Finset ℕ) (hmask : mask ⊆ sites) (sigma : SmallSample C Y) :
    massTotalVariation
      (finiteFieldLaw (largeUniformPMF C Y) (indicatorField (maskedLabelledFamily sites (conditionedSignedAt C L E Y sigma) mask)))
      (poissonFieldMass (allSignedRates sites L E mask)) ≤
      badSignedMass C L E Y mask sigma +
      2 * (bOne (largeUniformPMF C Y)
        (maskedLabelledFamily sites (conditionedSignedAt C L E Y sigma) (goodMask (L+E+1) Y mask))
        (labelledGraph sites (L+E+1) Y (Fin (E+1) × F₂)) +
        bTwo (largeUniformPMF C Y)
        (maskedLabelledFamily sites (conditionedSignedAt C L E Y sigma) (goodMask (L+E+1) Y mask))
        (labelledGraph sites (L+E+1) Y (Fin (E+1) × F₂))) +
      (1/(2 : ℝ)^L) * (badMask (L+E+1) Y mask).card := by
  have hdep := BulkMarkedDependency.hasExactDependencyGraph_signed (C := C) (E := E) hsite hL (goodMask (L+E+1) Y mask) sigma
  rw [← retainedIndicators_signed_eq] at hdep
  have hrates : fieldRates (largeUniformPMF C Y)
      (retainedIndicators (retainedSignedIndices sites L E Y mask) (maskedLabelledFamily sites (conditionedSignedAt C L E Y sigma) mask)) =
      retainedRates (retainedSignedIndices sites L E Y mask) (allSignedRates sites L E mask) := by
    rw [retainedIndicators_signed_eq,fieldRates_good_signed_eq hsite hL hC hY,retainedRates_signed_eq]
  have h := process_totalVariation_via_retention hAGG (largeUniformPMF C Y)
    (maskedLabelledFamily sites (conditionedSignedAt C L E Y sigma) mask) (retainedSignedIndices sites L E Y mask)
    (allSignedRates sites L E mask) (labelledGraph sites (L+E+1) Y (Fin (E+1) × F₂)) hdep hrates
  rw [retainedIndicators_signed_eq,bad_marginal_sum_signed_eq mask hmask] at h
  exact h.trans (add_le_add_right (bad_target_sum_signed_le mask hmask) _)

end
end PaperC.V282.BulkMarkedTransfer
