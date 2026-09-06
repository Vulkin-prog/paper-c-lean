import PaperCV282.ExactMarkedAggregation
import PaperCV282.DictionaryFieldTransfer

/-!
# Retention and process comparison of the entire signed exact-mark field

The same full site/mark/sign carrier is used for the source and both targets.
Only the explicit process AGG input is required. Rates vary with the excess.
-/
namespace PaperC.V282.ExactMarkedFieldTransfer

open ExactMarkedModel ExactMarkedDependency ExactMarkedAggregation LabelledSupportGraph LabelledProcessCosts
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
def allSignedRates (N L E : ℕ) (mask : Finset ℕ) (i : SignedMarkIndex N E) : ℝ≥0 :=
  if i.1.val ∈ mask then signedMarkRate L i.2.1.val else 0

def retainedSignedIndices (N L E Y : ℕ) (mask : Finset ℕ) : Finset (SignedMarkIndex N E) :=
  Finset.univ.filter fun i => i.1.val ∈ fullGoodMask N (L+E+1) Y mask

/-- The true probability mass removed at defective maximal supports. -/
def badSignedMass (C N L E Y : ℕ) (mask : Finset ℕ) (sigma : SmallSample C Y) : ℝ :=
  ∑ x ∈ fullBadMask N (L+E+1) Y mask, ∑ a : Fin (E+1) × F₂,
    eventProbability (largeUniformPMF C Y) (fun eta => conditionedSignedAt C L E Y sigma x a eta = true)

theorem retainedIndicators_signed_eq (C N L E Y : ℕ) (mask : Finset ℕ) (sigma : SmallSample C Y) :
    retainedIndicators (retainedSignedIndices N L E Y mask)
      (maskedLabelledFamily N (conditionedSignedAt C L E Y sigma) mask) =
      maskedLabelledFamily N (conditionedSignedAt C L E Y sigma) (fullGoodMask N (L+E+1) Y mask) := by
  funext i eta
  by_cases hi : i.1.val ∈ fullGoodMask N (L+E+1) Y mask
  · have hm := fullGoodMask_subset_mask N (L+E+1) Y mask hi
    simp [retainedIndicators,retainedSignedIndices,maskedLabelledFamily,maskedLabelIndicator,hi,hm]
  · simp [retainedIndicators,retainedSignedIndices,maskedLabelledFamily,maskedLabelIndicator,hi]

theorem retainedRates_signed_eq (N L E Y : ℕ) (mask : Finset ℕ) :
    retainedRates (retainedSignedIndices N L E Y mask) (allSignedRates N L E mask) =
      allSignedRates N L E (fullGoodMask N (L+E+1) Y mask) := by
  funext i
  by_cases hi : i.1.val ∈ fullGoodMask N (L+E+1) Y mask
  · have hm := fullGoodMask_subset_mask N (L+E+1) Y mask hi
    simp [retainedRates,retainedSignedIndices,allSignedRates,hi,hm]
  · simp [retainedRates,retainedSignedIndices,allSignedRates,hi]

theorem fieldRates_good_signed_eq {C N L E Y : ℕ}
    (hN : 2 ≤ N) (hL : 1 ≤ L) (hC : dyadicCutoff N (L+E+1) ≤ C)
    (hY : L+E+2 ≤ Y) (mask : Finset ℕ) (sigma : SmallSample C Y) :
    fieldRates (largeUniformPMF C Y)
      (maskedLabelledFamily N (conditionedSignedAt C L E Y sigma) (fullGoodMask N (L+E+1) Y mask)) =
      allSignedRates N L E (fullGoodMask N (L+E+1) Y mask) := by
  funext i
  apply NNReal.eq
  change marginal _ _ i = _
  rw [signedAt_marginal_masked_good hN hL hC hY]
  simp only [allSignedRates]
  split_ifs <;> rfl

/-- Reindexing deletion retains the exact total mass of all label alternatives. -/
theorem bad_marginal_sum_signed_eq {C N L E Y : ℕ} (mask : Finset ℕ)
    (hmask : mask ⊆ dyadicBlock N) (sigma : SmallSample C Y) :
    (∑ i ∈ badFieldSites (retainedSignedIndices N L E Y mask),
      marginal (largeUniformPMF C Y) (maskedLabelledFamily N (conditionedSignedAt C L E Y sigma) mask) i) =
      badSignedMass C N L E Y mask sigma := by
  rw [badFieldSites,Finset.sum_filter]
  trans ∑ i : SignedMarkIndex N E, if i.1.val ∈ fullBadMask N (L+E+1) Y mask then
    eventProbability (largeUniformPMF C Y) (fun eta => conditionedSignedAt C L E Y sigma i.1.val i.2 eta = true) else 0
  · apply Finset.sum_congr rfl
    intro i _
    by_cases hm : i.1.val ∈ mask <;> by_cases hb : i.1.val ∈ fullBadStarts N (L+E+1) Y <;>
      simp [retainedSignedIndices,mem_fullGoodMask,mem_fullBadMask,hm,hb,marginal,
        maskedLabelledFamily,maskedLabelIndicator,labelledFamily,eventProbability]
    all_goals
      apply Finset.sum_congr rfl
      intro eta _
      by_cases hs : conditionedSignedAt C L E Y sigma i.1.val i.2 eta = true <;> simp [hs]
  rw [sum_labelledIndex (κ := Fin (E+1) × F₂) N (fun x a => if x ∈ fullBadMask N (L+E+1) Y mask then
    eventProbability (largeUniformPMF C Y) (fun eta => conditionedSignedAt C L E Y sigma x a eta = true) else 0)]
  simp_rw [Finset.sum_ite_irrel,Finset.sum_const_zero]
  rw [← Finset.sum_filter]
  have hf : (dyadicBlock N).filter (fun x => x ∈ fullBadMask N (L+E+1) Y mask) = fullBadMask N (L+E+1) Y mask := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨And.right,fun hx => ⟨hmask (fullBadMask_subset_mask N (L+E+1) Y mask hx),hx⟩⟩
  rw [hf]
  rfl

/-- Target deletion costs at most the base probability per removed site. -/
theorem bad_target_sum_signed_le {N L E Y : ℕ} (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N) :
    (∑ i ∈ badFieldSites (retainedSignedIndices N L E Y mask), (allSignedRates N L E mask i : ℝ)) ≤
      (1/(2 : ℝ)^L) * (fullBadMask N (L+E+1) Y mask).card := by
  rw [badFieldSites,Finset.sum_filter]
  trans ∑ i : SignedMarkIndex N E, if i.1.val ∈ fullBadMask N (L+E+1) Y mask then
    (signedMarkRate L i.2.1.val : ℝ) else 0
  · apply le_of_eq
    apply Finset.sum_congr rfl
    intro i _
    by_cases hm : i.1.val ∈ mask <;> by_cases hb : i.1.val ∈ fullBadStarts N (L+E+1) Y <;>
      simp [retainedSignedIndices,allSignedRates,mem_fullGoodMask,mem_fullBadMask,hm,hb]
  rw [sum_labelledIndex (κ := Fin (E+1) × F₂) N (fun x a => if x ∈ fullBadMask N (L+E+1) Y mask then (signedMarkRate L a.1.val : ℝ) else 0)]
  simp_rw [Finset.sum_ite_irrel,Finset.sum_const_zero]
  rw [← Finset.sum_filter]
  have hf : (dyadicBlock N).filter (fun x => x ∈ fullBadMask N (L+E+1) Y mask) = fullBadMask N (L+E+1) Y mask := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨And.right,fun hx => ⟨hmask (fullBadMask_subset_mask N (L+E+1) Y mask hx),hx⟩⟩
  rw [hf]
  calc
    _ ≤ ∑ _x ∈ fullBadMask N (L+E+1) Y mask, 1/(2 : ℝ)^L := by
      apply Finset.sum_le_sum
      intro x hx
      simpa only [Fintype.sum_prod_type] using sum_all_signedMarkRate_le_base L E
    _ = _ := by simp [mul_comm]

/-- Conditional comparison of the full labelled signed field, before arithmetic bounds. -/
theorem signed_field_process_with_deletion (hAGG : ProcessAGGStatement)
    {C N L E Y : ℕ} (hN : 2 ≤ N) (hL : 1 ≤ L) (hC : dyadicCutoff N (L+E+1) ≤ C)
    (hY : L+E+2 ≤ Y) (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N) (sigma : SmallSample C Y) :
    massTotalVariation
      (finiteFieldLaw (largeUniformPMF C Y) (indicatorField (maskedLabelledFamily N (conditionedSignedAt C L E Y sigma) mask)))
      (poissonFieldMass (allSignedRates N L E mask)) ≤
      badSignedMass C N L E Y mask sigma +
      2 * (bOne (largeUniformPMF C Y)
        (maskedLabelledFamily N (conditionedSignedAt C L E Y sigma) (fullGoodMask N (L+E+1) Y mask))
        (labelledGraph N (L+E+1) Y (Fin (E+1) × F₂)) +
        bTwo (largeUniformPMF C Y)
        (maskedLabelledFamily N (conditionedSignedAt C L E Y sigma) (fullGoodMask N (L+E+1) Y mask))
        (labelledGraph N (L+E+1) Y (Fin (E+1) × F₂))) +
      (1/(2 : ℝ)^L) * (fullBadMask N (L+E+1) Y mask).card := by
  have hdep := hasExactDependencyGraph_signed (C := C) (E := E) hN hL (fullGoodMask N (L+E+1) Y mask) sigma
  rw [← retainedIndicators_signed_eq] at hdep
  have hrates : fieldRates (largeUniformPMF C Y)
      (retainedIndicators (retainedSignedIndices N L E Y mask) (maskedLabelledFamily N (conditionedSignedAt C L E Y sigma) mask)) =
      retainedRates (retainedSignedIndices N L E Y mask) (allSignedRates N L E mask) := by
    rw [retainedIndicators_signed_eq,fieldRates_good_signed_eq hN hL hC hY,retainedRates_signed_eq]
  have h := process_totalVariation_via_retention hAGG (largeUniformPMF C Y)
    (maskedLabelledFamily N (conditionedSignedAt C L E Y sigma) mask) (retainedSignedIndices N L E Y mask)
    (allSignedRates N L E mask) (labelledGraph N (L+E+1) Y (Fin (E+1) × F₂)) hdep hrates
  rw [retainedIndicators_signed_eq,bad_marginal_sum_signed_eq mask hmask] at h
  exact h.trans (add_le_add_right (bad_target_sum_signed_le mask hmask) _)

end
end PaperC.V282.ExactMarkedFieldTransfer
