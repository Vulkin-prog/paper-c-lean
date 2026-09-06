import PaperCV282.DictionaryFieldDependency
import PaperCV282.MaskedBadMass

/-!
# Retention and Poisson comparison without losing any dictionary label

Actual and retained fields and both product Poisson targets use the same
site-and-word carrier. The only probability comparison premise is the
explicit finite process AGG theorem. Word probabilities use L+1 bits.
-/

namespace PaperC.V282.DictionaryFieldTransfer

open DictionaryFieldModel DictionaryFieldDependency MaskedArithmeticGeometry MaskedBadMass
open ArratiaGoldsteinGordonInput ConditionalStartProbability ConditionalAGGInstantiation
open ConditionalAGGAverage SectionThirteenFiniteBound SectionTwelveMoments
open FiniteFieldTotalVariation FiniteFieldPoissonCoupling ProcessAGGInput
open PrescribedValues WindowValues InfiniteWordTransfer Affine
open scoped BigOperators NNReal

noncomputable section

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

def allWordRates (N L : ℕ) (W : Finset (Fin (L + 1) → F₂)) (mask : Finset ℕ)
    (i : DictionaryIndex N L W) : ℝ≥0 :=
  if i.1.val ∈ mask then wordRate L else 0

def retainedDictionaryIndices (N L Y : ℕ) (W : Finset (Fin (L + 1) → F₂)) (mask : Finset ℕ) :
    Finset (DictionaryIndex N L W) :=
  Finset.univ.filter (fun i => i.1.val ∈ fullGoodMask N L Y mask)

theorem retainedIndicators_dictionary_eq (N L Y : ℕ) (W : Finset (Fin (L + 1) → F₂))
    (mask : Finset ℕ) (sigma : SmallSample (dyadicCutoff N L) Y) :
    retainedIndicators (retainedDictionaryIndices N L Y W mask) (maskedWordIndicator N L Y W mask sigma) =
      maskedWordIndicator N L Y W (fullGoodMask N L Y mask) sigma := by
  classical
  funext i eta
  by_cases hi : i.1.val ∈ fullGoodMask N L Y mask
  · have hm := fullGoodMask_subset_mask N L Y mask hi
    simp [retainedIndicators,retainedDictionaryIndices,maskedWordIndicator,hi,hm]
  · simp [retainedIndicators,retainedDictionaryIndices,maskedWordIndicator,hi]

theorem retainedRates_dictionary_eq (N L Y : ℕ) (W : Finset (Fin (L + 1) → F₂)) (mask : Finset ℕ) :
    retainedRates (retainedDictionaryIndices N L Y W mask) (allWordRates N L W mask) =
      allWordRates N L W (fullGoodMask N L Y mask) := by
  funext i
  by_cases hi : i.1.val ∈ fullGoodMask N L Y mask
  · have hm := fullGoodMask_subset_mask N L Y mask hi
    simp [retainedRates,retainedDictionaryIndices,allWordRates,hi,hm]
  · simp [retainedRates,retainedDictionaryIndices,allWordRates,hi]

theorem fieldRates_good_dictionary_eq {N L Y : ℕ} (W : Finset (Fin (L + 1) → F₂))
    (mask : Finset ℕ) (hN : 2 ≤ N) (hLY : L + 1 ≤ Y)
    (sigma : SmallSample (dyadicCutoff N L) Y) :
    fieldRates (largeUniformPMF (dyadicCutoff N L) Y)
      (maskedWordIndicator N L Y W (fullGoodMask N L Y mask) sigma) =
      allWordRates N L W (fullGoodMask N L Y mask) := by
  funext i
  apply NNReal.eq
  change marginal (largeUniformPMF (dyadicCutoff N L) Y)
    (maskedWordIndicator N L Y W (fullGoodMask N L Y mask) sigma) i = _
  rw [marginal_maskedWordIndicator]
  by_cases hi : i.1.val ∈ fullGoodMask N L Y mask
  · rw [if_pos hi,marginal_conditionedWordIndicator_of_not_fullBad W hN hLY sigma i
      (mem_fullGoodMask.mp hi).2]
    simp only [allWordRates,if_pos hi]
  · simp [allWordRates,hi]

/-- Summation of a site quantity retains the dictionary multiplicity exactly. -/
theorem sum_dictionaryIndex_site (N L : ℕ) (W : Finset (Fin (L + 1) → F₂)) (f : ℕ → ℝ) :
    (∑ i : DictionaryIndex N L W, f i.1.val) = (W.card : ℝ) * ∑ x ∈ dyadicBlock N, f x := by
  change (∑ i : {x : ℕ // x ∈ dyadicBlock N} × {b : Fin (L + 1) → F₂ // b ∈ W}, f i.1.val) = _
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
  rw [← Finset.mul_sum,← Finset.sum_subtype (dyadicBlock N) (fun _ => Iff.rfl)]

theorem bad_marginal_sum_dictionary_eq (N L Y : ℕ) (W : Finset (Fin (L + 1) → F₂))
    (mask : Finset ℕ) (sigma : SmallSample (dyadicCutoff N L) Y) :
    (∑ i ∈ badFieldSites (retainedDictionaryIndices N L Y W mask),
      marginal (largeUniformPMF (dyadicCutoff N L) Y) (maskedWordIndicator N L Y W mask sigma) i) =
      ∑ i : DictionaryIndex N L W, if i.1.val ∈ fullBadMask N L Y mask then
        marginal (largeUniformPMF (dyadicCutoff N L) Y) (conditionedWordIndicator N L Y W sigma) i else 0 := by
  rw [badFieldSites,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hm : i.1.val ∈ mask <;> by_cases hb : i.1.val ∈ fullBadStarts N L Y <;>
    simp [retainedDictionaryIndices,mem_fullGoodMask,mem_fullBadMask,hm,hb,marginal_maskedWordIndicator]

theorem bad_target_sum_dictionary_eq {N L Y : ℕ} (W : Finset (Fin (L + 1) → F₂))
    (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N) :
    (∑ i ∈ badFieldSites (retainedDictionaryIndices N L Y W mask), (allWordRates N L W mask i : ℝ)) =
      (dictionaryRate L W : ℝ) * (fullBadMask N L Y mask).card := by
  rw [badFieldSites,Finset.sum_filter]
  trans ∑ i : DictionaryIndex N L W, if i.1.val ∈ fullBadMask N L Y mask then (wordRate L : ℝ) else 0
  · apply Finset.sum_congr rfl
    intro i hi
    by_cases hm : i.1.val ∈ mask <;> by_cases hb : i.1.val ∈ fullBadStarts N L Y <;>
      simp [retainedDictionaryIndices,allWordRates,mem_fullGoodMask,mem_fullBadMask,hm,hb]
  rw [sum_dictionaryIndex_site N L W (fun x => if x ∈ fullBadMask N L Y mask then (wordRate L : ℝ) else 0),← Finset.sum_filter]
  have hf : (dyadicBlock N).filter (fun x => x ∈ fullBadMask N L Y mask) = fullBadMask N L Y mask := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hx => ⟨hmask (fullBadMask_subset_mask N L Y mask hx),hx⟩⟩
  rw [hf]
  simp only [Finset.sum_const,nsmul_eq_mul,dictionaryRate_coe,wordRate_coe]
  ring

/-- Finite process comparison plus actual and target deletion, on the full carrier. -/
theorem dictionary_field_process_with_deletion (hAGG : ProcessAGGStatement)
    {N L Y : ℕ} (W : Finset (Fin (L + 1) → F₂)) (mask : Finset ℕ)
    (hmask : mask ⊆ dyadicBlock N) (hN : 2 ≤ N) (hLY : L + 1 ≤ Y)
    (sigma : SmallSample (dyadicCutoff N L) Y) :
    massTotalVariation
      (finiteFieldLaw (largeUniformPMF (dyadicCutoff N L) Y)
        (indicatorField (maskedWordIndicator N L Y W mask sigma)))
      (poissonFieldMass (allWordRates N L W mask)) ≤
      (∑ i : DictionaryIndex N L W, if i.1.val ∈ fullBadMask N L Y mask then
        marginal (largeUniformPMF (dyadicCutoff N L) Y) (conditionedWordIndicator N L Y W sigma) i else 0) +
      2 * (bOne (largeUniformPMF (dyadicCutoff N L) Y)
        (maskedWordIndicator N L Y W (fullGoodMask N L Y mask) sigma) (dictionaryGraph N L Y W) +
        bTwo (largeUniformPMF (dyadicCutoff N L) Y)
        (maskedWordIndicator N L Y W (fullGoodMask N L Y mask) sigma) (dictionaryGraph N L Y W)) +
      (dictionaryRate L W : ℝ) * (fullBadMask N L Y mask).card := by
  have hdep := hasExactDependencyGraph_maskedWordIndicator W (fullGoodMask N L Y mask) hN sigma
  rw [← retainedIndicators_dictionary_eq] at hdep
  have hrates : fieldRates (largeUniformPMF (dyadicCutoff N L) Y)
      (retainedIndicators (retainedDictionaryIndices N L Y W mask) (maskedWordIndicator N L Y W mask sigma)) =
      retainedRates (retainedDictionaryIndices N L Y W mask) (allWordRates N L W mask) := by
    rw [retainedIndicators_dictionary_eq,fieldRates_good_dictionary_eq W mask hN hLY sigma,
      retainedRates_dictionary_eq]
  have h := process_totalVariation_via_retention hAGG (largeUniformPMF (dyadicCutoff N L) Y)
    (maskedWordIndicator N L Y W mask sigma) (retainedDictionaryIndices N L Y W mask)
    (allWordRates N L W mask) (dictionaryGraph N L Y W) hdep hrates
  rw [retainedIndicators_dictionary_eq,bad_marginal_sum_dictionary_eq,bad_target_sum_dictionary_eq W mask hmask] at h
  exact h

end
end PaperC.V282.DictionaryFieldTransfer
