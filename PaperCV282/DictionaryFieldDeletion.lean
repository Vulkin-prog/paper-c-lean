import PaperCV282.DictionaryFieldTransfer
import PaperCV282.FullBandArithmetic

/-!
# Averaged actual deletion cost for a growing dictionary

The complete root-inclusive defect mass is multiplied by m/2^(L+1).
Actual words and target coordinates are both deleted, retaining the
chosen position mask and the exact dictionary multiplicity.
-/

namespace PaperC.V282.DictionaryFieldDeletion

open DictionaryFieldModel DictionaryFieldTransfer MaskedArithmeticGeometry MaskedBadMass FullBandArithmetic
open ArratiaGoldsteinGordonInput ConditionalStartProbability ConditionalAGGInstantiation
open ConditionalAGGAverage SectionThirteenFiniteBound SectionTwelveMoments
open FiniteFieldTotalVariation FiniteFieldPoissonCoupling ProcessAGGInput
open PrescribedValues WindowValues InfiniteWordTransfer Affine
open scoped BigOperators NNReal

noncomputable section

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- Finite actual word probability is bounded by its complete defective-vertex weight. -/
theorem finite_word_probability_le_defect {M x B : ℕ} (hx : 2 ≤ x)
    (hcut : x - 1 + B ≤ M + 1) (b : Fin B → F₂) :
    ((uniformEventProbability (fun omega : SampleSpace M => omega ∈ finiteWordEvent M x B b) : ℚ) : ℝ) ≤
      (2 : ℝ) ^ (defectIndices B x B).card / (2 : ℝ) ^ B := by
  have h := (Rat.cast_le (K := ℝ)).mpr (corollary_two_six_pointwise hx hcut b)
  have hp : uniformSolutionProbability (valueSystem M (vertex x B)) b =
      uniformEventProbability (fun omega : SampleSpace M => omega ∈ finiteWordEvent M x B b) := by
    rw [PrescribedValues.probability_eq_uniform_event]
    unfold uniformEventProbability
    congr 2
    apply congrArg Finset.card
    ext omega
    simp [finiteWordEvent]
  rw [hp] at h
  push_cast at h
  have hab := le_abs_self (((uniformEventProbability (fun omega : SampleSpace M =>
    omega ∈ finiteWordEvent M x B b) : ℚ) : ℝ) - 1 / (2 : ℝ) ^ B)
  have heq : ((2 : ℝ) ^ (defectIndices B x B).card - 1) / (2 : ℝ) ^ B + 1 / (2 : ℝ) ^ B =
      (2 : ℝ) ^ (defectIndices B x B).card / (2 : ℝ) ^ B := by ring
  linarith

theorem average_dictionary_marginal_le_defect {N L Y : ℕ}
    (W : Finset (Fin (L + 1) → F₂)) (hN : 2 ≤ N) (i : DictionaryIndex N L W) :
    finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
      marginal (largeUniformPMF (dyadicCutoff N L) Y) (conditionedWordIndicator N L Y W sigma) i) ≤
      (2 : ℝ) ^ (defectIndices (L + 1) i.1.val (L + 1)).card / (2 : ℝ) ^ (L + 1) := by
  rw [average_marginal_conditionedWordIndicator]
  apply finite_word_probability_le_defect (two_le_of_mem_dyadicBlock hN i.1.property)
  have hb := Finset.mem_Ico.mp i.1.property
  unfold dyadicCutoff
  omega

/-- Summing powers restores the exact baseline count removed by the defect subtraction. -/
theorem sum_defectWeight_eq_mass_add_card (L : ℕ) (s : Finset ℕ) :
    (∑ x ∈ s, (2 : ℝ) ^ (defectIndices (L + 1) x (L + 1)).card) =
      (fullDefectMass L s : ℝ) + s.card := by
  rw [fullDefectMass_cast_real,Finset.sum_sub_distrib]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
  ring

/-- The genuine averaged removed mass, uniform in every finite distinct-word dictionary. -/
theorem average_bad_word_mass_le {N L Y : ℕ}
    (W : Finset (Fin (L + 1) → F₂)) (mask : Finset ℕ)
    (hmask : mask ⊆ dyadicBlock N) (hN : 2 ≤ N) :
    finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
      ∑ i : DictionaryIndex N L W, if i.1.val ∈ fullBadMask N L Y mask then
        marginal (largeUniformPMF (dyadicCutoff N L) Y) (conditionedWordIndicator N L Y W sigma) i else 0) ≤
      (dictionaryRate L W : ℝ) * ((fullDefectMass L mask : ℝ) + (fullBadMask N L Y mask).card) := by
  rw [finiteUniformAverage_fintypeSum]
  calc
    _ ≤ ∑ i : DictionaryIndex N L W, if i.1.val ∈ fullBadMask N L Y mask then
        (2 : ℝ) ^ (defectIndices (L + 1) i.1.val (L + 1)).card / (2 : ℝ) ^ (L + 1) else 0 := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hb : i.1.val ∈ fullBadMask N L Y mask
      · simp only [if_pos hb]
        exact average_dictionary_marginal_le_defect W hN i
      · simp [hb,finiteUniformAverage]
    _ = (dictionaryRate L W : ℝ) *
        ((fullDefectMass L (fullBadMask N L Y mask) : ℝ) + (fullBadMask N L Y mask).card) := by
      rw [sum_dictionaryIndex_site N L W (fun x => if x ∈ fullBadMask N L Y mask then
        (2 : ℝ) ^ (defectIndices (L + 1) x (L + 1)).card / (2 : ℝ) ^ (L + 1) else 0),
        ← Finset.sum_filter]
      have hf : (dyadicBlock N).filter (fun x => x ∈ fullBadMask N L Y mask) = fullBadMask N L Y mask := by
        ext x
        simp only [Finset.mem_filter]
        exact ⟨And.right,fun hx => ⟨hmask (fullBadMask_subset_mask N L Y mask hx),hx⟩⟩
      rw [hf,← Finset.sum_div,sum_defectWeight_eq_mass_add_card,dictionaryRate_coe]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (dictionaryRate L W).coe_nonneg
      have hm : (fullDefectMass L (fullBadMask N L Y mask) : ℝ) ≤ (fullDefectMass L mask : ℝ) := by
        exact_mod_cast (fullDefectMass_mono (L := L) (fullBadMask_subset_mask N L Y mask))
      linarith

/-- Averaged process transfer with its actual word-deletion cost and exact retained graph costs. -/
theorem average_dictionary_field_le_deletion_and_graph (hAGG : ProcessAGGStatement)
    {N L Y : ℕ} (W : Finset (Fin (L + 1) → F₂)) (mask : Finset ℕ)
    (hmask : mask ⊆ dyadicBlock N) (hN : 2 ≤ N) (hLY : L + 1 ≤ Y) :
    finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
      massTotalVariation
        (finiteFieldLaw (largeUniformPMF (dyadicCutoff N L) Y)
          (indicatorField (maskedWordIndicator N L Y W mask sigma)))
        (poissonFieldMass (allWordRates N L W mask))) ≤
      (dictionaryRate L W : ℝ) * ((fullDefectMass L mask : ℝ) + 2 * (fullBadMask N L Y mask).card) +
      2 * finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
        bOne (largeUniformPMF (dyadicCutoff N L) Y)
          (maskedWordIndicator N L Y W (fullGoodMask N L Y mask) sigma)
          (DictionaryFieldDependency.dictionaryGraph N L Y W) +
        bTwo (largeUniformPMF (dyadicCutoff N L) Y)
          (maskedWordIndicator N L Y W (fullGoodMask N L Y mask) sigma)
          (DictionaryFieldDependency.dictionaryGraph N L Y W)) := by
  have h := finiteUniformAverage_mono (fun sigma =>
    dictionary_field_process_with_deletion hAGG W mask hmask hN hLY sigma)
  have hav {ι : Type} [Fintype ι] [Nonempty ι] (f g : ι → ℝ) (c : ℝ) :
      finiteUniformAverage (fun i => f i + 2 * g i + c) =
        finiteUniformAverage f + 2 * finiteUniformAverage g + c := by
    unfold finiteUniformAverage
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib,← Finset.mul_sum]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp
  rw [hav] at h
  have hdel := average_bad_word_mass_le W mask hmask hN (Y := Y)
  linarith

end
end PaperC.V282.DictionaryFieldDeletion
