import PaperCV282.BulkMarkedTransfer
import PaperCV282.FiniteStartMaskPairBounds
import PaperCV282.PointwiseStartBounds
import PaperCV282.MaskedBadMass

/-! # Deletion on arbitrary marked populations at the base threshold -/
namespace PaperC.V282.BulkMarkedDeletion

open ExactMarkedModel ExactMarkedDependency ExactMarkedAggregation BulkMarkedTransfer
open BulkSupportGraph BulkProcessCosts MacroscopicMaskGeometry MaskedArithmeticGeometry MaskedBadMass
open ArratiaGoldsteinGordonInput ConditionalStartProbability ConditionalAGGInstantiation
open ConditionalAGGAverage SectionThirteenFiniteBound SectionTwelveMoments Affine
open FiniteFieldTotalVariation FiniteFieldPoissonCoupling ProcessAGGInput
open scoped BigOperators NNReal

noncomputable section
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

theorem uniform_start_le_full_defects {C L x : ℕ} (hx : 2≤x) (hL : 1≤L) (hcut : x+L≤C) :
    uniformEventProbability (fun omega : SampleSpace C => startAt omega x L) ≤
      (1+((2^(WindowValues.defectIndices (L+1) x (L+1)).card-1 : ℕ) : ℚ))/(2 : ℚ)^L := by
  rw [FiniteStartMaskPairBounds.uniform_start_eq_affine C L x (by omega)]
  apply (PointwiseStartBounds.corollary_two_five_upper_finite hx hcut (startRhs L)).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [Nat.cast_sub Nat.one_le_two_pow]
  push_cast
  have h := pow_le_pow_right₀ (by norm_num : (1 : ℚ)≤2)
    (Nat.sub_le (WindowValues.defectIndices (L+1) x (L+1)).card 1)
  linarith

theorem average_bad_signed_mass_le {C L E Y : ℕ} {sites : Finset ℕ}
    (hsite : ∀ x ∈ sites, 2 ≤ x) (hL : 1 ≤ L) (hC : ∀ x ∈ sites, x+L+E+1 ≤ C)
    (mask : Finset ℕ) (hmask : mask ⊆ sites) :
    finiteUniformAverage (badSignedMass C L E Y mask) ≤
      (1/(2 : ℝ)^L) * ((fullDefectMass L mask : ℝ) + (badMask (L+E+1) Y mask).card) := by
  unfold badSignedMass
  rw [finiteUniformAverage_finsetSum]
  calc
    _ ≤ ∑ x ∈ badMask (L+E+1) Y mask,
        (1+((2^(WindowValues.defectIndices (L+1) x (L+1)).card-1 : ℕ) : ℝ))/(2 : ℝ)^L := by
      apply Finset.sum_le_sum
      intro x hx
      have hxs := hmask (badMask_subset (L+E+1) Y mask hx)
      have hc := hC x hxs
      have ha := finiteUniformAverage_mono (fun sigma : SmallSample C Y =>
        sum_conditioned_signed_probability_le_base C L E Y x sigma hL)
      change finiteUniformAverage (fun sigma : SmallSample C Y => ∑ a : Fin (E+1) × F₂,
        eventProbability (largeUniformPMF C Y) (fun eta => conditionedSignedAt C L E Y sigma x a eta = true)) ≤
        finiteUniformAverage (fun sigma : SmallSample C Y => eventProbability (largeUniformPMF C Y)
          (fun eta => startAt (assemble C Y sigma eta) x L)) at ha
      rw [finiteUniformAverage_largeEventProbability_eq_full C Y (fun omega => startAt omega x L)] at ha
      have hh := (Rat.cast_le (K := ℝ)).mpr (uniform_start_le_full_defects (hsite x hxs) hL (by omega : x+L≤C))
      push_cast at hh
      exact ha.trans hh
    _ = (1/(2 : ℝ)^L) * ((fullDefectMass L (badMask (L+E+1) Y mask) : ℝ) +
        (badMask (L+E+1) Y mask).card) := by
      rw [← Finset.sum_div,Finset.sum_add_distrib]
      simp [fullDefectMass]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hh : (fullDefectMass L (badMask (L+E+1) Y mask) : ℝ) ≤ fullDefectMass L mask := by
        exact_mod_cast fullDefectMass_mono (L := L) (badMask_subset (L+E+1) Y mask)
      linarith

/-- The full signed law with only the actual maximal graph costs left to estimate. -/
theorem average_signed_field_le_deletion_and_graph (hAGG : ProcessAGGStatement)
    {C L E Y : ℕ} {sites : Finset ℕ} (hsite : ∀ x ∈ sites, 2 ≤ x) (hL : 1 ≤ L) (hC : ∀ x ∈ sites, x+L+E+1 ≤ C)
    (hY : L+E+2 ≤ Y) (mask : Finset ℕ) (hmask : mask ⊆ sites) :
    finiteUniformAverage (fun sigma : SmallSample C Y =>
      massTotalVariation (finiteFieldLaw (largeUniformPMF C Y)
        (indicatorField (maskedLabelledFamily sites (conditionedSignedAt C L E Y sigma) mask)))
        (poissonFieldMass (allSignedRates sites L E mask))) ≤
      (1/(2 : ℝ)^L) * ((fullDefectMass L mask : ℝ) + 2*(badMask (L+E+1) Y mask).card) +
      2*finiteUniformAverage (fun sigma : SmallSample C Y =>
        bOne (largeUniformPMF C Y)
          (maskedLabelledFamily sites (conditionedSignedAt C L E Y sigma) (goodMask (L+E+1) Y mask))
          (labelledGraph sites (L+E+1) Y (Fin (E+1) × F₂)) +
        bTwo (largeUniformPMF C Y)
          (maskedLabelledFamily sites (conditionedSignedAt C L E Y sigma) (goodMask (L+E+1) Y mask))
          (labelledGraph sites (L+E+1) Y (Fin (E+1) × F₂))) := by
  have h := finiteUniformAverage_mono (fun sigma =>
    signed_field_process_with_deletion hAGG hsite hL hC hY mask hmask sigma)
  have hav {ι : Type} [Fintype ι] [Nonempty ι] (f g : ι → ℝ) (c : ℝ) :
      finiteUniformAverage (fun i => f i + 2*g i + c) =
        finiteUniformAverage f + 2*finiteUniformAverage g + c := by
    unfold finiteUniformAverage
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib,← Finset.mul_sum]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp
  rw [hav] at h
  have hd := average_bad_signed_mass_le (Y := Y) hsite hL hC mask hmask
  linarith

end
end PaperC.V282.BulkMarkedDeletion
