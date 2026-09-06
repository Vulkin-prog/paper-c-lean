import PaperCV282.ExactMarkedFieldTransfer
import PaperCV282.FullCylinderStartLaw
import PaperCV282.DictionaryFieldDeletion

/-!
# Deletion at maximal supports, controlled by the base start threshold

Summing the exact labels first avoids charging a longest-run defect mass.
The cylinder cutoff remains arbitrary and adequate.
-/
namespace PaperC.V282.ExactMarkedDeletion

open ExactMarkedModel ExactMarkedDependency ExactMarkedAggregation ExactMarkedFieldTransfer FullCylinderStartLaw
open LabelledSupportGraph LabelledProcessCosts MaskedArithmeticGeometry MaskedBadMass
open ArratiaGoldsteinGordonInput ConditionalStartProbability ConditionalAGGInstantiation
open ConditionalAGGAverage SectionThirteenFiniteBound SectionTwelveMoments
open FiniteFieldTotalVariation FiniteFieldPoissonCoupling ProcessAGGInput
open scoped BigOperators NNReal

noncomputable section
@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- Averaging the genuinely deleted signed mass uses the original base-length probability. -/
theorem average_bad_signed_mass_le {C N L E Y : ℕ}
    (hN : 2 ≤ N) (hL : 1 ≤ L) (hC : dyadicCutoff N (L+E+1) ≤ C)
    (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N) :
    finiteUniformAverage (badSignedMass C N L E Y mask) ≤
      (1/(2 : ℝ)^L) * ((fullDefectMass L mask : ℝ) + (fullBadMask N (L+E+1) Y mask).card) := by
  unfold badSignedMass
  rw [finiteUniformAverage_finsetSum]
  calc
    _ ≤ ∑ x ∈ fullBadMask N (L+E+1) Y mask, (startProbability N L x : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      have hxb := hmask (fullBadMask_subset_mask N (L+E+1) Y mask hx)
      have hc : x+L ≤ C := by
        have hb := Finset.mem_Ico.mp hxb
        unfold dyadicCutoff at hC
        omega
      have ha := finiteUniformAverage_mono (fun sigma : SmallSample C Y =>
        sum_conditioned_signed_probability_le_base C L E Y x sigma hL)
      have he := average_conditioned_base_start_probability Y hxb hc
      change finiteUniformAverage (fun sigma : SmallSample C Y => eventProbability (largeUniformPMF C Y)
        (fun eta => StartEvent (valueBit (assemble C Y sigma eta)) x L)) = _ at he
      rwa [he] at ha
    _ ≤ (1/(2 : ℝ)^L) * ((fullDefectMass L (fullBadMask N (L+E+1) Y mask) : ℝ) +
        (fullBadMask N (L+E+1) Y mask).card) := by
      have hh := startProbabilityMass_le_mask_defects hN (by omega : 0 < L)
        (fullBadMask N (L+E+1) Y mask) (fun x hx => hmask (fullBadMask_subset_mask N (L+E+1) Y mask hx))
      have hh' := (Rat.cast_le (K := ℝ)).mpr hh
      push_cast at hh'
      simpa only [one_div,div_eq_mul_inv,mul_comm,one_mul] using hh'
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hh : (fullDefectMass L (fullBadMask N (L+E+1) Y mask) : ℝ) ≤ fullDefectMass L mask := by
        exact_mod_cast fullDefectMass_mono (L := L) (fullBadMask_subset_mask N (L+E+1) Y mask)
      linarith

/-- The full signed law with only the actual maximal graph costs left to estimate. -/
theorem average_signed_field_le_deletion_and_graph (hAGG : ProcessAGGStatement)
    {C N L E Y : ℕ} (hN : 2 ≤ N) (hL : 1 ≤ L) (hC : dyadicCutoff N (L+E+1) ≤ C)
    (hY : L+E+2 ≤ Y) (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N) :
    finiteUniformAverage (fun sigma : SmallSample C Y =>
      massTotalVariation (finiteFieldLaw (largeUniformPMF C Y)
        (indicatorField (maskedLabelledFamily N (conditionedSignedAt C L E Y sigma) mask)))
        (poissonFieldMass (allSignedRates N L E mask))) ≤
      (1/(2 : ℝ)^L) * ((fullDefectMass L mask : ℝ) + 2*(fullBadMask N (L+E+1) Y mask).card) +
      2*finiteUniformAverage (fun sigma : SmallSample C Y =>
        bOne (largeUniformPMF C Y)
          (maskedLabelledFamily N (conditionedSignedAt C L E Y sigma) (fullGoodMask N (L+E+1) Y mask))
          (labelledGraph N (L+E+1) Y (Fin (E+1) × F₂)) +
        bTwo (largeUniformPMF C Y)
          (maskedLabelledFamily N (conditionedSignedAt C L E Y sigma) (fullGoodMask N (L+E+1) Y mask))
          (labelledGraph N (L+E+1) Y (Fin (E+1) × F₂))) := by
  have h := finiteUniformAverage_mono (fun sigma =>
    signed_field_process_with_deletion hAGG hN hL hC hY mask hmask sigma)
  have hav {ι : Type} [Fintype ι] [Nonempty ι] (f g : ι → ℝ) (c : ℝ) :
      finiteUniformAverage (fun i => f i + 2*g i + c) =
        finiteUniformAverage f + 2*finiteUniformAverage g + c := by
    unfold finiteUniformAverage
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib,← Finset.mul_sum]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp
  rw [hav] at h
  have hd := average_bad_signed_mass_le (Y := Y) hN hL hC mask hmask
  linarith

end
end PaperC.V282.ExactMarkedDeletion
