import PaperCV282.DictionaryFieldFirstCost
import PaperCV282.DictionaryFieldSecondCost
import PaperCV282.DictionaryErrorLedger

/-!
# Equation (5.7) for the true conditional site-and-word field

The process premise is applied to the explicitly constructed dependency graph.
Every term in the ledger comes from actual deletion, local compatibility, or the
full-value marginal cap on separated retained graph pairs.
-/
namespace PaperC.V282.DictionaryFieldBounds

open Affine ConditionalStartProbability ConditionalAGGInstantiation ConditionalAGGAverage
open ArratiaGoldsteinGordonInput SectionTwelveMoments SectionThirteenFiniteBound
open DictionaryFieldModel DictionaryFieldDependency DictionaryFieldTransfer DictionaryFieldDeletion
open DictionaryFieldFirstCost DictionaryFieldSecondCost DictionaryErrorLedger
open MaskedArithmeticGeometry MaskedPairGeometry CappedRelationMass TwoWindowParity
open FiniteFieldTotalVariation FiniteFieldPoissonCoupling ProcessAGGInput WordOverlapSum
open scoped BigOperators NNReal

noncomputable section

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- The explicit finite process estimate is uniform in every deterministic site mask. -/
theorem average_dictionary_field_le_arithmetic (hAGG : ProcessAGGStatement)
    {N L Y : ℕ} (W : Finset (Fin (L + 1) → F₂)) (hW : W.Nonempty)
    (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N)
    (hN : 2 ≤ N) (hY : 2 * (L + 1) ≤ Y) :
    finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
      massTotalVariation
        (finiteFieldLaw (largeUniformPMF (dyadicCutoff N L) Y)
          (indicatorField (maskedWordIndicator N L Y W mask sigma)))
        (poissonFieldMass (allWordRates N L W mask))) ≤
      (dictionaryRate L W : ℝ) * ((fullDefectMass L mask : ℝ) + 2 * (fullBadMask N L Y mask).card) +
      4 * (dictionaryRate L W : ℝ)^2 *
        ((N : ℝ) * (L + 1 : ℝ) + ((maskedSupportEdges L Y mask).card : ℝ) +
          cappedValueMass (dyadicCutoff N L) L (1 / (dictionaryRate L W : ℝ)) (separatedPairs mask L)) +
      4 * ((N : ℝ) * (dictionaryRate L W : ℝ)) * overlapWeight W := by
  have hLY : L + 1 ≤ Y := by omega
  have h := average_dictionary_field_le_deletion_and_graph hAGG W mask hmask hN hLY
  have hav (f g : SmallSample (dyadicCutoff N L) Y → ℝ) :
      finiteUniformAverage (fun sigma => f sigma + g sigma) =
        finiteUniformAverage f + finiteUniformAverage g := by
    unfold finiteUniformAverage
    rw [Finset.sum_add_distrib,add_div]
  rw [hav] at h
  have hOne := finiteUniformAverage_mono (fun sigma => bOne_dictionary_le W mask hmask hN hLY sigma)
  have hOne' : finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
      bOne (largeUniformPMF (dyadicCutoff N L) Y)
        (maskedWordIndicator N L Y W (fullGoodMask N L Y mask) sigma) (dictionaryGraph N L Y W)) ≤
      (dictionaryRate L W : ℝ)^2 * (2 * (N : ℝ) * (L + 1 : ℝ) +
        ((maskedSupportEdges L Y mask).card : ℝ)) := by
    simpa [finiteUniformAverage] using hOne
  have hTwo := average_bTwo_dictionary_le W hW mask hmask hN hY
  have hR := cappedValueMass_nonneg (dyadicCutoff N L) L
    (show 0 ≤ 1 / (dictionaryRate L W : ℝ) by positivity) (separatedPairs mask L)
  nlinarith [mul_nonneg (sq_nonneg (dictionaryRate L W : ℝ)) hR]

/-- Equation (5.7), on the literal full dyadic field and the exact arithmetic ledger. -/
theorem equation_five_seven (hAGG : ProcessAGGStatement)
    {N L Y : ℕ} (W : Finset (Fin (L + 1) → F₂)) (hW : W.Nonempty)
    (hN : 2 ≤ N) (hY : 2 * (L + 1) ≤ Y) :
    finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
      massTotalVariation
        (finiteFieldLaw (largeUniformPMF (dyadicCutoff N L) Y)
          (indicatorField (maskedWordIndicator N L Y W (dyadicBlock N) sigma)))
        (poissonFieldMass (allWordRates N L W (dyadicBlock N)))) ≤
      dictionaryArithmeticLedger N L Y (dictionaryRate L W : ℝ) (overlapWeight W) := by
  have h := average_dictionary_field_le_arithmetic hAGG W hW (dyadicBlock N) (fun _ h => h) hN hY
  have hbad : fullBadMask N L Y (dyadicBlock N) = fullBadStarts N L Y := by
    ext x
    simp only [mem_fullBadMask]
    exact ⟨And.right,fun hx => ⟨fullBadStarts_subset_block N L Y hx,hx⟩⟩
  simpa only [hbad,dictionaryArithmeticLedger] using h

end
end PaperC.V282.DictionaryFieldBounds
