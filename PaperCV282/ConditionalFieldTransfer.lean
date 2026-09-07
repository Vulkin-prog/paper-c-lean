import PaperCV282.ProcessAGGInput
import PaperCV282.AllStartConditionalDependency
import PaperCV282.MaskedArithmeticCosts

/-!
# The actual retained conditional field and its arithmetic process cost

The field is indexed by the historical good-start carrier and is set to zero
outside the literal full-support good mask. Its Poisson coordinates have
exactly the same retained baseline rates. The mean b1+b2 is bounded by the
proved masked arithmetic costs, without an intensity-dependent scalar factor.
The extension to the all-site carrier is treated below by reindexing.
-/

namespace PaperC.V282.ConditionalFieldTransfer

open ArratiaGoldsteinGordonInput ConditionalStartProbability ConditionalDependencyGraph
open ConditionalAGGInstantiation ConditionalAGGAverage MaskedPoissonCritical
open LargePrimeDependencyGraph SectionTwelveMoments SectionThirteenFiniteBound
open MaskedArithmeticGeometry MaskedArithmeticCosts MaskedPairGeometry TwoWindowParity
open FiniteFieldTotalVariation FiniteFieldPoissonCoupling ProcessAGGInput
open scoped BigOperators NNReal

noncomputable section

def retainedGoodFieldRates (N L Y : ℕ) (mask : Finset ℕ)
    (x : {x : ℕ // x ∈ goodStarts N L Y}) : ℝ≥0 := by
  classical
  exact if x.val ∈ fullGoodMask N L Y mask then ⟨1 / (2 : ℝ) ^ L, by positivity⟩ else 0

theorem fieldRates_maskedGood_eq {N L Y : ℕ} (mask : Finset ℕ)
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (sigma : SmallSample (dyadicCutoff N L) Y) :
    fieldRates (largeUniformPMF (dyadicCutoff N L) Y)
      (maskedConditionedGoodIndicator N L Y (fullGoodMask N L Y mask) sigma) =
        retainedGoodFieldRates N L Y mask := by
  classical
  funext x
  apply Subtype.ext
  change marginal (largeUniformPMF (dyadicCutoff N L) Y)
    (maskedConditionedGoodIndicator N L Y (fullGoodMask N L Y mask) sigma) x = _
  rw [marginal_maskedConditionedGoodIndicator (fullGoodMask N L Y mask) hN hL hLY sigma]
  by_cases hx : x.val ∈ fullGoodMask N L Y mask <;> simp [retainedGoodFieldRates, hx]
  rfl

theorem retained_conditional_field_process_bound (hAGG : ProcessAGGStatement)
    {N L Y : ℕ} (mask : Finset ℕ)
    (hN : 2 ≤ N) (hL : 0 < L) (hLY : L + 1 ≤ Y)
    (sigma : SmallSample (dyadicCutoff N L) Y) :
    massTotalVariation
      (finiteFieldLaw (largeUniformPMF (dyadicCutoff N L) Y)
        (indicatorField (maskedConditionedGoodIndicator N L Y (fullGoodMask N L Y mask) sigma)))
      (poissonFieldMass (retainedGoodFieldRates N L Y mask)) ≤
        2 * (bOne (largeUniformPMF (dyadicCutoff N L) Y)
          (maskedConditionedGoodIndicator N L Y (fullGoodMask N L Y mask) sigma)
          (largePrimeDependencyGraph N L Y) +
        bTwo (largeUniformPMF (dyadicCutoff N L) Y)
          (maskedConditionedGoodIndicator N L Y (fullGoodMask N L Y mask) sigma)
          (largePrimeDependencyGraph N L Y)) := by
  have h := process_totalVariation_le hAGG (largeUniformPMF (dyadicCutoff N L) Y)
    (maskedConditionedGoodIndicator N L Y (fullGoodMask N L Y mask) sigma)
    (largePrimeDependencyGraph N L Y)
    (hasExactDependencyGraph_maskedConditionedGoodIndicator (fullGoodMask N L Y mask) hL sigma)
  rw [fieldRates_maskedGood_eq mask hN hL hLY sigma] at h
  exact h

theorem average_retained_conditional_field_le_arithmetic (hAGG : ProcessAGGStatement)
    {N L Y : ℕ} (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N)
    (hN : 2 ≤ N) (hL : 0 < L) (hY : 2 * L ≤ Y) :
    finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
      massTotalVariation
        (finiteFieldLaw (largeUniformPMF (dyadicCutoff N L) Y)
          (indicatorField (maskedConditionedGoodIndicator N L Y (fullGoodMask N L Y mask) sigma)))
        (poissonFieldMass (retainedGoodFieldRates N L Y mask))) ≤
      2 * (((mask.card : ℝ) + 2 * (maskedSupportEdges L Y mask).card +
        (jointDefectMass N L (separatedPairs mask L) : ℝ)) / (2 : ℝ) ^ (2 * L)) := by
  have hLY : L + 1 ≤ Y := by omega
  have hbound := finiteUniformAverage_mono
    (fun sigma => retained_conditional_field_process_bound hAGG (N := N) (L := L) (Y := Y) mask hN hL hLY sigma)
  have havg := average_stein_terms_le mask hmask hN hL hY
  have hscale (f : SmallSample (dyadicCutoff N L) Y → ℝ) :
      finiteUniformAverage (fun sigma => 2 * f sigma) = 2 * finiteUniformAverage f := by
    unfold finiteUniformAverage
    rw [← Finset.mul_sum]
    ring
  rw [hscale] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_left havg (by norm_num))

theorem mixed_retained_field_le_arithmetic (hAGG : ProcessAGGStatement)
    {N L Y : ℕ} (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N)
    (hN : 2 ≤ N) (hL : 0 < L) (hY : 2 * L ≤ Y) :
    massTotalVariation
      (fun k => uniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
        finiteFieldLaw (largeUniformPMF (dyadicCutoff N L) Y)
          (indicatorField (maskedConditionedGoodIndicator N L Y (fullGoodMask N L Y mask) sigma)) k))
      (poissonFieldMass (retainedGoodFieldRates N L Y mask)) ≤
      2 * (((mask.card : ℝ) + 2 * (maskedSupportEdges L Y mask).card +
        (jointDefectMass N L (separatedPairs mask L) : ℝ)) / (2 : ℝ) ^ (2 * L)) := by
  have hmix := massTotalVariation_uniformMixture_le
    (fun sigma : SmallSample (dyadicCutoff N L) Y =>
      finiteFieldLaw (largeUniformPMF (dyadicCutoff N L) Y)
        (indicatorField (maskedConditionedGoodIndicator N L Y (fullGoodMask N L Y mask) sigma)))
    (poissonFieldMass (retainedGoodFieldRates N L Y mask))
    (fun sigma => FiniteFieldTotalVariation.summable_abs_sub_of_nonneg
      (summable_finiteFieldLaw _ _) (summable_poissonFieldMass _)
      (finiteFieldLaw_nonneg _ _) (poissonFieldMass_nonneg _))
  exact hmix.trans (average_retained_conditional_field_le_arithmetic hAGG mask hmask hN hL hY)

end

end PaperC.V282.ConditionalFieldTransfer
