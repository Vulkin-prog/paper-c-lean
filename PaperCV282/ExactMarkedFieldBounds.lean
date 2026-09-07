import PaperCV282.ExactMarkedDeletion
import PaperCV282.ExactMarkedFirstCost
import PaperCV282.ExactMarkedPairCosts
import PaperCV282.ExactMarkedLedger
import PaperCV282.ExactMarkedInfinite

/-!
# Equation (5.13) for the actual signed exact-mark field

All constants are absolute and no factor depends on the number of labels.
The cutoff C covers the entire field and may also cover all primes up to Y.
-/
namespace PaperC.V282.ExactMarkedFieldBounds

open ExactMarkedModel ExactMarkedDependency ExactMarkedFieldTransfer ExactMarkedDeletion
open ExactMarkedFirstCost ExactMarkedPairCosts ExactMarkedLedger ExactMarkedInfinite
open LabelledSupportGraph LabelledProcessCosts MaskedArithmeticGeometry MaskedPairGeometry
open ArratiaGoldsteinGordonInput ConditionalStartProbability ConditionalAGGInstantiation
open ConditionalAGGAverage SectionThirteenFiniteBound SectionTwelveMoments TwoWindowParity
open FiniteFieldTotalVariation FiniteFieldPoissonCoupling ProcessAGGInput InfiniteRademacher
open InfiniteCylinderTransfer InfiniteConditionalWords
open scoped BigOperators

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

/-- The average distance of true source conditional atom ratios. -/
def exactSignedConditionalDistance (C N L E Y : ℕ) (mask : Finset ℕ) : ℝ :=
  finiteUniformAverage (fun sigma : SmallSample C Y =>
    massTotalVariation (sourceConditionalSignedLaw C N L E Y mask sigma)
      (poissonFieldMass (allSignedRates N L E mask)))

/-- The distance of the actual infinite signed field law. -/
def exactSignedDistance (N L E : ℕ) (mask : Finset ℕ) : ℝ :=
  massTotalVariation (infiniteSignedLaw N L E mask) (poissonFieldMass (allSignedRates N L E mask))

theorem exactSignedConditionalDistance_nonneg (C N L E Y : ℕ) (mask : Finset ℕ) :
    0 ≤ exactSignedConditionalDistance C N L E Y mask := by
  unfold exactSignedConditionalDistance finiteUniformAverage
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => massTotalVariation_nonneg _ _)) (Nat.cast_nonneg _)

theorem exactSignedDistance_nonneg (N L E : ℕ) (mask : Finset ℕ) :
    0 ≤ exactSignedDistance N L E mask := by
  exact massTotalVariation_nonneg _ _

/-- Full finite process estimate, with the base R2 and maximal-support deletion. -/
theorem finite_signed_field_le_ledger (hAGG : ProcessAGGStatement)
    {C N L E Y : ℕ} (hN : 2 ≤ N) (hL : 1 ≤ L) (hC : dyadicCutoff N (L+E+1) ≤ C)
    (hY : 2*(L+E+2) ≤ Y) (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N) :
    finiteUniformAverage (fun sigma : SmallSample C Y =>
      massTotalVariation (finiteFieldLaw (largeUniformPMF C Y)
        (indicatorField (maskedLabelledFamily N (conditionedSignedAt C L E Y sigma) mask)))
        (poissonFieldMass (allSignedRates N L E mask))) ≤ exactMarkedLedger N L E Y mask := by
  have h := average_signed_field_le_deletion_and_graph (E := E) hAGG hN hL hC (by omega : L+E+2 ≤ Y) mask hmask
  have ha := average_bOne_signed_le (E := E) hN hL hC (by omega : L+E+2 ≤ Y) mask hmask
  have hb := average_bTwo_signed_le (E := E) hN hL hC hY mask hmask
  have hadd (f g : SmallSample C Y → ℝ) :
      finiteUniformAverage (fun sigma => f sigma+g sigma) = finiteUniformAverage f+finiteUniformAverage g := by
    unfold finiteUniformAverage
    rw [Finset.sum_add_distrib,add_div]
  rw [hadd] at h
  have hp : (2 : ℝ)^(2*L) = ((2 : ℝ)^L)^2 := by rw [mul_comm 2 L,pow_mul]
  rw [hp] at hb
  have hden : (1/(2 : ℝ)^L)^2 = 1/((2 : ℝ)^L)^2 := by ring
  rw [div_eq_mul_one_div,← hden] at hb
  unfold exactMarkedLedger
  nlinarith

/-- Equation (5.13) applies to the true conditional source ratios and the unconditional law. -/
theorem signed_source_field_le_ledger (hAGG : ProcessAGGStatement)
    {C N L E Y : ℕ} (hN : 2 ≤ N) (hL : 1 ≤ L) (hC : dyadicCutoff N (L+E+1) ≤ C)
    (hY : 2*(L+E+2) ≤ Y) (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N) :
    exactSignedConditionalDistance C N L E Y mask ≤ exactMarkedLedger N L E Y mask ∧
      exactSignedDistance N L E mask ≤ exactMarkedLedger N L E Y mask := by
  have hf := finite_signed_field_le_ledger hAGG hN hL hC hY mask hmask
  have hc : exactSignedConditionalDistance C N L E Y mask ≤ exactMarkedLedger N L E Y mask := by
    unfold exactSignedConditionalDistance
    rw [average_signed_source_ratio_eq hC]
    exact hf
  exact ⟨hc,(infiniteSignedLaw_distance_le_average Y hC mask (allSignedRates N L E mask)).trans hc⟩

/-- The free cutoff can always represent the full F_Y as well as the complete marked field. -/
theorem signed_field_fullFY_bound (hAGG : ProcessAGGStatement)
    {N L E Y : ℕ} (hN : 2 ≤ N) (hL : 1 ≤ L) (hY : 2*(L+E+2) ≤ Y)
    (mask : Finset ℕ) (hmask : mask ⊆ dyadicBlock N) :
    smallPrimeSigmaAlgebra (max Y (dyadicCutoff N (L+E+1))) Y =
      MeasurableSpace.comap (restrictToFinite Y) inferInstance ∧
    exactSignedConditionalDistance (max Y (dyadicCutoff N (L+E+1))) N L E Y mask ≤ exactMarkedLedger N L E Y mask ∧
    exactSignedDistance N L E mask ≤ exactMarkedLedger N L E Y mask := by
  exact ⟨smallPrimeSigmaAlgebra_eq_primeCylinder (le_max_left _ _),
    signed_source_field_le_ledger hAGG hN hL (le_max_right _ _) hY mask hmask⟩

end
end PaperC.V282.ExactMarkedFieldBounds
