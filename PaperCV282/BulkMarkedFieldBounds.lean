import PaperCV282.BulkMarkedDeletion
import PaperCV282.BulkMarkedFirstCost
import PaperCV282.BulkMarkedSeparatedCosts
import PaperCV282.BulkMarkedInfinite

/-!
# Equation (5.13) for the actual signed exact-mark field

All constants are absolute and no factor depends on the number of labels.
The cutoff C covers the entire field and may also cover all primes up to Y.
-/
namespace PaperC.V282.BulkMarkedFieldBounds

open ExactMarkedModel ExactMarkedDependency BulkMarkedTransfer BulkMarkedDeletion
open BulkMarkedFirstCost BulkMarkedSeparatedCosts BulkMarkedInfinite HostRankMass MacroscopicMaskGeometry
open BulkSupportGraph BulkProcessCosts MaskedArithmeticGeometry MaskedPairGeometry
open ArratiaGoldsteinGordonInput ConditionalStartProbability ConditionalAGGInstantiation
open ConditionalAGGAverage SectionThirteenFiniteBound SectionTwelveMoments TwoWindowParity
open FiniteFieldTotalVariation FiniteFieldPoissonCoupling ProcessAGGInput InfiniteRademacher
open InfiniteCylinderTransfer InfiniteConditionalWords
open scoped BigOperators

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

/-- Defect and relation masses use the base L; the graph and deletion use L+E+1. -/
def exactMarkedLedger (C : ℕ) (sites : Finset ℕ) (L E Y : ℕ) (mask : Finset ℕ) : ℝ :=
  (1/(2 : ℝ)^L) * ((fullDefectMass L mask : ℝ) + 2*(badMask (L+E+1) Y mask).card) +
  (1/(2 : ℝ)^L)^2 * (20*(sites.card : ℝ)*(L+E+2) + 4*(maskedSupportEdges (L+E+1) Y mask).card +
    2*(relationWeightMass C L (separatedPairs mask L) : ℝ))

theorem exactMarkedLedger_nonneg (C : ℕ) (sites : Finset ℕ) (L E Y : ℕ) (mask : Finset ℕ) :
    0 ≤ exactMarkedLedger C sites L E Y mask := by unfold exactMarkedLedger; positivity

/-- The average distance of true source conditional atom ratios. -/
def exactSignedConditionalDistance (C : ℕ) (sites : Finset ℕ) (L E Y : ℕ) (mask : Finset ℕ) : ℝ :=
  finiteUniformAverage (fun sigma : SmallSample C Y =>
    massTotalVariation (sourceConditionalSignedLaw C sites L E Y mask sigma)
      (poissonFieldMass (allSignedRates sites L E mask)))

/-- The distance of the actual infinite signed field law. -/
def exactSignedDistance (sites : Finset ℕ) (L E : ℕ) (mask : Finset ℕ) : ℝ :=
  massTotalVariation (infiniteSignedLaw sites L E mask) (poissonFieldMass (allSignedRates sites L E mask))

theorem exactSignedConditionalDistance_nonneg (C : ℕ) (sites : Finset ℕ) (L E Y : ℕ) (mask : Finset ℕ) :
    0 ≤ exactSignedConditionalDistance C sites L E Y mask := by
  unfold exactSignedConditionalDistance finiteUniformAverage
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => massTotalVariation_nonneg _ _)) (Nat.cast_nonneg _)

theorem exactSignedDistance_nonneg (sites : Finset ℕ) (L E : ℕ) (mask : Finset ℕ) :
    0 ≤ exactSignedDistance sites L E mask := by
  exact massTotalVariation_nonneg _ _

/-- Full finite process estimate, with the base R2 and maximal-support deletion. -/
theorem finite_signed_field_le_ledger (hAGG : ProcessAGGStatement)
    {C L E Y : ℕ} {sites : Finset ℕ} (hsite : ∀ x ∈ sites, 2 ≤ x) (hL : 1 ≤ L) (hC : ∀ x ∈ sites, x+L+E+1 ≤ C)
    (hY : 2*(L+E+2) ≤ Y) (mask : Finset ℕ) (hmask : mask ⊆ sites) :
    finiteUniformAverage (fun sigma : SmallSample C Y =>
      massTotalVariation (finiteFieldLaw (largeUniformPMF C Y)
        (indicatorField (maskedLabelledFamily sites (conditionedSignedAt C L E Y sigma) mask)))
        (poissonFieldMass (allSignedRates sites L E mask))) ≤ exactMarkedLedger C sites L E Y mask := by
  have h := average_signed_field_le_deletion_and_graph (E := E) hAGG hsite hL hC (by omega : L+E+2 ≤ Y) mask hmask
  have ha := average_bOne_signed_le (E := E) hsite hL hC (by omega : L+E+2 ≤ Y) mask hmask
  have hb := average_bTwo_signed_le (E := E) hsite hL hC hY mask hmask
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
    {C L E Y : ℕ} {sites : Finset ℕ} (hsite : ∀ x ∈ sites, 2 ≤ x) (hL : 1 ≤ L) (hC : ∀ x ∈ sites, x+L+E+1 ≤ C)
    (hY : 2*(L+E+2) ≤ Y) (mask : Finset ℕ) (hmask : mask ⊆ sites) :
    exactSignedConditionalDistance C sites L E Y mask ≤ exactMarkedLedger C sites L E Y mask ∧
      exactSignedDistance sites L E mask ≤ exactMarkedLedger C sites L E Y mask := by
  have hf := finite_signed_field_le_ledger hAGG hsite hL hC hY mask hmask
  have hc : exactSignedConditionalDistance C sites L E Y mask ≤ exactMarkedLedger C sites L E Y mask := by
    unfold exactSignedConditionalDistance
    rw [average_signed_source_ratio_eq hC]
    exact hf
  exact ⟨hc,(infiniteSignedLaw_distance_le_average Y hC mask (allSignedRates sites L E mask)).trans hc⟩

end
end PaperC.V282.BulkMarkedFieldBounds
