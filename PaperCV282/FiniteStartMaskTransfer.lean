import PaperCV282.FiniteStartMaskSteinCosts
import PaperCV282.FiniteStartMaskDeletion

/-! # Sharp scalar transfer on arbitrary actual finite masks -/
namespace PaperC.V282.FiniteStartMaskTransfer

open Affine ArratiaGoldsteinGordonInput ConditionalAGGInstantiation ConditionalAGGAverage
open ConditionalStartProbability SectionThirteenFiniteBound ScalarSteinInput ScalarPoissonBounds
open FiniteStartMaskModel FiniteStartMaskAverages FiniteStartMaskSteinCosts FiniteStartMaskDeletion
open MacroscopicMaskGeometry MaskedArithmeticGeometry MaskedPairGeometry LargePrimeDependencyGraph
open HostRankMass TwoWindowParity
open scoped BigOperators NNReal

noncomputable section

theorem average_good_costs_le {C L Y : ℕ} (mask : Finset ℕ)
    (hL : 0<L) (hY : 2*L≤Y) (hpos : ∀ x∈mask,2≤x) (hcut : ∀ x∈mask,x+L≤C) :
    finiteUniformAverage (fun sigma : SmallSample C Y =>
      bOne (largeUniformPMF C Y) (conditionedIndicator C L Y (goodMask L Y mask) sigma)
        (startMaskGraph L Y (goodMask L Y mask)) +
      bTwo (largeUniformPMF C Y) (conditionedIndicator C L Y (goodMask L Y mask) sigma)
        (startMaskGraph L Y (goodMask L Y mask))) ≤
      2*(((mask.card : ℝ)+(maskedSupportEdges L Y mask).card+
        (relationWeightMass C L (separatedPairs mask L) : ℝ))/(2 : ℝ)^(2*L)) := by
  have hgood (x : ℕ) (hx : x∈goodMask L Y mask) (i : Fin L) :
      ¬DefectivePredicate.HDefective Y (x+i.val) :=
    not_defective_of_good hx (mem_startTreeSupport.mpr (Or.inr ⟨i.val,i.isLt,rfl⟩))
  simp_rw [bOne_eq (goodMask L Y mask) hL (by omega : L+1≤Y)
    (fun x hx => hpos x (goodMask_subset L Y mask hx))
    (fun x hx => hcut x (goodMask_subset L Y mask hx)) hgood]
  have havg (c : ℝ) (f : SmallSample C Y → ℝ) :
      finiteUniformAverage (fun sigma => c+f sigma)=c+finiteUniformAverage f := by
    unfold finiteUniformAverage
    rw [Finset.sum_add_distrib,add_div]
    simp
  rw [havg]
  have htwo := average_bTwo_good_le mask hL hY hpos hcut
  have hone : (((goodMask L Y mask).card : ℝ)+(maskedSupportEdges L Y (goodMask L Y mask)).card) /
      (2 : ℝ)^(2*L) ≤ ((mask.card : ℝ)+(maskedSupportEdges L Y mask).card)/(2 : ℝ)^(2*L) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact add_le_add (by exact_mod_cast Finset.card_le_card (goodMask_subset L Y mask))
      (by exact_mod_cast Finset.card_le_card (goodEdges_subset_support L Y mask))
  apply (add_le_add hone htwo).trans
  have hcard : (0 : ℝ) ≤ mask.card := by positivity
  have hrel : (0 : ℝ) ≤ relationWeightMass C L (separatedPairs mask L) := by positivity
  have hp : (0 : ℝ)<2^(2*L) := by positivity
  field_simp
  nlinarith

theorem retained_scalar_tv_le (hStein : ScalarSteinFactorsStatement) {C L Y : ℕ}
    (mask : Finset ℕ) (hL : 0<L) (hY : 2*L≤Y)
    (hpos : ∀ x∈mask,2≤x) (hcut : ∀ x∈mask,x+L≤C) :
    natTotalVariation (finiteLaw C L (goodMask L Y mask))
      (poissonMass (maskRate L (goodMask L Y mask))) ≤
      2*firstSteinFactor (maskRate L (goodMask L Y mask))*
        (((mask.card : ℝ)+(maskedSupportEdges L Y mask).card+
          (relationWeightMass C L (separatedPairs mask L) : ℝ))/(2 : ℝ)^(2*L)) := by
  apply (finite_tv_le_average C L Y (goodMask L Y mask) _).trans
  have hpoint := finiteUniformAverage_mono (fun sigma : SmallSample C Y =>
    good_scalar_bound hStein (goodMask L Y mask) hL (by omega : L+1≤Y)
      (fun x hx => hpos x (goodMask_subset L Y mask hx))
      (fun x hx => hcut x (goodMask_subset L Y mask hx))
      (fun x hx i => not_defective_of_good hx (mem_startTreeSupport.mpr (Or.inr ⟨i.val,i.isLt,rfl⟩))) sigma)
  have hmul (c : ℝ) (f : SmallSample C Y → ℝ) :
      finiteUniformAverage (fun sigma => c*f sigma)=c*finiteUniformAverage f := by
    unfold finiteUniformAverage
    rw [← Finset.mul_sum]
    ring
  rw [hmul] at hpoint
  apply (hpoint.trans (mul_le_mul_of_nonneg_left
    (average_good_costs_le mask hL hY hpos hcut) (firstSteinFactor_nonneg _))).trans_eq
  ring

/-- The complete finite scalar comparison with its true retained mean and arithmetic costs. -/
theorem finite_scalar_tv_le (hStein : ScalarSteinFactorsStatement) {C L Y : ℕ}
    (mask : Finset ℕ) (hL : 0<L) (hY : 2*L≤Y)
    (hpos : ∀ x∈mask,2≤x) (hcut : ∀ x∈mask,x+L≤C) :
    natTotalVariation (finiteLaw C L mask) (poissonMass (maskRate L mask)) ≤
      ((fullDefectMass L mask : ℝ)+2*(badMask L Y mask).card)/(2 : ℝ)^L +
      2*firstSteinFactor (maskRate L (goodMask L Y mask))*
        (((mask.card : ℝ)+(maskedSupportEdges L Y mask).card+
          (relationWeightMass C L (separatedPairs mask L) : ℝ))/(2 : ℝ)^(2*L)) := by
  have hfirst := natTotalVariation_triangle
    (p := finiteLaw C L mask) (q := finiteLaw C L (goodMask L Y mask))
    (r := poissonMass (maskRate L mask))
    (summable_finiteNatLaw _ _) (summable_finiteNatLaw _ _) (hasSum_poissonMass _).summable
    (finiteNatLaw_nonneg _ _) (finiteNatLaw_nonneg _ _) (poissonMass_nonneg _)
  have hsecond := natTotalVariation_triangle
    (p := finiteLaw C L (goodMask L Y mask)) (q := poissonMass (maskRate L (goodMask L Y mask)))
    (r := poissonMass (maskRate L mask))
    (summable_finiteNatLaw _ _) (hasSum_poissonMass _).summable (hasSum_poissonMass _).summable
    (finiteNatLaw_nonneg _ _) (poissonMass_nonneg _) (poissonMass_nonneg _)
  have hbad := finiteLaw_good_tv_le (Y := Y) mask hL hpos hcut
  have hret := retained_scalar_tv_le hStein mask hL hY hpos hcut
  have hshift := good_poisson_tv_le L Y mask
  have he : ((fullDefectMass L mask : ℝ)+2*(badMask L Y mask).card)/(2 : ℝ)^L =
      ((fullDefectMass L mask : ℝ)+(badMask L Y mask).card)/(2 : ℝ)^L +
        (badMask L Y mask).card/(2 : ℝ)^L := by ring
  rw [he]
  linarith

end
end PaperC.V282.FiniteStartMaskTransfer
