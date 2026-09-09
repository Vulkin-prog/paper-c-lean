import PaperCV282.MacroAggregateCosts
import PaperCV282.SignedDirectionalFactors
import PaperCV282.MacroAggregateModel
import PaperCV282.BulkMarkedDeletion
import PaperCV282.DirectionalPoissonComparison
import PaperCV282.FiniteStartMaskAverages

/-! # Filling the genuinely deleted signed categories to their full target rates -/
namespace PaperC.V282.MacroAggregateFilling

open Affine MacroAggregateModel SignedDirectionalFactors SignedGeometricWeights
open ExactMarkedModel ExactMarkedDependency BulkMarkedTransfer BulkMarkedDeletion BulkMarkedDependency MacroscopicMaskGeometry
open BulkSupportGraph BulkProcessCosts MacroAggregateCosts
open DirectionalSteinComparison DirectionalSteinIntegration DirectionalPoissonComparison
open DirectionalSteinInput DirectionalHessian PoissonFilling ProcessAGGInput
open ConditionalStartProbability ConditionalAGGInstantiation ArratiaGoldsteinGordonInput
open SectionThirteenFiniteBound SectionTwelveMoments MaskedArithmeticGeometry MaskedPairGeometry
open FiniteFieldTotalVariation FiniteFieldPoissonCoupling MassPushforward FiniteStartMaskAverages
open scoped BigOperators NNReal

noncomputable section

local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- Independent Poisson replacement at the exact missing rate of each excess/sign category. -/
def badSignedFillRates (sites : Finset ℕ) (L E Y : ℕ) : Fin (E+1) × F₂ → ℝ≥0 :=
  fun a => ((badMask (L+E+1) Y (sites)).card : ℝ≥0)*signedMarkRate L a.1.val

/-- Actual category means in the retained conditional field. -/
theorem categoryRate_signed_good_eq {C L E Y : ℕ} {sites : Finset ℕ}
    (hsite : ∀ x ∈ sites, 2 ≤ x) (hL : 1 ≤ L) (hC : ∀ x ∈ sites, x+L+E+1 ≤ C)
    (hY : L+E+2 ≤ Y) (sigma : SmallSample C Y) (a : Fin (E+1) × F₂) :
    categoryRate (largeUniformPMF C Y)
      (maskedLabelledFamily sites (conditionedSignedAt C L E Y sigma)
        (goodMask (L+E+1) Y (sites))) Prod.snd a =
      ((goodMask (L+E+1) Y (sites)).card : ℝ≥0)*signedMarkRate L a.1.val := by
  apply NNReal.eq
  change (∑ i : LabelledIndex sites (Fin (E+1) × F₂), if i.2=a then marginal _ _ i else 0) = _
  simp_rw [signedAt_marginal_masked_good hsite hL hC hY]
  rw [sum_labelledIndex sites (fun x b => if b=a then
    (if x ∈ goodMask (L+E+1) Y (sites) then (signedMarkRate L b.1.val : ℝ) else 0) else 0)]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [← Finset.sum_filter]
  have heq : (sites).filter (fun x => x ∈ goodMask (L+E+1) Y (sites)) =
      goodMask (L+E+1) Y (sites) := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨And.right,fun h => ⟨goodMask_subset _ _ _ h,h⟩⟩
  rw [heq]
  simp

/-- Filling restores the full target exactly, without a lower bound on the retained population. -/
theorem signed_filling_balance {C L E Y : ℕ} {sites : Finset ℕ}
    (hsite : ∀ x ∈ sites, 2 ≤ x) (hL : 1 ≤ L) (hC : ∀ x ∈ sites, x+L+E+1 ≤ C)
    (hY : L+E+2 ≤ Y) (sigma : SmallSample C Y) (a : Fin (E+1) × F₂) :
    signedAggregateRates (maskRate L sites) E a = badSignedFillRates sites L E Y a+
      categoryRate (largeUniformPMF C Y)
        (maskedLabelledFamily sites (conditionedSignedAt C L E Y sigma)
          (goodMask (L+E+1) Y (sites))) Prod.snd a := by
  rw [categoryRate_signed_good_eq hsite hL hC hY sigma]
  apply NNReal.eq
  rw [signedAggregateRates_coe]
  have hc := card_good_add_bad (L+E+1) Y (sites)
  have hcard : ((goodMask (L+E+1) Y sites).card : ℝ)+
      (badMask (L+E+1) Y sites).card = (sites.card : ℝ) := by exact_mod_cast hc
  simp only [NNReal.coe_add,NNReal.coe_mul,NNReal.coe_natCast,
    badSignedFillRates,signedMarkRate_eq_base_mul_weight,maskRate]
  change (sites.card : ℝ)/2^L*signedGeometricWeight a.1.val = _
  rw [← hcard]
  ring

/-- The complete filling mass is at most the base rate times the deleted-site count. -/
theorem sum_badSignedFillRates_le (sites : Finset ℕ) (L E Y : ℕ) :
    (∑ a, (badSignedFillRates sites L E Y a : ℝ)) ≤
      (1/(2 : ℝ)^L)*(badMask (L+E+1) Y (sites)).card := by
  simp only [badSignedFillRates,NNReal.coe_mul,NNReal.coe_natCast,← Finset.mul_sum]
  have h : (∑ a : Fin (E+1) × F₂, (signedMarkRate L a.1.val : ℝ)) ≤ 1/(2 : ℝ)^L := by
    simpa only [Fintype.sum_prod_type] using sum_all_signedMarkRate_le_base L E
  have hh := mul_le_mul_of_nonneg_left h
    (by positivity : 0 ≤ ((badMask (L+E+1) Y (sites)).card : ℝ))
  simpa only [mul_comm] using hh

/-- Actual Poisson-filled category comparison, using the source-faithful directional input. -/
theorem signed_filled_comparison (hStein : DirectionalSteinFactorsStatement)
    {C L E Y : ℕ} {sites : Finset ℕ} (hne : sites.Nonempty) (hsite : ∀ x ∈ sites, 2 ≤ x) (hL : 1 ≤ L) (hC : ∀ x ∈ sites, x+L+E+1 ≤ C)
    (hY : L+E+2 ≤ Y) (sigma : SmallSample C Y) :
    massTotalVariation (filledLaw (largeUniformPMF C Y)
      (maskedLabelledFamily sites (conditionedSignedAt C L E Y sigma)
        (goodMask (L+E+1) Y (sites))) Prod.snd (badSignedFillRates sites L E Y))
      (poissonFieldMass (signedAggregateRates (maskRate L sites) E)) ≤
    typedCost (largeUniformPMF C Y)
      (maskedLabelledFamily sites (conditionedSignedAt C L E Y sigma)
        (goodMask (L+E+1) Y (sites))) Prod.snd
      (labelledGraph sites (L+E+1) Y (Fin (E+1) × F₂))
      (entryFactor (signedAggregateRates (maskRate L sites) E)) := by
  apply directional_poisson_filling_comparison hStein
  · simp only [Fintype.card_prod,Fintype.card_fin]
    norm_num
  · exact hasExactDependencyGraph_signed hsite hL _ sigma
  · apply signedAggregateRates_pos
    change (0 : ℝ)<(maskRate L sites : ℝ)
    change 0<(sites.card : ℝ)/2^L
    have hc : 0 < sites.card := Finset.card_pos.mpr hne
    positivity
  · exact signed_filling_balance hsite hL hC hY sigma

/-- Deleting actual bad labels and then aggregating cannot enlarge the deletion cost. -/
theorem signed_aggregate_retention_le {C L E Y : ℕ} {sites : Finset ℕ} (sigma : SmallSample C Y) :
    massTotalVariation
      (finiteFieldLaw (largeUniformPMF C Y) (typedSum
        (maskedLabelledFamily sites (conditionedSignedAt C L E Y sigma) (sites)) Prod.snd Finset.univ))
      (finiteFieldLaw (largeUniformPMF C Y) (typedSum
        (maskedLabelledFamily sites (conditionedSignedAt C L E Y sigma)
          (goodMask (L+E+1) Y (sites))) Prod.snd Finset.univ)) ≤
      badSignedMass C L E Y (sites) sigma := by
  let X := maskedLabelledFamily sites (conditionedSignedAt C L E Y sigma) (sites)
  let good := retainedSignedIndices sites L E Y (sites)
  have h := massTotalVariation_retainedField_le_bad_sites (largeUniformPMF C Y) good (indicatorField X)
  simp_rw [eventProbability_indicatorField_active] at h
  rw [← indicatorField_retainedIndicators,retainedIndicators_signed_eq,
    bad_marginal_sum_signed_eq _ (Finset.Subset.refl _)] at h
  have hc := massTotalVariation_pushforward_le (finiteSignedAggregate sites E)
    (hasSum_finiteFieldLaw (largeUniformPMF C Y) (indicatorField X))
    (hasSum_finiteFieldLaw (largeUniformPMF C Y) (indicatorField
      (maskedLabelledFamily sites (conditionedSignedAt C L E Y sigma)
        (goodMask (L+E+1) Y (sites)))))
    (finiteFieldLaw_nonneg _ _) (finiteFieldLaw_nonneg _ _)
  rw [pushforwardMass_finiteFieldLaw,pushforwardMass_finiteFieldLaw] at hc
  have heq (Z : LabelledIndex sites (Fin (E+1) × F₂) → LargeSample C Y → Bool) :
      (fun omega => finiteSignedAggregate sites E (indicatorField Z omega)) = typedSum Z Prod.snd Finset.univ := by
    funext omega
    exact finiteSignedAggregate_indicator sites E Z omega
  rw [heq,heq] at hc
  exact hc.trans h

end
end PaperC.V282.MacroAggregateFilling
