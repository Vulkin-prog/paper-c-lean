import PaperCV282.SignedAggregateArithmetic
import PaperCV282.SignedAggregateConfiguration
import PaperCV282.ExactMarkedDeletion
import PaperCV282.DirectionalPoissonComparison

/-! # Filling the genuinely deleted signed categories to their full target rates -/
namespace PaperC.V282.SignedAggregateFilling

open Affine SignedAggregateArithmetic SignedAggregateConfiguration SignedDirectionalFactors SignedGeometricWeights
open ExactMarkedModel ExactMarkedDependency ExactMarkedFieldTransfer ExactMarkedDeletion
open LabelledSupportGraph LabelledProcessCosts WeightedLabelledCosts DirectionalMarkedCosts
open DirectionalSteinComparison DirectionalSteinIntegration DirectionalPoissonComparison
open DirectionalSteinInput DirectionalHessian PoissonFilling ProcessAGGInput
open ConditionalStartProbability ConditionalAGGInstantiation ArratiaGoldsteinGordonInput
open SectionThirteenFiniteBound SectionTwelveMoments MaskedArithmeticGeometry MaskedPairGeometry
open FiniteFieldTotalVariation FiniteFieldPoissonCoupling MassPushforward AllStartSoftPoisson
open scoped BigOperators NNReal

noncomputable section

local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- Independent Poisson replacement at the exact missing rate of each excess/sign category. -/
def badSignedFillRates (N L E Y : ℕ) : Fin (E+1) × F₂ → ℝ≥0 :=
  fun a => ((fullBadMask N (L+E+1) Y (dyadicBlock N)).card : ℝ≥0)*signedMarkRate L a.1.val

/-- Actual category means in the retained conditional field. -/
theorem categoryRate_signed_good_eq {C N L E Y : ℕ}
    (hN : 2 ≤ N) (hL : 1 ≤ L) (hC : dyadicCutoff N (L+E+1) ≤ C)
    (hY : L+E+2 ≤ Y) (sigma : SmallSample C Y) (a : Fin (E+1) × F₂) :
    categoryRate (largeUniformPMF C Y)
      (maskedLabelledFamily N (conditionedSignedAt C L E Y sigma)
        (fullGoodMask N (L+E+1) Y (dyadicBlock N))) Prod.snd a =
      ((fullGoodMask N (L+E+1) Y (dyadicBlock N)).card : ℝ≥0)*signedMarkRate L a.1.val := by
  apply NNReal.eq
  change (∑ i : SignedMarkIndex N E, if i.2=a then marginal _ _ i else 0) = _
  simp_rw [signedAt_marginal_masked_good hN hL hC hY]
  rw [sum_labelledIndex N (fun x b => if b=a then
    (if x ∈ fullGoodMask N (L+E+1) Y (dyadicBlock N) then (signedMarkRate L b.1.val : ℝ) else 0) else 0)]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [← Finset.sum_filter]
  have heq : (dyadicBlock N).filter (fun x => x ∈ fullGoodMask N (L+E+1) Y (dyadicBlock N)) =
      fullGoodMask N (L+E+1) Y (dyadicBlock N) := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨And.right,fun h => ⟨fullGoodMask_subset_mask _ _ _ _ h,h⟩⟩
  rw [heq]
  simp

/-- Filling restores the full target exactly, without a lower bound on the retained population. -/
theorem signed_filling_balance {C N L E Y : ℕ}
    (hN : 2 ≤ N) (hL : 1 ≤ L) (hC : dyadicCutoff N (L+E+1) ≤ C)
    (hY : L+E+2 ≤ Y) (sigma : SmallSample C Y) (a : Fin (E+1) × F₂) :
    signedAggregateRates (fullRate N L) E a = badSignedFillRates N L E Y a+
      categoryRate (largeUniformPMF C Y)
        (maskedLabelledFamily N (conditionedSignedAt C L E Y sigma)
          (fullGoodMask N (L+E+1) Y (dyadicBlock N))) Prod.snd a := by
  rw [categoryRate_signed_good_eq hN hL hC hY sigma]
  apply NNReal.eq
  have hc := card_fullGood_add_card_fullBad N (L+E+1) Y (dyadicBlock N)
  have hcard : ((fullGoodMask N (L+E+1) Y (dyadicBlock N)).card : ℝ)+
      (fullBadMask N (L+E+1) Y (dyadicBlock N)).card = (N : ℝ) := by
    have hcn : (fullGoodMask N (L+E+1) Y (dyadicBlock N)).card+
        (fullBadMask N (L+E+1) Y (dyadicBlock N)).card=N := by
      have hb : (dyadicBlock N).card=N := by simp [dyadicBlock, two_mul]
      rwa [hb] at hc
    exact_mod_cast hcn
  simp only [signedAggregateRates_coe,NNReal.coe_add,NNReal.coe_mul,NNReal.coe_natCast,
    badSignedFillRates,signedMarkRate_eq_base_mul_weight,fullRate_coe]
  rw [← hcard]
  ring

/-- The complete filling mass is at most the base rate times the deleted-site count. -/
theorem sum_badSignedFillRates_le (N L E Y : ℕ) :
    (∑ a, (badSignedFillRates N L E Y a : ℝ)) ≤
      (1/(2 : ℝ)^L)*(fullBadMask N (L+E+1) Y (dyadicBlock N)).card := by
  simp only [badSignedFillRates,NNReal.coe_mul,NNReal.coe_natCast,← Finset.mul_sum]
  have h : (∑ a : Fin (E+1) × F₂, (signedMarkRate L a.1.val : ℝ)) ≤ 1/(2 : ℝ)^L := by
    simpa only [Fintype.sum_prod_type] using sum_all_signedMarkRate_le_base L E
  have hh := mul_le_mul_of_nonneg_left h
    (by positivity : 0 ≤ ((fullBadMask N (L+E+1) Y (dyadicBlock N)).card : ℝ))
  simpa only [mul_comm] using hh

/-- Actual Poisson-filled category comparison, using the source-faithful directional input. -/
theorem signed_filled_comparison (hStein : DirectionalSteinFactorsStatement)
    {C N L E Y : ℕ} (hN : 2 ≤ N) (hL : 1 ≤ L) (hC : dyadicCutoff N (L+E+1) ≤ C)
    (hY : L+E+2 ≤ Y) (sigma : SmallSample C Y) :
    massTotalVariation (filledLaw (largeUniformPMF C Y)
      (maskedLabelledFamily N (conditionedSignedAt C L E Y sigma)
        (fullGoodMask N (L+E+1) Y (dyadicBlock N))) Prod.snd (badSignedFillRates N L E Y))
      (poissonFieldMass (signedAggregateRates (fullRate N L) E)) ≤
    typedCost (largeUniformPMF C Y)
      (maskedLabelledFamily N (conditionedSignedAt C L E Y sigma)
        (fullGoodMask N (L+E+1) Y (dyadicBlock N))) Prod.snd
      (labelledGraph N (L+E+1) Y (Fin (E+1) × F₂))
      (entryFactor (signedAggregateRates (fullRate N L) E)) := by
  apply directional_poisson_filling_comparison hStein
  · simp only [Fintype.card_prod,Fintype.card_fin]
    norm_num
  · exact hasExactDependencyGraph_signed hN hL _ sigma
  · apply signedAggregateRates_pos
    change (0 : ℝ)<(fullRate N L : ℝ)
    rw [fullRate_coe]
    positivity
  · exact signed_filling_balance hN hL hC hY sigma

/-- Deleting actual bad labels and then aggregating cannot enlarge the deletion cost. -/
theorem signed_aggregate_retention_le {C N L E Y : ℕ} (sigma : SmallSample C Y) :
    massTotalVariation
      (finiteFieldLaw (largeUniformPMF C Y) (typedSum
        (maskedLabelledFamily N (conditionedSignedAt C L E Y sigma) (dyadicBlock N)) Prod.snd Finset.univ))
      (finiteFieldLaw (largeUniformPMF C Y) (typedSum
        (maskedLabelledFamily N (conditionedSignedAt C L E Y sigma)
          (fullGoodMask N (L+E+1) Y (dyadicBlock N))) Prod.snd Finset.univ)) ≤
      badSignedMass C N L E Y (dyadicBlock N) sigma := by
  let X := maskedLabelledFamily N (conditionedSignedAt C L E Y sigma) (dyadicBlock N)
  let good := retainedSignedIndices N L E Y (dyadicBlock N)
  have h := massTotalVariation_retainedField_le_bad_sites (largeUniformPMF C Y) good (indicatorField X)
  simp_rw [eventProbability_indicatorField_active] at h
  rw [← indicatorField_retainedIndicators,retainedIndicators_signed_eq,
    bad_marginal_sum_signed_eq _ (Finset.Subset.refl _)] at h
  have hc := massTotalVariation_pushforward_le (finiteSignedAggregate N E)
    (hasSum_finiteFieldLaw (largeUniformPMF C Y) (indicatorField X))
    (hasSum_finiteFieldLaw (largeUniformPMF C Y) (indicatorField
      (maskedLabelledFamily N (conditionedSignedAt C L E Y sigma)
        (fullGoodMask N (L+E+1) Y (dyadicBlock N)))))
    (finiteFieldLaw_nonneg _ _) (finiteFieldLaw_nonneg _ _)
  rw [pushforwardMass_finiteFieldLaw,pushforwardMass_finiteFieldLaw] at hc
  have heq (Z : SignedMarkIndex N E → LargeSample C Y → Bool) :
      (fun omega => finiteSignedAggregate N E (indicatorField Z omega)) = typedSum Z Prod.snd Finset.univ := by
    funext omega
    exact finiteSignedAggregate_indicator N E Z omega
  rw [heq,heq] at hc
  exact hc.trans h

end
end PaperC.V282.SignedAggregateFilling
