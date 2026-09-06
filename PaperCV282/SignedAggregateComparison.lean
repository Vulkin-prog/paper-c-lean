import PaperCV282.SignedAggregateFilling
import PaperCV282.PoissonFillingCoupling
import PaperCV282.SignedAggregateRates
import PaperCV282.SignedAggregateTruncation
import PaperCV282.CountablePrimeEventTransfer
import PaperCV282.InfiniteMaskedScalarTransfer

/-! # The actual signed aggregate C.1 comparison and every positive full-F_Y event -/
namespace PaperC.V282.SignedAggregateComparison

open MeasureTheory SignedAggregateFilling SignedAggregateRates SignedAggregateArithmetic SignedAggregateConfiguration
open SignedAggregateTruncation SignedDirectionalFactors ExactMarkedModel ExactMarkedDependency
open ExactMarkedFieldTransfer ExactMarkedDeletion ExactMarkedInfinite SignedGeometricWeights
open LabelledSupportGraph LabelledProcessCosts DirectionalMarkedCosts
open DirectionalSteinComparison DirectionalPoissonComparison DirectionalSteinInput DirectionalHessian
open PoissonFilling PoissonFillingCoupling ConditionalStartProbability ConditionalAGGInstantiation
open ArratiaGoldsteinGordonInput SectionThirteenFiniteBound SectionTwelveMoments ConditionalAGGAverage
open MaskedArithmeticGeometry MaskedPairGeometry AllStartSoftPoisson ProcessAGGInput
open FiniteFieldTotalVariation FiniteFieldPoissonCoupling InfiniteRademacher InfiniteCylinderTransfer
open InfiniteConditionalWords InfiniteMassCoupling ConditionedCountableLaw CountablePrimeEventTransfer
open InfiniteMaskedScalarTransfer InfiniteExactLengthProbabilityTransfer InfiniteFieldTransfer SpatialMarkedFieldComparison
open scoped BigOperators NNReal

noncomputable section

local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

def finiteAggregateLaw (C N L E Y : ℕ) (sigma : SmallSample C Y) : (Fin (E+1) × F₂ → ℕ) → ℝ :=
  finiteFieldLaw (largeUniformPMF C Y) (typedSum
    (maskedLabelledFamily N (conditionedSignedAt C L E Y sigma) (dyadicBlock N)) Prod.snd Finset.univ)

/-- Deletion, independent filling and the genuine directional graph comparison. -/
theorem finite_aggregate_distance_le_costs (hStein : DirectionalSteinFactorsStatement)
    {C N L E Y : ℕ} (hN : 2 ≤ N) (hL : 1 ≤ L) (hC : dyadicCutoff N (L+E+1) ≤ C)
    (hY : L+E+2 ≤ Y) (sigma : SmallSample C Y) :
    massTotalVariation (finiteAggregateLaw C N L E Y sigma)
      (poissonFieldMass (signedAggregateRates (fullRate N L) E)) ≤
      badSignedMass C N L E Y (dyadicBlock N) sigma+
      (1/(2 : ℝ)^L)*(fullBadMask N (L+E+1) Y (dyadicBlock N)).card+
      typedCost (largeUniformPMF C Y)
        (maskedLabelledFamily N (conditionedSignedAt C L E Y sigma)
          (fullGoodMask N (L+E+1) Y (dyadicBlock N))) Prod.snd
        (labelledGraph N (L+E+1) Y (Fin (E+1) × F₂))
        (entryFactor (signedAggregateRates (fullRate N L) E)) := by
  let mu := largeUniformPMF C Y
  let X := maskedLabelledFamily N (conditionedSignedAt C L E Y sigma) (dyadicBlock N)
  let G := maskedLabelledFamily N (conditionedSignedAt C L E Y sigma)
    (fullGoodMask N (L+E+1) Y (dyadicBlock N))
  let fill := badSignedFillRates N L E Y
  let target := signedAggregateRates (fullRate N L) E
  have ht1 := massTotalVariation_triangle
    (hasSum_finiteFieldLaw mu (typedSum X Prod.snd Finset.univ)).summable
    (hasSum_finiteFieldLaw mu (typedSum G Prod.snd Finset.univ)).summable
    (hasSum_poissonFieldMass target).summable
    (finiteFieldLaw_nonneg _ _) (finiteFieldLaw_nonneg _ _) (poissonFieldMass_nonneg target)
  have ht2 := massTotalVariation_triangle
    (hasSum_finiteFieldLaw mu (typedSum G Prod.snd Finset.univ)).summable
    (hasSum_filledLaw mu G Prod.snd fill).summable
    (hasSum_poissonFieldMass target).summable
    (finiteFieldLaw_nonneg _ _) (filledLaw_nonneg _ _ _ _) (poissonFieldMass_nonneg target)
  have hd := signed_aggregate_retention_le (N := N) (L := L) (E := E) sigma
  have hf := (unfilled_to_filled_tv_le mu G Prod.snd fill).trans (sum_badSignedFillRates_le N L E Y)
  have hs := signed_filled_comparison hStein hN hL hC hY sigma
  exact ht1.trans ((add_le_add hd (ht2.trans (add_le_add hf hs))).trans_eq (by ring))

/-- Companion C.1 for the actual finite signed aggregate, uniformly in the number of marks. -/
theorem average_finite_aggregate_le_ledger (hStein : DirectionalSteinFactorsStatement)
    {C N L E Y : ℕ} (hN : 2 ≤ N) (hL : 1 ≤ L) (hC : dyadicCutoff N (L+E+1) ≤ C)
    (hY : 2*(L+E+2) ≤ Y) :
    finiteUniformAverage (fun sigma : SmallSample C Y =>
      massTotalVariation (finiteAggregateLaw C N L E Y sigma)
        (poissonFieldMass (signedAggregateRates (fullRate N L) E))) ≤
      signedAggregateLedger N L E Y (dyadicBlock N) := by
  have h := finiteUniformAverage_mono (fun sigma =>
    finite_aggregate_distance_le_costs (E := E) (Y := Y) hStein hN hL hC (by omega) sigma)
  rw [finiteUniformAverage_add,finiteUniformAverage_add] at h
  have hc := average_typedCost_signed_directional_le hN hL hC hY
    (dyadicBlock N) (Finset.Subset.refl _) (fullRate N L) (by
      change (0 : ℝ)<(fullRate N L : ℝ)
      rw [fullRate_coe]
      positivity)
  have hb := average_bad_signed_mass_le (Y := Y) hN hL hC (dyadicBlock N) (Finset.Subset.refl _)
  have hconst : finiteUniformAverage (fun _sigma : SmallSample C Y =>
      (1/(2 : ℝ)^L)*(fullBadMask N (L+E+1) Y (dyadicBlock N)).card) =
      (1/(2 : ℝ)^L)*(fullBadMask N (L+E+1) Y (dyadicBlock N)).card := by
    simp [finiteUniformAverage]
  rw [hconst] at h
  exact h.trans ((add_le_add (add_le_add hb (le_refl _)) hc).trans_eq (by unfold signedAggregateLedger; ring))

/-- The finite aggregate is the literal statistic of the adequate source cylinder. -/
theorem finiteAggregateLaw_eq_cylinder (C N L E Y : ℕ) (sigma : SmallSample C Y) :
    finiteAggregateLaw C N L E Y sigma = finiteFieldLaw (largeUniformPMF C Y)
      (fun eta => finiteSignedAggregate N E (cylinderSignedField C N L E (dyadicBlock N) (assemble C Y sigma eta))) := by
  unfold finiteAggregateLaw
  congr 1
  funext eta
  rw [← finiteSignedAggregate_indicator]
  exact congrArg (finiteSignedAggregate N E)
    (indicatorField_conditionedSigned_eq C N L E Y (dyadicBlock N) sigma eta)

/-- Each represented conditioning atom has exactly the finite aggregate law. -/
theorem conditional_atom_aggregate_eq_finite {C N L E Y : ℕ}
    (hC : dyadicCutoff N (L+E+1) ≤ C) (sigma : SmallSample C Y) :
    conditionalObservableLaw infiniteRademacherMeasure (infiniteSmallPrimeAtom C Y sigma)
      (finiteSignedAggregate N E ∘ infiniteSignedField N L E (dyadicBlock N)) =
      finiteAggregateLaw C N L E Y sigma := by
  rw [finiteAggregateLaw_eq_cylinder]
  funext k
  rw [conditionalObservableLaw_eq_ratio _ _ (measurableSet_infiniteSmallPrimeAtom C Y sigma),
    finiteFieldLaw_eq_eventProbability]
  have heq : {omega | (finiteSignedAggregate N E ∘ infiniteSignedField N L E (dyadicBlock N)) omega=k} =
      restrictToFinite C ⁻¹' {omega | finiteSignedAggregate N E (cylinderSignedField C N L E (dyadicBlock N) omega)=k} := by
    ext omega
    simp only [Set.mem_setOf_eq,Set.mem_preimage,Function.comp_apply,cylinderSignedField_restrict_eq hC]
  rw [heq]
  exact (eventProbability_eq_infinite_atom_ratio C Y
    (fun omega => finiteSignedAggregate N E (cylinderSignedField C N L E (dyadicBlock N) omega)=k) sigma).symm

/-- The mean over the real prime atoms equals the checked finite source mean. -/
theorem meanAtomDistance_aggregate_eq {C N L E Y : ℕ} (hC : dyadicCutoff N (L+E+1) ≤ C) :
    meanAtomDistance C Y (finiteSignedAggregate N E ∘ infiniteSignedField N L E (dyadicBlock N))
      (poissonFieldMass (signedAggregateRates (fullRate N L) E)) =
      finiteUniformAverage (fun sigma : SmallSample C Y =>
        massTotalVariation (finiteAggregateLaw C N L E Y sigma)
          (poissonFieldMass (signedAggregateRates (fullRate N L) E))) := by
  unfold meanAtomDistance
  simp_rw [conditional_atom_aggregate_eq_finite hC]
  rfl

/-- The actual full-F_Y event comparison, with one exact inverse-probability factor. -/
theorem conditional_finite_signed_aggregate_le_ledger (hStein : DirectionalSteinFactorsStatement)
    {C N L E Y : ℕ} (hN : 2 ≤ N) (hL : 1 ≤ L) (hC : dyadicCutoff N (L+E+1) ≤ C)
    (hY : 2*(L+E+2) ≤ Y) (hYC : Y ≤ C) (A : Set InfiniteSample)
    (hA : MeasurableSet[MeasurableSpace.comap (restrictToFinite Y) inferInstance] A)
    (hpos : 0 < infiniteRademacherMeasure.real A) :
    conditionalFiniteSignedAggregateDistance N L E A ≤
      signedAggregateLedger N L E Y (dyadicBlock N)/infiniteRademacherMeasure.real A := by
  have h := field_event_tv_le_mean_div_probability hYC A hA hpos
    ((measurable_of_countable (finiteSignedAggregate N E)).comp (measurable_infiniteSignedField_full N L E))
    (hasSum_poissonFieldMass (signedAggregateRates (fullRate N L) E))
    (poissonFieldMass_nonneg (signedAggregateRates (fullRate N L) E))
  rw [meanAtomDistance_aggregate_eq hC] at h
  exact h.trans (div_le_div_of_nonneg_right (average_finite_aggregate_le_ledger hStein hN hL hC hY) hpos.le)

end
end PaperC.V282.SignedAggregateComparison
