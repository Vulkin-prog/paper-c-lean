import PaperCV282.MacroAggregateFilling
import PaperCV282.PoissonFillingCoupling
import PaperCV282.MacroAggregateArithmetic
import PaperCV282.BulkMarkedInfinite
import PaperCV282.CountablePrimeEventTransfer
import PaperCV282.InfiniteMaskedScalarTransfer

/-! # The actual signed aggregate C.1 comparison and every positive full-F_Y event -/
namespace PaperC.V282.MacroAggregateComparison

open MeasureTheory MacroAggregateFilling MacroAggregateArithmetic MacroAggregateModel
open SignedDirectionalFactors ExactMarkedModel ExactMarkedDependency
open BulkMarkedTransfer BulkMarkedDeletion BulkMarkedInfinite BulkMarkedDependency MacroscopicMaskGeometry FiniteStartMaskAverages SignedGeometricWeights
open BulkSupportGraph BulkProcessCosts MacroAggregateCosts
open DirectionalSteinComparison DirectionalPoissonComparison DirectionalSteinInput DirectionalHessian
open PoissonFilling PoissonFillingCoupling ConditionalStartProbability ConditionalAGGInstantiation
open ArratiaGoldsteinGordonInput SectionThirteenFiniteBound SectionTwelveMoments ConditionalAGGAverage
open MaskedArithmeticGeometry MaskedPairGeometry AllStartSoftPoisson ProcessAGGInput
open FiniteFieldTotalVariation FiniteFieldPoissonCoupling InfiniteRademacher InfiniteCylinderTransfer
open InfiniteConditionalWords InfiniteMassCoupling ConditionedCountableLaw CountablePrimeEventTransfer
open InfiniteMaskedScalarTransfer InfiniteExactLengthProbabilityTransfer InfiniteFieldTransfer
open scoped BigOperators NNReal

noncomputable section

local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

def finiteAggregateLaw (C : ℕ) (sites : Finset ℕ) (L E Y : ℕ) (sigma : SmallSample C Y) : (Fin (E+1) × F₂ → ℕ) → ℝ :=
  finiteFieldLaw (largeUniformPMF C Y) (typedSum
    (maskedLabelledFamily sites (conditionedSignedAt C L E Y sigma) (sites)) Prod.snd Finset.univ)

/-- True event-conditioned signed count vector, before any truncation tail. -/
def conditionalFiniteAggregateDistance (sites : Finset ℕ) (L E : ℕ) (A : Set InfiniteSample) : ℝ :=
  massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure A
    (finiteSignedAggregate sites E ∘ infiniteSignedField sites L E sites))
    (poissonFieldMass (signedAggregateRates (maskRate L sites) E))

/-- Measurability follows from the actual finite-coordinate events. -/
theorem measurable_infiniteSignedField (sites : Finset ℕ) (L E : ℕ) :
    Measurable (infiniteSignedField sites L E sites) := by
  exact measurable_to_countable'
    (fun k => measurableSet_infiniteSignedField_event sites L E sites k)

/-- Deletion, independent filling and the genuine directional graph comparison. -/
theorem finite_aggregate_distance_le_costs (hStein : DirectionalSteinFactorsStatement)
    {C L E Y : ℕ} {sites : Finset ℕ} (hne : sites.Nonempty) (hsite : ∀ x ∈ sites, 2 ≤ x) (hL : 1 ≤ L) (hC : ∀ x ∈ sites, x+L+E+1 ≤ C)
    (hY : L+E+2 ≤ Y) (sigma : SmallSample C Y) :
    massTotalVariation (finiteAggregateLaw C sites L E Y sigma)
      (poissonFieldMass (signedAggregateRates (maskRate L sites) E)) ≤
      badSignedMass C L E Y (sites) sigma+
      (1/(2 : ℝ)^L)*(badMask (L+E+1) Y (sites)).card+
      typedCost (largeUniformPMF C Y)
        (maskedLabelledFamily sites (conditionedSignedAt C L E Y sigma)
          (goodMask (L+E+1) Y (sites))) Prod.snd
        (labelledGraph sites (L+E+1) Y (Fin (E+1) × F₂))
        (entryFactor (signedAggregateRates (maskRate L sites) E)) := by
  let mu := largeUniformPMF C Y
  let X := maskedLabelledFamily sites (conditionedSignedAt C L E Y sigma) (sites)
  let G := maskedLabelledFamily sites (conditionedSignedAt C L E Y sigma)
    (goodMask (L+E+1) Y (sites))
  let fill := badSignedFillRates sites L E Y
  let target := signedAggregateRates (maskRate L sites) E
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
  have hd := signed_aggregate_retention_le (sites := sites) (L := L) (E := E) sigma
  have hf := (unfilled_to_filled_tv_le mu G Prod.snd fill).trans (sum_badSignedFillRates_le sites L E Y)
  have hs := signed_filled_comparison hStein hne hsite hL hC hY sigma
  exact ht1.trans ((add_le_add hd (ht2.trans (add_le_add hf hs))).trans_eq (by ring))

/-- Companion C.1 for the actual finite signed aggregate, uniformly in the number of marks. -/
theorem average_finite_aggregate_le_ledger (hStein : DirectionalSteinFactorsStatement)
    {C L E Y : ℕ} {sites : Finset ℕ} (hne : sites.Nonempty) (hsite : ∀ x ∈ sites, 2 ≤ x) (hL : 1 ≤ L) (hC : ∀ x ∈ sites, x+L+E+1 ≤ C)
    (hY : 2*(L+E+2) ≤ Y) :
    finiteUniformAverage (fun sigma : SmallSample C Y =>
      massTotalVariation (finiteAggregateLaw C sites L E Y sigma)
        (poissonFieldMass (signedAggregateRates (maskRate L sites) E))) ≤
      aggregateLedger C L E Y sites := by
  have h := finiteUniformAverage_mono (fun sigma =>
    finite_aggregate_distance_le_costs (E := E) (Y := Y) hStein hne hsite hL hC (by omega) sigma)
  rw [finiteUniformAverage_add,finiteUniformAverage_add] at h
  have hc := average_typedCost_directional_le hsite hL hC hY
    (sites) (Finset.Subset.refl _) (maskRate L sites) (by
      change (0 : ℝ)<(maskRate L sites : ℝ)
      change 0<(sites.card : ℝ)/2^L
      have hc := Finset.card_pos.mpr hne
      positivity)
  have hb := average_bad_signed_mass_le (Y := Y) hsite hL hC (sites) (Finset.Subset.refl _)
  have hconst : finiteUniformAverage (fun _sigma : SmallSample C Y =>
      (1/(2 : ℝ)^L)*(badMask (L+E+1) Y (sites)).card) =
      (1/(2 : ℝ)^L)*(badMask (L+E+1) Y (sites)).card := by
    simp [finiteUniformAverage]
  rw [hconst] at h
  exact h.trans ((add_le_add (add_le_add hb (le_refl _)) hc).trans_eq (by unfold aggregateLedger; ring))

/-- The finite aggregate is the literal statistic of the adequate source cylinder. -/
theorem finiteAggregateLaw_eq_cylinder (C : ℕ) (sites : Finset ℕ) (L E Y : ℕ) (sigma : SmallSample C Y) :
    finiteAggregateLaw C sites L E Y sigma = finiteFieldLaw (largeUniformPMF C Y)
      (fun eta => finiteSignedAggregate sites E (cylinderSignedField C sites L E (sites) (assemble C Y sigma eta))) := by
  unfold finiteAggregateLaw
  congr 1
  funext eta
  rw [← finiteSignedAggregate_indicator]
  exact congrArg (finiteSignedAggregate sites E)
    (indicatorField_conditionedSigned_eq C sites L E Y (sites) sigma eta)

/-- Each represented conditioning atom has exactly the finite aggregate law. -/
theorem conditional_atom_aggregate_eq_finite {C L E Y : ℕ} {sites : Finset ℕ}
    (hC : ∀ x ∈ sites, x+L+E+1 ≤ C) (sigma : SmallSample C Y) :
    conditionalObservableLaw infiniteRademacherMeasure (infiniteSmallPrimeAtom C Y sigma)
      (finiteSignedAggregate sites E ∘ infiniteSignedField sites L E (sites)) =
      finiteAggregateLaw C sites L E Y sigma := by
  rw [finiteAggregateLaw_eq_cylinder]
  funext k
  rw [conditionalObservableLaw_eq_ratio _ _ (measurableSet_infiniteSmallPrimeAtom C Y sigma),
    finiteFieldLaw_eq_eventProbability]
  have heq : {omega | (finiteSignedAggregate sites E ∘ infiniteSignedField sites L E (sites)) omega=k} =
      restrictToFinite C ⁻¹' {omega | finiteSignedAggregate sites E (cylinderSignedField C sites L E (sites) omega)=k} := by
    ext omega
    simp only [Set.mem_setOf_eq,Set.mem_preimage,Function.comp_apply,cylinderSignedField_restrict_eq hC]
  rw [heq]
  exact (eventProbability_eq_infinite_atom_ratio C Y
    (fun omega => finiteSignedAggregate sites E (cylinderSignedField C sites L E (sites) omega)=k) sigma).symm

/-- The mean over the real prime atoms equals the checked finite source mean. -/
theorem meanAtomDistance_aggregate_eq {C L E Y : ℕ} {sites : Finset ℕ} (hC : ∀ x ∈ sites, x+L+E+1 ≤ C) :
    meanAtomDistance C Y (finiteSignedAggregate sites E ∘ infiniteSignedField sites L E (sites))
      (poissonFieldMass (signedAggregateRates (maskRate L sites) E)) =
      finiteUniformAverage (fun sigma : SmallSample C Y =>
        massTotalVariation (finiteAggregateLaw C sites L E Y sigma)
          (poissonFieldMass (signedAggregateRates (maskRate L sites) E))) := by
  unfold meanAtomDistance
  simp_rw [conditional_atom_aggregate_eq_finite hC]
  rfl

/-- The actual full-F_Y event comparison, with one exact inverse-probability factor. -/
theorem conditional_finite_signed_aggregate_le_ledger (hStein : DirectionalSteinFactorsStatement)
    {C L E Y : ℕ} {sites : Finset ℕ} (hne : sites.Nonempty) (hsite : ∀ x ∈ sites, 2 ≤ x) (hL : 1 ≤ L) (hC : ∀ x ∈ sites, x+L+E+1 ≤ C)
    (hY : 2*(L+E+2) ≤ Y) (hYC : Y ≤ C) (A : Set InfiniteSample)
    (hA : MeasurableSet[MeasurableSpace.comap (restrictToFinite Y) inferInstance] A)
    (hpos : 0 < infiniteRademacherMeasure.real A) :
    conditionalFiniteAggregateDistance sites L E A ≤
      aggregateLedger C L E Y sites/infiniteRademacherMeasure.real A := by
  have h := field_event_tv_le_mean_div_probability hYC A hA hpos
    ((measurable_of_countable (finiteSignedAggregate sites E)).comp (measurable_infiniteSignedField sites L E))
    (hasSum_poissonFieldMass (signedAggregateRates (maskRate L sites) E))
    (poissonFieldMass_nonneg (signedAggregateRates (maskRate L sites) E))
  rw [meanAtomDistance_aggregate_eq hC] at h
  exact h.trans (div_le_div_of_nonneg_right (average_finite_aggregate_le_ledger hStein hne hsite hL hC hY) hpos.le)

end
end PaperC.V282.MacroAggregateComparison
