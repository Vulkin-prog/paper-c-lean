import PaperCV282.FinitePrimeEnvironment
import PaperCV282.SignedAggregateComparison

/-!
# Averaging the genuine conditional tails before removing truncation

The source tail is averaged as a conditional probability. Replacing it by
an unconditional probability divided by an atom probability before averaging
would lose the number of environments; that loss is absent here.
-/
namespace PaperC.V282.MeanAggregateTruncation

open MeasureTheory ProbabilityTheory FinitePrimeEnvironment SignedAggregateComparison
open SignedAggregateTruncation SignedAggregateConfiguration SignedDirectionalFactors
open InfiniteRademacher InfiniteCylinderTransfer InfiniteConditionalWords ConditionedCountableLaw
open CountablePrimeEventTransfer CountableLawTransfer InfiniteMassCoupling FiniteFieldTotalVariation
open SpatialMarkedTypes SpatialMarkedTarget SpatialMarkedTargetProjection ExactMarkedInfinite ExactMarkedModel
open SpatialMarkedFieldComparison ConditionalStartProbability SectionThirteenFiniteBound ConditionalAGGAverage
open DirectionalMarkedCosts MarkedDetruncation SignedAggregateRates DirectionalSteinInput AllStartSoftPoisson
open scoped NNReal

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

def aggregateTailEvent (N L E : ℕ) : Set InfiniteSample :=
  {omega | signedAggregateSource N L omega ≠ embedSignedAggregate E
    (finiteSignedAggregate N E (infiniteSignedField N L E (dyadicBlock N) omega))}

theorem measurableSet_aggregateTailEvent (N L E : ℕ) : MeasurableSet (aggregateTailEvent N L E) := by
  exact (measurableSet_eq_fun (measurable_signedAggregateSource N L)
    ((measurable_of_countable (embedSignedAggregate E ∘ finiteSignedAggregate N E)).comp
      (SpatialMarkedFieldComparison.measurable_infiniteSignedField_full N L E))).compl

/-- Pointwise conditioning retains the actual conditional source-tail probability. -/
theorem conditional_tv_le_actual_tail (N L E : ℕ) (A : Set InfiniteSample)
    (hpos : 0 < infiniteRademacherMeasure.real A) :
    conditionalSignedAggregateDistance N L A ≤
      (cond infiniteRademacherMeasure A).real (aggregateTailEvent N L E)+
      conditionalFiniteSignedAggregateDistance N L E A+(fullRate N L : ℝ)/(2 : ℝ)^(E+1) := by
  letI instProbabilityConditionalSource : IsProbabilityMeasure (cond infiniteRademacherMeasure A) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hpos)
  have hf : Measurable (finiteSignedAggregate N E ∘ infiniteSignedField N L E (dyadicBlock N)) :=
    (measurable_of_countable _).comp (SpatialMarkedFieldComparison.measurable_infiniteSignedField_full N L E)
  have hm : massTotalVariation
      (observableLaw (cond infiniteRademacherMeasure A)
        (finiteSignedAggregate N E ∘ infiniteSignedField N L E (dyadicBlock N)))
      (observableLaw (spatialTargetMeasure N L) (finiteSignedAggregate N E ∘ projectConfiguration N E))=
        conditionalFiniteSignedAggregateDistance N L E A := by
    rw [observableLaw_project_signedAggregate]
    rfl
  exact truncation_tv_le_of_bounds (cond infiniteRademacherMeasure A) (spatialTargetMeasure N L)
    (measurable_signedAggregateSource N L) (measurable_of_countable _) hf (measurable_of_countable _)
    (embedSignedAggregate E) (le_refl _) hm.le (target_aggregate_disagreement_le N L E)

/-- The full genuine mean distance has only one unconditional source tail. -/
theorem mean_signed_aggregate_le_ledger_and_tails (hStein : DirectionalSteinFactorsStatement)
    {C N L E Y : ℕ} (hN : 2 ≤ N) (hL : 1 ≤ L)
    (hC : dyadicCutoff N (L+E+1) ≤ C) (hY : 2*(L+E+2) ≤ Y) :
    meanAtomDistance C Y (signedAggregateSource N L) (signedAggregateTargetLaw N L) ≤
      infiniteMarkTailProbability N L E+signedAggregateLedger N L E Y (dyadicBlock N)+
      (fullRate N L : ℝ)/(2 : ℝ)^(E+1) := by
  have hpos (sigma : SmallSample C Y) :
      0 < infiniteRademacherMeasure.real (infiniteSmallPrimeAtom C Y sigma) := by
    rw [PrimeFieldEventConditioning.real_atom_mass]
    positivity
  have ht := finiteUniformAverage_mono (fun sigma : SmallSample C Y =>
    conditional_tv_le_actual_tail N L E (infiniteSmallPrimeAtom C Y sigma) (hpos sigma))
  rw [finiteUniformAverage_add,finiteUniformAverage_add] at ht
  have htail : finiteUniformAverage (fun sigma : SmallSample C Y =>
      (cond infiniteRademacherMeasure (infiniteSmallPrimeAtom C Y sigma)).real (aggregateTailEvent N L E)) ≤
        infiniteMarkTailProbability N L E := by
    change uniformAverage _ ≤ _
    rw [average_conditional_event C Y _ (measurableSet_aggregateTailEvent N L E)]
    exact source_aggregate_disagreement_le N L E
  have hfinite : finiteUniformAverage (fun sigma : SmallSample C Y =>
      conditionalFiniteSignedAggregateDistance N L E (infiniteSmallPrimeAtom C Y sigma)) ≤
        signedAggregateLedger N L E Y (dyadicBlock N) := by
    change meanAtomDistance C Y (finiteSignedAggregate N E ∘ infiniteSignedField N L E (dyadicBlock N))
      (FiniteFieldPoissonCoupling.poissonFieldMass (signedAggregateRates (fullRate N L) E)) ≤ _
    rw [meanAtomDistance_aggregate_eq hC]
    exact average_finite_aggregate_le_ledger hStein hN hL hC hY
  have hconst : finiteUniformAverage (fun _sigma : SmallSample C Y =>
      (fullRate N L : ℝ)/(2 : ℝ)^(E+1)) = (fullRate N L : ℝ)/(2 : ℝ)^(E+1) := by
    simp [finiteUniformAverage]
  rw [hconst] at ht
  exact ht.trans (add_le_add (add_le_add htail hfinite) (le_refl _))

end
end PaperC.V282.MeanAggregateTruncation
