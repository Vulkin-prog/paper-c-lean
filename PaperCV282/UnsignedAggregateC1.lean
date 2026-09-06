import PaperCV282.UnsignedDirectionalCosts
import PaperCV282.SignedAggregateComparison
import PaperCV282.UnsignedAggregateTarget

/-!
# The exact unsigned finite comparison of companion C.1

The proof uses the actual two-sign field to cover E=0 with the same published
directional input. Signs are summed at fixed excesses inside the graph costs,
so the final arithmetic profile is relative at Q=L+E+1 rows. The final laws
are those of the literal unsigned exact-length counts on the infinite source.
-/
namespace PaperC.V282.UnsignedAggregateC1

open MeasureTheory ProbabilityTheory InfiniteRademacher InfiniteCylinderTransfer InfiniteConditionalWords
open UnsignedDirectionalCosts SignedAggregateComparison SignedAggregateFilling
open SignedAggregateTruncation SignedAggregateConfiguration SignedDirectionalFactors
open UnsignedAggregateTarget AggregateCoordinateIdentities ExactMarkedModel ExactMarkedInfinite
open ExactMarkedDeletion DirectionalSteinInput DirectionalSteinComparison DirectionalHessian
open ConditionalStartProbability ConditionalAGGAverage ConditionalAGGInstantiation
open ArratiaGoldsteinGordonInput SectionThirteenFiniteBound SectionTwelveMoments
open AllStartSoftPoisson MaskedArithmeticGeometry MaskedPairGeometry TwoWindowParity
open LabelledProcessCosts LabelledSupportGraph FiniteFieldTotalVariation FiniteFieldPoissonCoupling
open PoissonFieldMeasure FiniteFieldPoissonCoupling MassPushforward ConditionedCountableLaw
open CountableLawTransfer CountablePrimeEventTransfer InfiniteMassCoupling
open GeometricClusterTruncation MarkedDetruncation
open DirectionalMarkedCosts SpatialMarkedFieldComparison
open scoped BigOperators NNReal

noncomputable section

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

def relativeAggregateLedger (N L E Y : ℕ) (mask : Finset ℕ) : ℝ :=
  (1/(2 : ℝ)^L)*((fullDefectMass L mask : ℝ)+2*(fullBadMask N (L+E+1) Y mask).card)+
  (1/(2 : ℝ)^L)^2*signedDirectionalFactor (fullRate N L)*
    (6*(N : ℝ)*(L+E+2)+2*(maskedSupportEdges (L+E+1) Y mask).card+
      (jointDefectMass N (L+E+1) (separatedPairs mask (L+E+1)) : ℝ))

def exactCountVector (N L E : ℕ) (omega : InfiniteSample) (e : Fin (E+1)) : ℕ :=
  infiniteExactLengthCount N L e.val omega

def conditionalExactAggregateDistance (N L E : ℕ) (A : Set InfiniteSample) : ℝ :=
  massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure A (exactCountVector N L E))
    (poissonFieldMass (geometricCoordinateRates (fullRate N L) E))

/-- The three terms printed in (C.5), with one explicit universal directional constant. -/
def printedAggregateBudget (N L E Y : ℕ) : ℝ :=
  (1/(2 : ℝ)^L)*((fullDefectMass L (dyadicBlock N) : ℝ)+
      (fullBadMask N (L+E+1) Y (dyadicBlock N)).card)+
  (1/(2 : ℝ)^L)^2*signedDirectionalFactor (fullRate N L)*
    ((N : ℝ)*(L+E+1)+(maskedSupportEdges (L+E+1) Y (dyadicBlock N)).card+
      (jointDefectMass N (L+E+1) (separatedPairs (dyadicBlock N) (L+E+1)) : ℝ))

theorem relativeAggregateLedger_le_printed (N L E Y : ℕ) :
    relativeAggregateLedger N L E Y (dyadicBlock N)≤12*printedAggregateBudget N L E Y := by
  have hM : (0 : ℝ)≤fullDefectMass L (dyadicBlock N) := by positivity
  have hD : (0 : ℝ)≤(fullBadMask N (L+E+1) Y (dyadicBlock N)).card := by positivity
  have hG : (0 : ℝ)≤(maskedSupportEdges (L+E+1) Y (dyadicBlock N)).card := by positivity
  have hR : (0 : ℝ)≤jointDefectMass N (L+E+1) (separatedPairs (dyadicBlock N) (L+E+1)) := by positivity
  have hlocal : 6*(N : ℝ)*(L+E+2)≤12*(N : ℝ)*(L+E+1) := by
    have h : (0 : ℝ)≤(N : ℝ)*((L : ℝ)+E) := by positivity
    nlinarith only [h]
  have hdel : (fullDefectMass L (dyadicBlock N) : ℝ)+
      2*(fullBadMask N (L+E+1) Y (dyadicBlock N)).card ≤
    12*((fullDefectMass L (dyadicBlock N) : ℝ)+(fullBadMask N (L+E+1) Y (dyadicBlock N)).card) := by
    linarith
  have hgraph : 6*(N : ℝ)*(L+E+2)+2*(maskedSupportEdges (L+E+1) Y (dyadicBlock N)).card+
      (jointDefectMass N (L+E+1) (separatedPairs (dyadicBlock N) (L+E+1)) : ℝ) ≤
    12*((N : ℝ)*(L+E+1)+(maskedSupportEdges (L+E+1) Y (dyadicBlock N)).card+
      (jointDefectMass N (L+E+1) (separatedPairs (dyadicBlock N) (L+E+1)) : ℝ)) := by
    linarith
  have hs := signedDirectionalFactor_nonneg (fullRate N L).coe_nonneg
  have h := add_le_add (mul_le_mul_of_nonneg_left hdel (by positivity : (0 : ℝ)≤1/2^L))
    (mul_le_mul_of_nonneg_left hgraph (by positivity : (0 : ℝ)≤(1/2^L)^2*signedDirectionalFactor (fullRate N L)))
  exact h.trans_eq (by unfold printedAggregateBudget;ring)

/-- The relative ledger bounds even the retained signed comparison, before forgetting signs. -/
theorem average_finite_signed_le_relative (hStein : DirectionalSteinFactorsStatement)
    {C N L E Y : ℕ} (hN : 2≤N) (hL : 1≤L) (hC : dyadicCutoff N (L+E+1)≤C)
    (hY : 2*(L+E+1)<Y) :
    finiteUniformAverage (fun sigma : SmallSample C Y =>
      massTotalVariation (finiteAggregateLaw C N L E Y sigma)
        (poissonFieldMass (signedAggregateRates (fullRate N L) E))) ≤
      relativeAggregateLedger N L E Y (dyadicBlock N) := by
  have h := finiteUniformAverage_mono (fun sigma =>
    finite_aggregate_distance_le_costs (E := E) (Y := Y) hStein hN hL hC (by omega) sigma)
  rw [finiteUniformAverage_add,finiteUniformAverage_add] at h
  have hc := average_typedCost_relative_le hN hL hC hY
    (dyadicBlock N) (Finset.Subset.refl _) (fullRate N L) (by
      change (0 : ℝ)<(fullRate N L : ℝ)
      rw [fullRate_coe]
      positivity)
  have hb := average_bad_signed_mass_le (Y := Y) hN hL hC (dyadicBlock N) (Finset.Subset.refl _)
  have hconst : finiteUniformAverage (fun _sigma : SmallSample C Y =>
      (1/(2 : ℝ)^L)*(fullBadMask N (L+E+1) Y (dyadicBlock N)).card)=
      (1/(2 : ℝ)^L)*(fullBadMask N (L+E+1) Y (dyadicBlock N)).card := by
    simp [finiteUniformAverage]
  rw [hconst] at h
  exact h.trans ((add_le_add (add_le_add hb (le_refl _)) hc).trans_eq (by
    unfold relativeAggregateLedger
    ring))

/-- The statistic is the true count for each exact excess, not an assumed image law. -/
theorem exactCountVector_eq_forget_signed (N L E : ℕ) :
    exactCountVector N L E=forgetFiniteSigns E ∘
      (finiteSignedAggregate N E ∘ infiniteSignedField N L E (dyadicBlock N)) := by
  funext omega e
  simp only [Function.comp_apply,forgetFiniteSigns,finiteSignedAggregate]
  rw [Finset.sum_comm]
  have hp (x : {x : ℕ // x∈dyadicBlock N}) :
      (∑ s : F₂,infiniteSignedField N L E (dyadicBlock N) omega (x,(e,s)))=
        exactMarkValue (infiniteValueBit omega) x.val L e.val := by
    change (∑ s : F₂, if x.val∈dyadicBlock N ∧
      SignedExactMark (infiniteValueBit omega) x.val L e.val s then 1 else 0)=_
    have hx : x.val∈dyadicBlock N := x.property
    simp only [hx,true_and]
    exact sum_signedMarkValue _ _ _ _
  simp_rw [hp]
  change (∑ x∈dyadicBlock N,exactMarkValue (infiniteValueBit omega) x L e.val)=
    ∑ x∈(dyadicBlock N).attach,exactMarkValue (infiniteValueBit omega) x.val L e.val
  exact (Finset.sum_attach _ _).symm

theorem measurable_exactCountVector (N L E : ℕ) : Measurable (exactCountVector N L E) := by
  rw [exactCountVector_eq_forget_signed]
  exact (measurable_of_countable _).comp
    ((measurable_of_countable _).comp (measurable_infiniteSignedField_full N L E))

theorem pushforward_signed_aggregate_target (lambda : ℝ≥0) (E : ℕ) :
    pushforwardMass (forgetFiniteSigns E) (poissonFieldMass (signedAggregateRates lambda E))=
      poissonFieldMass (geometricCoordinateRates lambda E) := by
  rw [pushforward_poissonFieldMass_of_hasLaw _ _ _ (hasLaw_forgetFiniteSigns lambda E)]
  exact funext (fieldMeasure_real_singleton _)

/-- The printed independent coordinate mean is exactly lambda times 2^(-e-1). -/
theorem unsigned_target_mean (N L E : ℕ) (e : Fin (E+1)) :
    (geometricCoordinateRates (fullRate N L) E e : ℝ)=
      (N : ℝ)/(2 : ℝ)^L/(2 : ℝ)^(e.val+1) := by
  simp [geometricCoordinateRates,fullRate_coe,div_eq_mul_inv]

theorem conditional_exact_le_signed (N L E : ℕ) (A : Set InfiniteSample)
    (hpos : 0 < infiniteRademacherMeasure.real A) :
    conditionalExactAggregateDistance N L E A≤conditionalFiniteSignedAggregateDistance N L E A := by
  have hm : Measurable (finiteSignedAggregate N E ∘ infiniteSignedField N L E (dyadicBlock N)) :=
    (measurable_of_countable _).comp (measurable_infiniteSignedField_full N L E)
  have hc := massTotalVariation_pushforward_le (forgetFiniteSigns E)
    (hasSum_conditionalObservableLaw infiniteRademacherMeasure A hpos hm)
    (hasSum_poissonFieldMass (signedAggregateRates (fullRate N L) E))
    (conditionalObservableLaw_nonneg _ _ _) (poissonFieldMass_nonneg _)
  rw [pushforward_signed_aggregate_target] at hc
  unfold conditionalExactAggregateDistance
  rw [exactCountVector_eq_forget_signed]
  have he := pushforwardMass_observableLaw (cond infiniteRademacherMeasure A) hm (forgetFiniteSigns E)
  change pushforwardMass _ (conditionalObservableLaw infiniteRademacherMeasure A _) =
    conditionalObservableLaw infiniteRademacherMeasure A _ at he
  rw [he] at hc
  exact hc

/-- Genuine conditional laws averaged on the small-prime atoms, with the exact relative profile. -/
theorem mean_exact_aggregate_le_relative (hStein : DirectionalSteinFactorsStatement)
    {C N L E Y : ℕ} (hN : 2≤N) (hL : 1≤L) (hC : dyadicCutoff N (L+E+1)≤C)
    (hY : 2*(L+E+1)<Y) :
    meanAtomDistance C Y (exactCountVector N L E)
      (poissonFieldMass (geometricCoordinateRates (fullRate N L) E))≤
      relativeAggregateLedger N L E Y (dyadicBlock N) := by
  have h := finiteUniformAverage_mono (fun sigma : SmallSample C Y =>
    conditional_exact_le_signed N L E (infiniteSmallPrimeAtom C Y sigma)
      (ENNReal.toReal_pos (ne_of_gt (infiniteSmallPrimeAtom_measure_pos C Y sigma))
        (infiniteSmallPrimeAtom_measure_ne_top C Y sigma)))
  have hs := average_finite_signed_le_relative (C := C) hStein hN hL hC hY
  rw [← meanAtomDistance_aggregate_eq hC] at hs
  exact h.trans hs

/-- Full-F_Y restriction multiplies the checked finite bound by exactly one inverse probability. -/
theorem event_exact_aggregate_le_relative (hStein : DirectionalSteinFactorsStatement)
    {C N L E Y : ℕ} (hN : 2≤N) (hL : 1≤L) (hC : dyadicCutoff N (L+E+1)≤C)
    (hY : 2*(L+E+1)<Y) (hYC : Y≤C) (A : Set InfiniteSample)
    (hA : MeasurableSet[MeasurableSpace.comap (restrictToFinite Y) inferInstance] A)
    (hpos : 0 < infiniteRademacherMeasure.real A) :
    conditionalExactAggregateDistance N L E A≤
      relativeAggregateLedger N L E Y (dyadicBlock N)/infiniteRademacherMeasure.real A := by
  have h := field_event_tv_le_mean_div_probability hYC A hA hpos
    (measurable_exactCountVector N L E) (hasSum_poissonFieldMass (geometricCoordinateRates (fullRate N L) E))
    (poissonFieldMass_nonneg (geometricCoordinateRates (fullRate N L) E))
  exact h.trans (div_le_div_of_nonneg_right
    (mean_exact_aggregate_le_relative hStein hN hL hC hY) hpos.le)

/-- Companion C.1/(C.5): every E, the exact 2Q<Y domain, and genuine full-F_Y atom laws. -/
theorem theorem_c_one (hStein : DirectionalSteinFactorsStatement)
    {N L E Y : ℕ} (hN : 2≤N) (hL : 1≤L) (hY : 2*(L+E+1)<Y) :
    meanAtomDistance (max Y (dyadicCutoff N (L+E+1))) Y (exactCountVector N L E)
      (poissonFieldMass (geometricCoordinateRates (fullRate N L) E))≤
      12*printedAggregateBudget N L E Y :=
  (mean_exact_aggregate_le_relative hStein hN hL (le_max_right _ _) hY).trans
    (relativeAggregateLedger_le_printed N L E Y)

theorem theorem_c_one_event (hStein : DirectionalSteinFactorsStatement)
    {N L E Y : ℕ} (hN : 2≤N) (hL : 1≤L) (hY : 2*(L+E+1)<Y) (A : Set InfiniteSample)
    (hA : MeasurableSet[MeasurableSpace.comap (restrictToFinite Y) inferInstance] A)
    (hpos : 0 < infiniteRademacherMeasure.real A) :
    conditionalExactAggregateDistance N L E A≤
      12*printedAggregateBudget N L E Y/infiniteRademacherMeasure.real A :=
  (event_exact_aggregate_le_relative hStein hN hL (le_max_right Y _) hY (le_max_left _ _) A hA hpos).trans
    (div_le_div_of_nonneg_right (relativeAggregateLedger_le_printed N L E Y) hpos.le)

end
end PaperC.V282.UnsignedAggregateC1
