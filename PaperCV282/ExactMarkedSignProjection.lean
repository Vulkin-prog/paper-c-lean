import PaperCV282.ExactMarkedInfinite
import PaperCV282.ExactMarkedFieldTransfer
import PaperCV282.PoissonFieldAggregation

/-!
# Forgetting only the sign of an exact mark

The source projection is exactly the unsigned marked field. The target
projection is the product Poisson field with twice each signed rate. This
is an identity of whole laws, followed by contraction with coefficient one.
-/
namespace PaperC.V282.ExactMarkedSignProjection

open MeasureTheory ProbabilityTheory Set
open ExactMarkedModel ExactMarkedInfinite ExactMarkedFieldTransfer MixedLengthAffine
open PoissonFieldMeasure PoissonFieldAggregation MassPushforward
open FiniteFieldTotalVariation FiniteFieldPoissonCoupling InfiniteFieldTransfer
open InfiniteRademacher InfiniteCylinderTransfer InfiniteConditionalWords InfiniteExactLengthProbabilityTransfer
open ConditionalStartProbability ConditionalAGGInstantiation ConditionalAGGAverage
open ArratiaGoldsteinGordonInput SectionThirteenCouplings SectionThirteenFiniteBound InfiniteMaskedScalarTransfer
open scoped BigOperators NNReal

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- Preserve site and excess and sum exactly the two sign coordinates. -/
def forgetSigns (N E : ℕ) (k : SignedMarkIndex N E → ℕ) (i : ExactMarkIndex N E) : ℕ :=
  ∑ s : F₂, k (i.1,(i.2,s))

/-- Reorder the same carrier so that each sign pair is one column. -/
def signFirstEquiv (N E : ℕ) : SignedMarkIndex N E ≃ F₂ × ExactMarkIndex N E where
  toFun i := (i.2.2,(i.1,i.2.1))
  invFun i := (i.2.1,(i.2.2,i.1))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The unsigned target retains every site and excess label. -/
def allExactRates (N L E : ℕ) (mask : Finset ℕ) (i : ExactMarkIndex N E) : ℝ≥0 :=
  if i.1.val ∈ mask then exactMarkRate L i.2.val else 0

/-- Actual product Poisson laws are invariant under reindexing by an equivalence. -/
theorem hasLaw_reindexedPoisson {I J : Type*} [Fintype I] [Fintype J]
    (rate : I → ℝ≥0) (e : I ≃ J) :
    HasLaw (fun k : I → ℕ => fun j => k (e.symm j))
      (fieldMeasure (fun j => rate (e.symm j))) (fieldMeasure rate) := by
  refine ⟨(measurable_of_countable _).aemeasurable,?_⟩
  apply Measure.ext_of_singleton
  intro k
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have hpre : (fun a : I → ℕ => fun j => a (e.symm j)) ⁻¹' {k} = {fun i => k (e i)} := by
    ext a
    simp only [Set.mem_preimage,Set.mem_singleton_iff]
    constructor
    · intro h
      funext i
      simpa only [e.symm_apply_apply] using congrFun h (e i)
    · intro h
      subst a
      funext j
      simp only [e.apply_symm_apply]
  rw [hpre]
  simp only [fieldMeasure,Measure.pi_singleton]
  simpa only [e.symm_apply_apply] using
    e.prod_comp (fun j => poissonMeasure (rate (e.symm j)) {k j})

/-- Summing the two signed rates gives exactly the unsigned rate at each masked coordinate. -/
theorem sum_signedRates_eq_exact (N L E : ℕ) (mask : Finset ℕ) (i : ExactMarkIndex N E) :
    (∑ s : F₂, allSignedRates N L E mask (i.1,(i.2,s))) = allExactRates N L E mask i := by
  apply NNReal.coe_injective
  push_cast
  by_cases hi : i.1.val ∈ mask
  · simp only [allSignedRates,allExactRates,if_pos hi]
    exact sum_signedMarkRate L i.2.val
  · simp [allSignedRates,allExactRates,hi]

/-- The complete target after forgetting signs is the independent unsigned product field. -/
theorem hasLaw_forgetSigns (N L E : ℕ) (mask : Finset ℕ) :
    HasLaw (forgetSigns N E) (fieldMeasure (allExactRates N L E mask))
      (fieldMeasure (allSignedRates N L E mask)) := by
  have hr := hasLaw_reindexedPoisson (allSignedRates N L E mask) (signFirstEquiv N E)
  have hc := hasLaw_column_sums (fun i : F₂ × ExactMarkIndex N E =>
    allSignedRates N L E mask ((signFirstEquiv N E).symm i)) (fun _ => Finset.univ)
  have hh := hc.fun_comp hr
  have heq : (fun i : ExactMarkIndex N E => ∑ s : F₂,
      allSignedRates N L E mask ((signFirstEquiv N E).symm (s,i))) = allExactRates N L E mask := by
    funext i
    exact sum_signedRates_eq_exact N L E mask i
  rw [heq] at hh
  exact hh

theorem pushforward_signed_target (N L E : ℕ) (mask : Finset ℕ) :
    pushforwardMass (forgetSigns N E) (poissonFieldMass (allSignedRates N L E mask)) =
      poissonFieldMass (allExactRates N L E mask) := by
  rw [pushforward_poissonFieldMass_of_hasLaw _ _ _ (hasLaw_forgetSigns N L E mask)]
  exact funext (fieldMeasure_real_singleton _)

/-- The literal unsigned exact field in the infinite source. -/
def infiniteExactField (N L E : ℕ) (mask : Finset ℕ) (omega : InfiniteSample)
    (i : ExactMarkIndex N E) : ℕ :=
  if i.1.val ∈ mask then exactMarkValue (infiniteValueBit omega) i.1.val L i.2.val else 0

def infiniteExactLaw (N L E : ℕ) (mask : Finset ℕ) (k : ExactMarkIndex N E → ℕ) : ℝ :=
  (infiniteRademacherMeasure {omega | infiniteExactField N L E mask omega = k}).toReal

def sourceConditionalExactLaw (C N L E Y : ℕ) (mask : Finset ℕ) (sigma : SmallSample C Y)
    (k : ExactMarkIndex N E → ℕ) : ℝ :=
  (infiniteRademacherMeasure
    ({omega | infiniteExactField N L E mask omega = k} ∩ infiniteSmallPrimeAtom C Y sigma)).toReal /
      (infiniteRademacherMeasure (infiniteSmallPrimeAtom C Y sigma)).toReal

theorem forgetSigns_infiniteSignedField (N L E : ℕ) (mask : Finset ℕ) (omega : InfiniteSample) :
    forgetSigns N E (infiniteSignedField N L E mask omega) = infiniteExactField N L E mask omega := by
  funext i
  by_cases hi : i.1.val ∈ mask
  · simp only [forgetSigns,infiniteSignedField,hi,true_and,infiniteExactField,if_true]
    exact sum_signedMarkValue (infiniteValueBit omega) i.1.val L i.2.val
  · simp [forgetSigns,infiniteSignedField,infiniteExactField,hi]

/-- Every statistic of the actual signed field is an observable of the same adequate cylinder. -/
theorem signed_statistic_event_eq_preimage {C N L E : ℕ} {T : Type*}
    (hC : dyadicCutoff N (L+E+1) ≤ C) (mask : Finset ℕ)
    (f : (SignedMarkIndex N E → ℕ) → T) (k : T) :
    {omega | f (infiniteSignedField N L E mask omega) = k} =
      restrictToFinite C ⁻¹' {omega | f (cylinderSignedField C N L E mask omega) = k} := by
  ext omega
  simp only [Set.mem_setOf_eq,Set.mem_preimage,cylinderSignedField_restrict_eq hC mask]

theorem pushforward_infiniteSignedLaw {N L E : ℕ} {T : Type*} (mask : Finset ℕ)
    (f : (SignedMarkIndex N E → ℕ) → T) :
    pushforwardMass f (infiniteSignedLaw N L E mask) =
      fun k => (infiniteRademacherMeasure {omega | f (infiniteSignedField N L E mask omega) = k}).toReal := by
  rw [infiniteSignedLaw_eq_finiteFieldLaw (le_refl (dyadicCutoff N (L+E+1))) mask,
    pushforwardMass_finiteFieldLaw]
  funext k
  rw [signed_statistic_event_eq_preimage (le_refl (dyadicCutoff N (L+E+1))) mask f k,
    ← Measure.map_apply (measurable_restrictToFinite _) (Set.toFinite _ |>.measurableSet),
    map_infiniteRademacherMeasure_restrictToFinite,
    finiteRademacherMeasure_event_eq_uniformEventProbability,ENNReal.toReal_ofReal]
  · rw [finiteFieldLaw_eq_eventProbability,eventProbability_fullUniformPMF_eq,
      finiteUniformProbability_eq_uniformEventProbability]
  · apply Rat.cast_nonneg.mpr
    unfold uniformEventProbability
    positivity

theorem pushforward_conditionalSignedLaw {C N L E Y : ℕ} {T : Type*}
    (hC : dyadicCutoff N (L+E+1) ≤ C) (mask : Finset ℕ)
    (f : (SignedMarkIndex N E → ℕ) → T) (sigma : SmallSample C Y) :
    pushforwardMass f (conditionalSignedLaw C N L E Y mask sigma) =
      fun k => (infiniteRademacherMeasure
        ({omega | f (infiniteSignedField N L E mask omega) = k} ∩ infiniteSmallPrimeAtom C Y sigma)).toReal /
          (infiniteRademacherMeasure (infiniteSmallPrimeAtom C Y sigma)).toReal := by
  unfold conditionalSignedLaw
  rw [pushforwardMass_finiteFieldLaw]
  funext k
  rw [signed_statistic_event_eq_preimage hC mask f k]
  exact (finiteFieldLaw_eq_eventProbability _ _ _).trans
    (eventProbability_eq_infinite_atom_ratio C Y (fun omega => f (cylinderSignedField C N L E mask omega) = k) sigma)

theorem pushforward_signed_source (N L E : ℕ) (mask : Finset ℕ) :
    pushforwardMass (forgetSigns N E) (infiniteSignedLaw N L E mask) = infiniteExactLaw N L E mask := by
  rw [pushforward_infiniteSignedLaw]
  simp only [forgetSigns_infiniteSignedField]
  rfl

theorem pushforward_signed_source_conditional {C N L E Y : ℕ}
    (hC : dyadicCutoff N (L+E+1) ≤ C) (mask : Finset ℕ) (sigma : SmallSample C Y) :
    pushforwardMass (forgetSigns N E) (sourceConditionalSignedLaw C N L E Y mask sigma) =
      sourceConditionalExactLaw C N L E Y mask sigma := by
  rw [← conditionalSignedLaw_eq_source_ratio hC mask,pushforward_conditionalSignedLaw hC]
  simp only [forgetSigns_infiniteSignedField]
  rfl

theorem hasSum_infiniteExactLaw (N L E : ℕ) (mask : Finset ℕ) : HasSum (infiniteExactLaw N L E mask) 1 := by
  rw [← pushforward_signed_source]
  exact hasSum_pushforwardMass _ (hasSum_infiniteSignedLaw N L E mask)

/-- Forgetting signs contracts the genuine unconditional source-to-target distance with coefficient one. -/
theorem infinite_exact_distance_le_signed (N L E : ℕ) (mask : Finset ℕ) :
    massTotalVariation (infiniteExactLaw N L E mask) (poissonFieldMass (allExactRates N L E mask)) ≤
      massTotalVariation (infiniteSignedLaw N L E mask) (poissonFieldMass (allSignedRates N L E mask)) := by
  rw [← pushforward_signed_source,← pushforward_signed_target]
  exact massTotalVariation_pushforward_le _ (hasSum_infiniteSignedLaw N L E mask)
    (hasSum_poissonFieldMass _) (infiniteSignedLaw_nonneg N L E mask) (poissonFieldMass_nonneg _)

/-- The same coefficient-one contraction holds on each actual represented prime atom. -/
theorem conditional_exact_distance_le_signed {C N L E Y : ℕ}
    (hC : dyadicCutoff N (L+E+1) ≤ C) (mask : Finset ℕ) (sigma : SmallSample C Y) :
    massTotalVariation (sourceConditionalExactLaw C N L E Y mask sigma) (poissonFieldMass (allExactRates N L E mask)) ≤
      massTotalVariation (sourceConditionalSignedLaw C N L E Y mask sigma) (poissonFieldMass (allSignedRates N L E mask)) := by
  rw [← pushforward_signed_source_conditional hC mask,← pushforward_signed_target]
  apply massTotalVariation_pushforward_le _ (hasSum_sourceConditionalSignedLaw hC mask sigma)
    (hasSum_poissonFieldMass _) _ (poissonFieldMass_nonneg _)
  rw [← conditionalSignedLaw_eq_source_ratio hC mask]
  exact finiteFieldLaw_nonneg _ _

/-- Averaging the actual conditional contraction creates no factor in the number of marks. -/
theorem average_exact_distance_le_signed {C N L E Y : ℕ}
    (hC : dyadicCutoff N (L+E+1) ≤ C) (mask : Finset ℕ) :
    finiteUniformAverage (fun sigma : SmallSample C Y =>
      massTotalVariation (sourceConditionalExactLaw C N L E Y mask sigma) (poissonFieldMass (allExactRates N L E mask))) ≤
    finiteUniformAverage (fun sigma : SmallSample C Y =>
      massTotalVariation (sourceConditionalSignedLaw C N L E Y mask sigma) (poissonFieldMass (allSignedRates N L E mask))) := by
  unfold finiteUniformAverage
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Finset.sum_le_sum fun sigma _ => conditional_exact_distance_le_signed hC mask sigma

end
end PaperC.V282.ExactMarkedSignProjection
