import PaperCV282.ExactMarkedDependency
import PaperCV282.DictionaryFieldInfinite

/-!
# Exact marked fields under the actual infinite source law

C is any cylinder covering all marked values. When C also covers Y, the
conditioning atoms represent the whole F_Y, and all atoms have positive mass.
The source and conditional laws retain every site, excess and sign label.
-/
namespace PaperC.V282.ExactMarkedInfinite

open MeasureTheory Set InfiniteRademacher InfiniteCylinderTransfer InfiniteConditionalWords
open InfiniteExactLengthProbabilityTransfer InfiniteFieldTransfer InfiniteMaskedScalarTransfer
open ExactMarkedModel ExactMarkedDependency LabelledSupportGraph LabelledProcessCosts MixedLengthAffine
open ConditionalStartProbability ConditionalAGGAverage ConditionalAGGInstantiation
open ArratiaGoldsteinGordonInput SectionThirteenFiniteBound SectionThirteenCouplings
open FiniteFieldTotalVariation FiniteFieldPoissonCoupling ProcessAGGInput MaskedScalarFullConditioning

open scoped NNReal

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- Exact signed field evaluated in any finite prime cylinder. -/
def cylinderSignedField (C N L E : ℕ) (mask : Finset ℕ) (omega : SampleSpace C)
    (i : SignedMarkIndex N E) : ℕ :=
  if i.1.val ∈ mask ∧ SignedExactMark (valueBit omega) i.1.val L i.2.1.val i.2.2 then 1 else 0

def conditionalSignedLaw (C N L E Y : ℕ) (mask : Finset ℕ) (sigma : SmallSample C Y) :
    (SignedMarkIndex N E → ℕ) → ℝ :=
  finiteFieldLaw (largeUniformPMF C Y) (fun eta => cylinderSignedField C N L E mask (assemble C Y sigma eta))

/-- The literal source field, including the true absolute run sign. -/
def infiniteSignedField (N L E : ℕ) (mask : Finset ℕ) (omega : InfiniteSample)
    (i : SignedMarkIndex N E) : ℕ :=
  if i.1.val ∈ mask ∧ SignedExactMark (infiniteValueBit omega) i.1.val L i.2.1.val i.2.2 then 1 else 0

def infiniteSignedLaw (N L E : ℕ) (mask : Finset ℕ) (k : SignedMarkIndex N E → ℕ) : ℝ :=
  (infiniteRademacherMeasure {omega | infiniteSignedField N L E mask omega = k}).toReal

/-- Literal conditional source masses on the represented small-prime atoms. -/
def sourceConditionalSignedLaw (C N L E Y : ℕ) (mask : Finset ℕ) (sigma : SmallSample C Y)
    (k : SignedMarkIndex N E → ℕ) : ℝ :=
  (infiniteRademacherMeasure
    ({omega | infiniteSignedField N L E mask omega = k} ∩ infiniteSmallPrimeAtom C Y sigma)).toReal /
      (infiniteRademacherMeasure (infiniteSmallPrimeAtom C Y sigma)).toReal

/-- Source exact signed events are preserved by every adequate finite restriction. -/
theorem signedExactMark_restrictToFinite_iff {C x L e : ℕ} (hcut : x+(L+e) ≤ C)
    (s : F₂) (omega : InfiniteSample) :
    SignedExactMark (valueBit (restrictToFinite C omega)) x L e s ↔
      SignedExactMark (infiniteValueBit omega) x L e s := by
  unfold SignedExactMark
  have hq : x+(excessRowCount L e-1) ≤ C := by simpa only [excessRowCount,Nat.add_sub_cancel] using hcut
  have he := exactLengthAt_restrictToFinite_iff omega hq
  change (ExactLengthEvent (valueBit (restrictToFinite C omega)) x (excessRowCount L e) ↔ _) at he
  rw [he,valueBit_restrictToFinite_eq_infiniteValueBit omega (by omega)]

/-- The field used by finite process AGG is exactly the finite source field. -/
theorem indicatorField_conditionedSigned_eq (C N L E Y : ℕ) (mask : Finset ℕ)
    (sigma : SmallSample C Y) (eta : LargeSample C Y) :
    indicatorField (maskedLabelledFamily N (conditionedSignedAt C L E Y sigma) mask) eta =
      cylinderSignedField C N L E mask (assemble C Y sigma eta) := by
  funext i
  by_cases hi : i.1.val ∈ mask <;>
    simp [indicatorField,maskedLabelledFamily,maskedLabelIndicator,labelledFamily,conditionedSignedAt,signedAt,
      cylinderSignedField,hi]

theorem conditionalSignedLaw_eq_process_law (C N L E Y : ℕ) (mask : Finset ℕ) (sigma : SmallSample C Y) :
    conditionalSignedLaw C N L E Y mask sigma =
      finiteFieldLaw (largeUniformPMF C Y)
        (indicatorField (maskedLabelledFamily N (conditionedSignedAt C L E Y sigma) mask)) := by
  unfold conditionalSignedLaw
  congr 1
  funext eta
  exact (indicatorField_conditionedSigned_eq C N L E Y mask sigma eta).symm

/-- Every coordinate of the maximal marked support lies below the common cylinder cutoff. -/
theorem marked_coordinate_cutoff {C N L E : ℕ} (hC : dyadicCutoff N (L+E+1) ≤ C)
    (i : SignedMarkIndex N E) : i.1.val+(L+i.2.1.val) ≤ C := by
  have hx := Finset.mem_Ico.mp i.1.property
  have he := i.2.1.isLt
  unfold dyadicCutoff at hC
  omega

theorem cylinderSignedField_restrict_eq {C N L E : ℕ} (hC : dyadicCutoff N (L+E+1) ≤ C)
    (mask : Finset ℕ) (omega : InfiniteSample) :
    cylinderSignedField C N L E mask (restrictToFinite C omega) = infiniteSignedField N L E mask omega := by
  funext i
  simp only [cylinderSignedField,infiniteSignedField,
    signedExactMark_restrictToFinite_iff (marked_coordinate_cutoff hC i)]

theorem infiniteSignedField_event_eq_preimage {C N L E : ℕ} (hC : dyadicCutoff N (L+E+1) ≤ C)
    (mask : Finset ℕ) (k : SignedMarkIndex N E → ℕ) :
    {omega | infiniteSignedField N L E mask omega = k} =
      restrictToFinite C ⁻¹' {sigma | cylinderSignedField C N L E mask sigma = k} := by
  ext omega
  simp only [Set.mem_setOf_eq,Set.mem_preimage,cylinderSignedField_restrict_eq hC mask]

theorem measurableSet_infiniteSignedField_event (N L E : ℕ) (mask : Finset ℕ) (k : SignedMarkIndex N E → ℕ) :
    MeasurableSet {omega | infiniteSignedField N L E mask omega = k} := by
  rw [infiniteSignedField_event_eq_preimage (le_refl (dyadicCutoff N (L+E+1))) mask]
  exact (measurable_restrictToFinite _) (Set.toFinite _ |>.measurableSet)

/-- Actual conditional masses are exactly the finite laws, with their real atom denominators. -/
theorem conditionalSignedLaw_eq_source_ratio {C N L E Y : ℕ} (hC : dyadicCutoff N (L+E+1) ≤ C)
    (mask : Finset ℕ) (sigma : SmallSample C Y) :
    conditionalSignedLaw C N L E Y mask sigma = sourceConditionalSignedLaw C N L E Y mask sigma := by
  funext k
  unfold sourceConditionalSignedLaw
  rw [infiniteSignedField_event_eq_preimage hC mask]
  exact (finiteFieldLaw_eq_eventProbability _ _ _).trans
    (eventProbability_eq_infinite_atom_ratio C Y (fun omega => cylinderSignedField C N L E mask omega = k) sigma)

/-- The actual unconditional source field has the complete finite-cylinder law. -/
theorem infiniteSignedLaw_eq_finiteFieldLaw {C N L E : ℕ} (hC : dyadicCutoff N (L+E+1) ≤ C)
    (mask : Finset ℕ) :
    infiniteSignedLaw N L E mask = finiteFieldLaw (fullUniformPMF C) (cylinderSignedField C N L E mask) := by
  funext k
  unfold infiniteSignedLaw
  rw [infiniteSignedField_event_eq_preimage hC mask,
    ← Measure.map_apply (measurable_restrictToFinite C) (Set.toFinite _ |>.measurableSet),
    map_infiniteRademacherMeasure_restrictToFinite,
    finiteRademacherMeasure_event_eq_uniformEventProbability,ENNReal.toReal_ofReal]
  · rw [finiteFieldLaw_eq_eventProbability,eventProbability_fullUniformPMF_eq,
      finiteUniformProbability_eq_uniformEventProbability]
  · apply Rat.cast_nonneg.mpr
    unfold uniformEventProbability
    positivity

theorem hasSum_infiniteSignedLaw (N L E : ℕ) (mask : Finset ℕ) : HasSum (infiniteSignedLaw N L E mask) 1 := by
  rw [infiniteSignedLaw_eq_finiteFieldLaw (le_refl (dyadicCutoff N (L+E+1))) mask]
  exact hasSum_finiteFieldLaw _ _

theorem infiniteSignedLaw_nonneg (N L E : ℕ) (mask : Finset ℕ) (k : SignedMarkIndex N E → ℕ) :
    0 ≤ infiniteSignedLaw N L E mask k := ENNReal.toReal_nonneg

theorem hasSum_sourceConditionalSignedLaw {C N L E Y : ℕ} (hC : dyadicCutoff N (L+E+1) ≤ C)
    (mask : Finset ℕ) (sigma : SmallSample C Y) : HasSum (sourceConditionalSignedLaw C N L E Y mask sigma) 1 := by
  rw [← conditionalSignedLaw_eq_source_ratio hC mask]
  exact hasSum_finiteFieldLaw _ _

/-- The unconditional source law is the exact uniform mixture of the conditional cylinder laws. -/
theorem infiniteSignedLaw_eq_uniformMixture {C N L E : ℕ} (Y : ℕ)
    (hC : dyadicCutoff N (L+E+1) ≤ C) (mask : Finset ℕ) :
    infiniteSignedLaw N L E mask = fun k => uniformAverage
      (fun sigma : SmallSample C Y => conditionalSignedLaw C N L E Y mask sigma k) := by
  rw [infiniteSignedLaw_eq_finiteFieldLaw hC mask]
  funext k
  have h := finiteUniformAverage_largeEventProbability_eq_full C Y
    (fun omega => cylinderSignedField C N L E mask omega = k)
  rw [← finiteUniformProbability_eq_uniformEventProbability,← eventProbability_fullUniformPMF_eq] at h
  simp only [conditionalSignedLaw,finiteFieldLaw_eq_eventProbability]
  exact h.symm

/-- No represented conditioning atom is null. -/
theorem signed_conditioning_atom_real_pos (C Y : ℕ) (sigma : SmallSample C Y) :
    0 < (infiniteRademacherMeasure (infiniteSmallPrimeAtom C Y sigma)).toReal := by
  rw [conditioningAtoms_equiprobable,ENNReal.toReal_ofReal (by positivity)]
  positivity

/-- With C covering Y these are exactly the atoms of the full prime sigma-algebra F_Y. -/
theorem signed_fullFY_identification {C N L E Y : ℕ} (hC : dyadicCutoff N (L+E+1) ≤ C)
    (hYC : Y ≤ C) (mask : Finset ℕ) :
    smallPrimeSigmaAlgebra C Y = MeasurableSpace.comap (restrictToFinite Y) inferInstance ∧
      ∀ sigma : SmallSample C Y,
        0 < (infiniteRademacherMeasure (infiniteSmallPrimeAtom C Y sigma)).toReal ∧
        conditionalSignedLaw C N L E Y mask sigma = sourceConditionalSignedLaw C N L E Y mask sigma := by
  exact ⟨smallPrimeSigmaAlgebra_eq_primeCylinder hYC,fun sigma =>
    ⟨signed_conditioning_atom_real_pos C Y sigma,conditionalSignedLaw_eq_source_ratio hC mask sigma⟩⟩

/-- Mean conditional TV is literally the mean of true source atom-ratio distances. -/
theorem average_signed_source_ratio_eq {C N L E Y : ℕ} (hC : dyadicCutoff N (L+E+1) ≤ C)
    (mask : Finset ℕ) (target : (SignedMarkIndex N E → ℕ) → ℝ) :
    finiteUniformAverage (fun sigma : SmallSample C Y =>
      massTotalVariation (sourceConditionalSignedLaw C N L E Y mask sigma) target) =
    finiteUniformAverage (fun sigma : SmallSample C Y =>
      massTotalVariation (finiteFieldLaw (largeUniformPMF C Y)
        (indicatorField (maskedLabelledFamily N (conditionedSignedAt C L E Y sigma) mask))) target) := by
  simp_rw [← conditionalSignedLaw_eq_source_ratio hC mask,conditionalSignedLaw_eq_process_law]

/-- Mixture contraction for any specified product Poisson rate on the full marked carrier. -/
theorem infiniteSignedLaw_distance_le_average {C N L E : ℕ} (Y : ℕ)
    (hC : dyadicCutoff N (L+E+1) ≤ C) (mask : Finset ℕ) (rate : SignedMarkIndex N E → ℝ≥0) :
    massTotalVariation (infiniteSignedLaw N L E mask) (poissonFieldMass rate) ≤
      finiteUniformAverage (fun sigma : SmallSample C Y =>
        massTotalVariation (sourceConditionalSignedLaw C N L E Y mask sigma) (poissonFieldMass rate)) := by
  rw [infiniteSignedLaw_eq_uniformMixture Y hC mask]
  simp_rw [← conditionalSignedLaw_eq_source_ratio hC mask]
  exact massTotalVariation_uniformMixture_le _ _ (fun sigma =>
    summable_abs_sub_of_nonneg (summable_finiteFieldLaw _ _) (summable_poissonFieldMass _)
      (finiteFieldLaw_nonneg _ _) (poissonFieldMass_nonneg _))

end
end PaperC.V282.ExactMarkedInfinite
