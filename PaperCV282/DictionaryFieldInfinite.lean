import PaperCV282.DictionaryFieldTransfer
import PaperCV282.InfiniteFieldTransfer
import PaperCV282.MassPushforward

/-!
# The full dictionary field in the infinite multiplicative source

Every site and prescribed word remains a separate coordinate. Conditional
masses are literal ratios on positive small-prime atoms. An adequate
cylinder contains every bit, so the finite law is exactly the source law.
-/

namespace PaperC.V282.DictionaryFieldInfinite

open MeasureTheory Set InfiniteRademacher InfiniteCylinderTransfer InfiniteConditionalWords
open InfiniteWordTransfer InfiniteFieldTransfer InfiniteExactLengthProbabilityTransfer
open DictionaryFieldModel DictionaryFieldTransfer SectionTwelveMoments
open ConditionalStartProbability ConditionalAGGAverage ArratiaGoldsteinGordonInput
open ConditionalAGGInstantiation ConditionalDependencyGraph SectionThirteenCouplings
open InfiniteMaskedScalarTransfer
open SectionThirteenFiniteBound FiniteFieldTotalVariation FiniteFieldPoissonCoupling
open ProcessAGGInput MassPushforward

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

def cylinderDictionaryField (C N L : ℕ) (W : Finset (Fin (L+1) → F₂))
    (omega : SampleSpace C) (i : DictionaryIndex N L W) : ℕ :=
  if omega ∈ finiteWordEvent C i.1.val (L+1) i.2.val then 1 else 0

def conditionalDictionaryLaw (C N L Y : ℕ) (W : Finset (Fin (L+1) → F₂))
    (sigma : SmallSample C Y) : (DictionaryIndex N L W → ℕ) → ℝ :=
  finiteFieldLaw (largeUniformPMF C Y)
    (fun eta => cylinderDictionaryField C N L W (assemble C Y sigma eta))

def infiniteDictionaryField (N L : ℕ) (W : Finset (Fin (L+1) → F₂))
    (omega : InfiniteSample) (i : DictionaryIndex N L W) : ℕ :=
  if omega ∈ infiniteWordEvent i.1.val (L+1) i.2.val then 1 else 0

def infiniteDictionaryLaw (N L : ℕ) (W : Finset (Fin (L+1) → F₂))
    (k : DictionaryIndex N L W → ℕ) : ℝ :=
  (infiniteRademacherMeasure {omega | infiniteDictionaryField N L W omega = k}).toReal

theorem dictionary_vertex_cutoff (N L : ℕ) (x : {x : ℕ // x ∈ dyadicBlock N}) :
    x.val - 1 + (L+1) ≤ dyadicCutoff N L + 1 := by
  have hx := Finset.mem_Ico.mp x.property
  unfold dyadicCutoff
  omega

theorem conditionalDictionaryLaw_at_dyadic (N L Y : ℕ) (W : Finset (Fin (L+1) → F₂))
    (sigma : SmallSample (dyadicCutoff N L) Y) :
    conditionalDictionaryLaw (dyadicCutoff N L) N L Y W sigma =
      finiteFieldLaw (largeUniformPMF (dyadicCutoff N L) Y)
        (indicatorField (maskedWordIndicator N L Y W (dyadicBlock N) sigma)) := by
  unfold conditionalDictionaryLaw
  congr 1
  funext eta i
  simp [cylinderDictionaryField,indicatorField,maskedWordIndicator,
    conditionedWordIndicator,finiteWordIndicator,i.1.property]

theorem infiniteDictionaryField_event_eq_preimage {C N L : ℕ}
    (W : Finset (Fin (L+1) → F₂)) (hcut : dyadicCutoff N L ≤ C)
    (k : DictionaryIndex N L W → ℕ) :
    {omega | infiniteDictionaryField N L W omega = k} =
      restrictToFinite C ⁻¹' {sigma | cylinderDictionaryField C N L W sigma = k} := by
  have heq (omega : InfiniteSample) :
      cylinderDictionaryField C N L W (restrictToFinite C omega) = infiniteDictionaryField N L W omega := by
    funext i
    have h := finiteWordEvent_restrictToFinite_iff
      ((dictionary_vertex_cutoff N L i.1).trans (Nat.add_le_add_right hcut 1)) i.2.val omega
    simp only [cylinderDictionaryField,infiniteDictionaryField,h]
  ext omega
  simp only [Set.mem_setOf_eq,Set.mem_preimage,heq]

theorem measurableSet_infiniteDictionaryField_event {C N L : ℕ}
    (W : Finset (Fin (L+1) → F₂)) (hcut : dyadicCutoff N L ≤ C)
    (k : DictionaryIndex N L W → ℕ) :
    MeasurableSet {omega | infiniteDictionaryField N L W omega = k} := by
  rw [infiniteDictionaryField_event_eq_preimage W hcut]
  exact (measurable_restrictToFinite _) (Set.toFinite _ |>.measurableSet)

theorem conditionalDictionaryLaw_eq_infinite_atom_ratio {C N L Y : ℕ}
    (W : Finset (Fin (L+1) → F₂)) (hcut : dyadicCutoff N L ≤ C)
    (sigma : SmallSample C Y) (k : DictionaryIndex N L W → ℕ) :
    conditionalDictionaryLaw C N L Y W sigma k =
      (infiniteRademacherMeasure
        ({omega | infiniteDictionaryField N L W omega = k} ∩ infiniteSmallPrimeAtom C Y sigma)).toReal /
      (infiniteRademacherMeasure (infiniteSmallPrimeAtom C Y sigma)).toReal := by
  rw [infiniteDictionaryField_event_eq_preimage W hcut k]
  exact (finiteFieldLaw_eq_eventProbability _ _ _).trans
    (eventProbability_eq_infinite_atom_ratio C Y (fun omega => cylinderDictionaryField C N L W omega = k) sigma)

theorem infiniteDictionaryLaw_eq_finiteFieldLaw {C N L : ℕ}
    (W : Finset (Fin (L+1) → F₂)) (hcut : dyadicCutoff N L ≤ C) :
    infiniteDictionaryLaw N L W = finiteFieldLaw (fullUniformPMF C) (cylinderDictionaryField C N L W) := by
  funext k
  unfold infiniteDictionaryLaw
  rw [infiniteDictionaryField_event_eq_preimage W hcut k,
    ← Measure.map_apply (measurable_restrictToFinite C) (Set.toFinite _ |>.measurableSet),
    map_infiniteRademacherMeasure_restrictToFinite,
    finiteRademacherMeasure_event_eq_uniformEventProbability, ENNReal.toReal_ofReal]
  · rw [finiteFieldLaw_eq_eventProbability,eventProbability_fullUniformPMF_eq,
      finiteUniformProbability_eq_uniformEventProbability]
  · apply Rat.cast_nonneg.mpr
    unfold uniformEventProbability
    positivity

theorem hasSum_infiniteDictionaryLaw (N L : ℕ) (W : Finset (Fin (L+1) → F₂)) :
    HasSum (infiniteDictionaryLaw N L W) 1 := by
  rw [infiniteDictionaryLaw_eq_finiteFieldLaw W (le_refl _)]
  exact hasSum_finiteFieldLaw _ _

theorem infiniteDictionaryLaw_nonneg (N L : ℕ) (W : Finset (Fin (L+1) → F₂))
    (k : DictionaryIndex N L W → ℕ) : 0 ≤ infiniteDictionaryLaw N L W k := ENNReal.toReal_nonneg

theorem cylinderDictionaryLaw_eq_uniformMixture (C N L Y : ℕ) (W : Finset (Fin (L+1) → F₂)) :
    finiteFieldLaw (fullUniformPMF C) (cylinderDictionaryField C N L W) =
      fun k => uniformAverage (fun sigma : SmallSample C Y => conditionalDictionaryLaw C N L Y W sigma k) := by
  funext k
  have h := finiteUniformAverage_largeEventProbability_eq_full C Y
    (fun omega => cylinderDictionaryField C N L W omega = k)
  rw [← finiteUniformProbability_eq_uniformEventProbability, ← eventProbability_fullUniformPMF_eq] at h
  simp only [conditionalDictionaryLaw,finiteFieldLaw_eq_eventProbability]
  exact h.symm

/-- Mean conditional total variation on the exact finite prime cylinder. -/
def dictionaryConditionalDistance (N L Y : ℕ) (W : Finset (Fin (L+1) → F₂)) : ℝ :=
  finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
    massTotalVariation (conditionalDictionaryLaw (dyadicCutoff N L) N L Y W sigma)
      (poissonFieldMass (allWordRates N L W (dyadicBlock N))))

def dictionaryDistance (N L : ℕ) (W : Finset (Fin (L+1) → F₂)) : ℝ :=
  massTotalVariation (infiniteDictionaryLaw N L W) (poissonFieldMass (allWordRates N L W (dyadicBlock N)))

theorem dictionaryDistance_nonneg (N L : ℕ) (W : Finset (Fin (L+1) → F₂)) :
    0 ≤ dictionaryDistance N L W := massTotalVariation_nonneg _ _

theorem dictionaryConditionalDistance_nonneg (N L Y : ℕ) (W : Finset (Fin (L+1) → F₂)) :
    0 ≤ dictionaryConditionalDistance N L Y W := by
  unfold dictionaryConditionalDistance finiteUniformAverage
  exact div_nonneg (Finset.sum_nonneg fun _ _ => massTotalVariation_nonneg _ _) (by positivity)

theorem dictionaryDistance_le_conditionalDistance (N L Y : ℕ) (W : Finset (Fin (L+1) → F₂)) :
    dictionaryDistance N L W ≤ dictionaryConditionalDistance N L Y W := by
  unfold dictionaryDistance
  rw [infiniteDictionaryLaw_eq_finiteFieldLaw W (le_refl _),
    cylinderDictionaryLaw_eq_uniformMixture (dyadicCutoff N L) N L Y W]
  exact massTotalVariation_uniformMixture_le _ _
    (fun sigma => summable_abs_sub_of_nonneg (summable_finiteFieldLaw _ _)
      (summable_poissonFieldMass _) (finiteFieldLaw_nonneg _ _) (poissonFieldMass_nonneg _))

end
end PaperC.V282.DictionaryFieldInfinite
