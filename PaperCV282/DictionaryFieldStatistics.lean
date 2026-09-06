import PaperCV282.DictionaryFieldInfinite
import PaperCV282.MassPushforward

/-!
# Actual deterministic statistics and restrictions of the word field

The image mass is identified with the true source event before applying
contraction. The codomain can be any type: the source field has finite
support, so every such event is a measurable finite-cylinder event.
This is not a general stable-product lifting theorem.
-/

namespace PaperC.V282.DictionaryFieldStatistics

open MeasureTheory Set InfiniteRademacher InfiniteCylinderTransfer InfiniteConditionalWords
open InfiniteWordTransfer InfiniteFieldTransfer InfiniteExactLengthProbabilityTransfer
open DictionaryFieldModel DictionaryFieldTransfer DictionaryFieldInfinite
open ConditionalStartProbability ConditionalAGGInstantiation ConditionalAGGAverage
open ArratiaGoldsteinGordonInput SectionThirteenCouplings SectionThirteenFiniteBound
open ConditionalDependencyGraph InfiniteMaskedScalarTransfer
open FiniteFieldTotalVariation FiniteFieldPoissonCoupling MassPushforward

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

/-- The entire actual field is preserved by an adequate prime restriction. -/
theorem cylinderDictionaryField_restrict_eq {C N L : ℕ}
    (W : Finset (Fin (L+1) → F₂)) (hcut : dyadicCutoff N L ≤ C)
    (omega : InfiniteSample) :
    cylinderDictionaryField C N L W (restrictToFinite C omega) =
      infiniteDictionaryField N L W omega := by
  funext i
  have h := finiteWordEvent_restrictToFinite_iff
    ((dictionary_vertex_cutoff N L i.1).trans (Nat.add_le_add_right hcut 1)) i.2.val omega
  simp only [cylinderDictionaryField,infiniteDictionaryField]
  by_cases hf : restrictToFinite C omega ∈ finiteWordEvent C i.1.val (L+1) i.2.val
  · simp only [if_pos hf, if_pos (h.mp hf)]
  · have hi : omega ∉ infiniteWordEvent i.1.val (L+1) i.2.val := fun hi => hf (h.mpr hi)
    simp only [if_neg hf, if_neg hi]

/-- Every deterministic statistic uses the same genuine finite-cylinder event. -/
theorem statistic_event_eq_preimage {C N L : ℕ} {T : Type*}
    (W : Finset (Fin (L+1) → F₂)) (hcut : dyadicCutoff N L ≤ C)
    (f : (DictionaryIndex N L W → ℕ) → T) (b : T) :
    {omega | f (infiniteDictionaryField N L W omega) = b} =
      restrictToFinite C ⁻¹' {omega | f (cylinderDictionaryField C N L W omega) = b} := by
  ext omega
  simp only [Set.mem_setOf_eq,Set.mem_preimage,cylinderDictionaryField_restrict_eq W hcut]

theorem measurableSet_statistic_event {N L : ℕ} {T : Type*}
    (W : Finset (Fin (L+1) → F₂))
    (f : (DictionaryIndex N L W → ℕ) → T) (b : T) :
    MeasurableSet {omega | f (infiniteDictionaryField N L W omega) = b} := by
  rw [statistic_event_eq_preimage W (le_refl (dyadicCutoff N L)) f b]
  exact (measurable_restrictToFinite _) (Set.toFinite _ |>.measurableSet)

/-- A finite-source statistic has exactly the probability of the corresponding source event. -/
theorem finite_statistic_probability_eq_source {C N L : ℕ} {T : Type*}
    (W : Finset (Fin (L+1) → F₂)) (hcut : dyadicCutoff N L ≤ C)
    (f : (DictionaryIndex N L W → ℕ) → T) (b : T) :
    finiteFieldLaw (fullUniformPMF C) (fun omega => f (cylinderDictionaryField C N L W omega)) b =
      (infiniteRademacherMeasure {omega | f (infiniteDictionaryField N L W omega) = b}).toReal := by
  classical
  rw [statistic_event_eq_preimage W hcut f b,
    ← Measure.map_apply (measurable_restrictToFinite C) (Set.toFinite _ |>.measurableSet),
    map_infiniteRademacherMeasure_restrictToFinite,
    finiteRademacherMeasure_event_eq_uniformEventProbability, ENNReal.toReal_ofReal]
  · rw [finiteFieldLaw_eq_eventProbability,eventProbability_fullUniformPMF_eq,
      finiteUniformProbability_eq_uniformEventProbability]
  · apply Rat.cast_nonneg.mpr
    unfold uniformEventProbability
    positivity

/-- The pushforward of the true source law is the true law of the composed statistic. -/
theorem pushforward_infiniteDictionaryLaw_eq {N L : ℕ} {T : Type*}
    (W : Finset (Fin (L+1) → F₂)) (f : (DictionaryIndex N L W → ℕ) → T) :
    pushforwardMass f (infiniteDictionaryLaw N L W) =
      fun b => (infiniteRademacherMeasure
        {omega | f (infiniteDictionaryField N L W omega) = b}).toReal := by
  rw [infiniteDictionaryLaw_eq_finiteFieldLaw W (le_refl (dyadicCutoff N L)),
    pushforwardMass_finiteFieldLaw]
  funext b
  exact finite_statistic_probability_eq_source W (le_refl _) f b

/-- Conditional pushforward is exactly the actual ratio on each represented prime atom. -/
theorem pushforward_conditionalDictionaryLaw_eq_atom_ratio {C N L Y : ℕ} {T : Type*}
    (W : Finset (Fin (L+1) → F₂)) (hcut : dyadicCutoff N L ≤ C)
    (f : (DictionaryIndex N L W → ℕ) → T) (sigma : SmallSample C Y) :
    pushforwardMass f (conditionalDictionaryLaw C N L Y W sigma) =
      fun b => (infiniteRademacherMeasure
        ({omega | f (infiniteDictionaryField N L W omega) = b} ∩
          infiniteSmallPrimeAtom C Y sigma)).toReal /
        (infiniteRademacherMeasure (infiniteSmallPrimeAtom C Y sigma)).toReal := by
  unfold conditionalDictionaryLaw
  rw [pushforwardMass_finiteFieldLaw]
  funext b
  rw [statistic_event_eq_preimage W hcut f b]
  exact (finiteFieldLaw_eq_eventProbability _ _ _).trans
    (eventProbability_eq_infinite_atom_ratio C Y
      (fun omega => f (cylinderDictionaryField C N L W omega) = b) sigma)

/-- An adequate cylinder containing Y represents the entire prime sigma-algebra. -/
theorem full_FY_statistic_representation {C N L Y : ℕ} {T : Type*}
    (W : Finset (Fin (L+1) → F₂)) (hcut : dyadicCutoff N L ≤ C) (hY : Y ≤ C)
    (f : (DictionaryIndex N L W → ℕ) → T) :
    smallPrimeSigmaAlgebra C Y = MeasurableSpace.comap (restrictToFinite Y) inferInstance ∧
    ∀ sigma : SmallSample C Y,
      pushforwardMass f (conditionalDictionaryLaw C N L Y W sigma) =
        fun b => (infiniteRademacherMeasure
          ({omega | f (infiniteDictionaryField N L W omega) = b} ∩
            infiniteSmallPrimeAtom C Y sigma)).toReal /
          (infiniteRademacherMeasure (infiniteSmallPrimeAtom C Y sigma)).toReal := by
  exact ⟨smallPrimeSigmaAlgebra_eq_primeCylinder hY,
    fun sigma => pushforward_conditionalDictionaryLaw_eq_atom_ratio W hcut f sigma⟩

/-- Deterministic source statistics contract against the image of the same Poisson field. -/
theorem infinite_statistic_distance_le {N L : ℕ} {T : Type*}
    (W : Finset (Fin (L+1) → F₂)) (f : (DictionaryIndex N L W → ℕ) → T) :
    massTotalVariation
      (fun b => (infiniteRademacherMeasure
        {omega | f (infiniteDictionaryField N L W omega) = b}).toReal)
      (pushforwardMass f (poissonFieldMass (allWordRates N L W (dyadicBlock N)))) ≤
        dictionaryDistance N L W := by
  rw [← pushforward_infiniteDictionaryLaw_eq W f]
  exact massTotalVariation_pushforward_le f (hasSum_infiniteDictionaryLaw N L W)
    (hasSum_poissonFieldMass _) (infiniteDictionaryLaw_nonneg N L W) (poissonFieldMass_nonneg _)

/-- The finite conditional statistic bound uses the true composed finite field. -/
theorem conditional_statistic_distance_le {C N L Y : ℕ} {T : Type*}
    (W : Finset (Fin (L+1) → F₂)) (f : (DictionaryIndex N L W → ℕ) → T)
    (sigma : SmallSample C Y) :
    massTotalVariation
      (pushforwardMass f (conditionalDictionaryLaw C N L Y W sigma))
      (pushforwardMass f (poissonFieldMass (allWordRates N L W (dyadicBlock N)))) ≤
      massTotalVariation (conditionalDictionaryLaw C N L Y W sigma)
        (poissonFieldMass (allWordRates N L W (dyadicBlock N))) := by
  unfold conditionalDictionaryLaw
  rw [pushforwardMass_finiteFieldLaw]
  exact finiteFieldLaw_statistic_bound _ _ f (hasSum_poissonFieldMass _)
    (poissonFieldMass_nonneg _) (le_refl _)

/-- The same bound on literal conditional source ratios. -/
theorem conditional_source_statistic_distance_le {C N L Y : ℕ} {T : Type*}
    (W : Finset (Fin (L+1) → F₂)) (hcut : dyadicCutoff N L ≤ C)
    (f : (DictionaryIndex N L W → ℕ) → T) (sigma : SmallSample C Y) :
    massTotalVariation
      (fun b => (infiniteRademacherMeasure
        ({omega | f (infiniteDictionaryField N L W omega) = b} ∩
          infiniteSmallPrimeAtom C Y sigma)).toReal /
        (infiniteRademacherMeasure (infiniteSmallPrimeAtom C Y sigma)).toReal)
      (pushforwardMass f (poissonFieldMass (allWordRates N L W (dyadicBlock N)))) ≤
      massTotalVariation (conditionalDictionaryLaw C N L Y W sigma)
        (poissonFieldMass (allWordRates N L W (dyadicBlock N))) := by
  rw [← pushforward_conditionalDictionaryLaw_eq_atom_ratio W hcut f sigma]
  exact conditional_statistic_distance_le W f sigma

/-- Averaging the actual source-atom statistic distances does not increase the field error. -/
theorem average_source_statistic_distance_le {N L Y : ℕ} {T : Type*}
    (W : Finset (Fin (L+1) → F₂)) (f : (DictionaryIndex N L W → ℕ) → T) :
    finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
      massTotalVariation
        (fun b => (infiniteRademacherMeasure
          ({omega | f (infiniteDictionaryField N L W omega) = b} ∩
            infiniteSmallPrimeAtom (dyadicCutoff N L) Y sigma)).toReal /
          (infiniteRademacherMeasure (infiniteSmallPrimeAtom (dyadicCutoff N L) Y sigma)).toReal)
        (pushforwardMass f (poissonFieldMass (allWordRates N L W (dyadicBlock N))))) ≤
      dictionaryConditionalDistance N L Y W := by
  exact finiteUniformAverage_mono (fun sigma =>
    conditional_source_statistic_distance_le W (le_refl _) f sigma)

/-- The actual unconditional statistic also receives the mean conditional bound. -/
theorem infinite_statistic_distance_le_conditional {N L Y : ℕ} {T : Type*}
    (W : Finset (Fin (L+1) → F₂)) (f : (DictionaryIndex N L W → ℕ) → T) :
    massTotalVariation
      (fun b => (infiniteRademacherMeasure
        {omega | f (infiniteDictionaryField N L W omega) = b}).toReal)
      (pushforwardMass f (poissonFieldMass (allWordRates N L W (dyadicBlock N)))) ≤
      dictionaryConditionalDistance N L Y W :=
  (infinite_statistic_distance_le W f).trans (dictionaryDistance_le_conditionalDistance N L Y W)

/-- The displayed actual source statistic law has total mass one. -/
theorem hasSum_source_statistic_law {N L : ℕ} {T : Type*}
    (W : Finset (Fin (L+1) → F₂)) (f : (DictionaryIndex N L W → ℕ) → T) :
    HasSum (fun b => (infiniteRademacherMeasure
      {omega | f (infiniteDictionaryField N L W omega) = b}).toReal) 1 := by
  rw [← pushforward_infiniteDictionaryLaw_eq W f]
  exact hasSum_pushforwardMass f (hasSum_infiniteDictionaryLaw N L W)

/-- Each displayed conditional source statistic law has total mass one. -/
theorem hasSum_conditional_source_statistic_law {C N L Y : ℕ} {T : Type*}
    (W : Finset (Fin (L+1) → F₂)) (hcut : dyadicCutoff N L ≤ C)
    (f : (DictionaryIndex N L W → ℕ) → T) (sigma : SmallSample C Y) :
    HasSum (fun b => (infiniteRademacherMeasure
      ({omega | f (infiniteDictionaryField N L W omega) = b} ∩
        infiniteSmallPrimeAtom C Y sigma)).toReal /
      (infiniteRademacherMeasure (infiniteSmallPrimeAtom C Y sigma)).toReal) 1 := by
  rw [← pushforward_conditionalDictionaryLaw_eq_atom_ratio W hcut f sigma]
  exact hasSum_pushforwardMass f (hasSum_finiteFieldLaw _ _)

end
end PaperC.V282.DictionaryFieldStatistics
