import PaperCV282.ConditionedCountableLaw
import PaperCV282.RestrictedPoissonTransfer

/-!
# Positive arithmetic conditioning events for arbitrary countable fields

The selected event is an actual union of equiprobable small-prime atoms.
The comparison therefore costs exactly the inverse source probability,
including for the full spatial marked configuration.
-/
namespace PaperC.V282.CountablePrimeEventTransfer

open MeasureTheory Set InfiniteRademacher InfiniteCylinderTransfer InfiniteConditionalWords
open PrimeFieldEventConditioning RestrictedPoissonTransfer ConditionedCountableLaw
open InfiniteMassCoupling FiniteFieldTotalVariation ConditionalStartProbability

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

def meanAtomDistance {α : Type*} (C Y : ℕ) (f : InfiniteSample → α) (q : α → ℝ) : ℝ :=
  uniformAverage (fun sigma : SmallSample C Y =>
    massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure
      (infiniteSmallPrimeAtom C Y sigma) f) q)

theorem meanAtomDistance_nonneg {α : Type*} (C Y : ℕ) (f : InfiniteSample → α) (q : α → ℝ) :
    0 ≤ meanAtomDistance C Y f q := by
  unfold meanAtomDistance uniformAverage
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => massTotalVariation_nonneg _ _)) (by positivity)

/-- The actual conditional field law is the uniform mixture over the selected atoms. -/
theorem conditional_law_selected_average {α : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (C Y : ℕ) (S : Finset (SmallSample C Y)) (hS : S.Nonempty)
    {f : InfiniteSample → α} (hf : Measurable f) :
    conditionalObservableLaw infiniteRademacherMeasure (primeFieldEvent C Y S) f =
      fun a => uniformAverage (fun sigma : {sigma // sigma ∈ S} =>
        conditionalObservableLaw infiniteRademacherMeasure (infiniteSmallPrimeAtom C Y sigma.val) f a) := by
  classical
  funext a
  rw [conditionalObservableLaw_eq_ratio _ _ (measurableSet_primeFieldEvent C Y S)]
  have hfiber : MeasurableSet {ω | f ω=a} := hf (measurableSet_singleton a)
  rw [source_event_ratio_eq_atom_average C Y S hS {ω | f ω=a} hfiber]
  simp_rw [conditionalObservableLaw_eq_ratio _ _ (measurableSet_infiniteSmallPrimeAtom C Y _)]
  rw [uniformAverage,Fintype.card_coe]
  congr 1
  exact (Finset.sum_subtype S (fun _ => Iff.rfl)
    (fun sigma => infiniteRademacherMeasure.real ({ω | f ω=a} ∩ infiniteSmallPrimeAtom C Y sigma) /
      infiniteRademacherMeasure.real (infiniteSmallPrimeAtom C Y sigma)))

set_option maxHeartbeats 800000 in
theorem selected_field_tv_le_mean_div_probability {α : Type*}
    [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (C Y : ℕ) (S : Finset (SmallSample C Y)) (hS : S.Nonempty)
    {f : InfiniteSample → α} (hf : Measurable f) {q : α → ℝ}
    (hq : HasSum q 1) (hq0 : ∀ a, 0 ≤ q a) :
    massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure (primeFieldEvent C Y S) f) q ≤
      meanAtomDistance C Y f q / infiniteRademacherMeasure.real (primeFieldEvent C Y S) := by
  obtain ⟨sigma,hsigma⟩ := hS
  letI : Nonempty {sigma // sigma ∈ S} := ⟨⟨sigma,hsigma⟩⟩
  rw [conditional_law_selected_average C Y S ⟨sigma,hsigma⟩ hf]
  have hpos (tau : SmallSample C Y) :
      0 < infiniteRademacherMeasure.real (infiniteSmallPrimeAtom C Y tau) :=
    ENNReal.toReal_pos (ne_of_gt (infiniteSmallPrimeAtom_measure_pos C Y tau))
      (infiniteSmallPrimeAtom_measure_ne_top C Y tau)
  have hsum (tau : {sigma // sigma ∈ S}) : HasSum
      (conditionalObservableLaw infiniteRademacherMeasure (infiniteSmallPrimeAtom C Y tau.val) f) 1 :=
    hasSum_conditionalObservableLaw infiniteRademacherMeasure _ (hpos tau.val) hf
  apply (massTotalVariation_uniformMixture_le
    (fun tau : {sigma // sigma ∈ S} => conditionalObservableLaw infiniteRademacherMeasure
      (infiniteSmallPrimeAtom C Y tau.val) f) q (fun tau =>
    summable_abs_sub_of_nonneg (hsum tau).summable hq.summable
      (conditionalObservableLaw_nonneg _ _ _) hq0)).trans
  have hsel := selected_average_le_average_div_probability C Y S ⟨sigma,hsigma⟩
    (fun tau => massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure
      (infiniteSmallPrimeAtom C Y tau) f) q) (fun _ => massTotalVariation_nonneg _ _)
  simpa only [uniformAverage,SectionThirteenFiniteBound.finiteUniformAverage,meanAtomDistance] using hsel

/-- All positive events measurable in the full small-prime field are included. -/
theorem field_event_tv_le_mean_div_probability {α : Type*}
    [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    {C Y : ℕ} (hYC : Y ≤ C) (A : Set InfiniteSample)
    (hA : MeasurableSet[MeasurableSpace.comap (restrictToFinite Y) inferInstance] A)
    (hpos : 0 < infiniteRademacherMeasure.real A)
    {f : InfiniteSample → α} (hf : Measurable f) {q : α → ℝ}
    (hq : HasSum q 1) (hq0 : ∀ a, 0 ≤ q a) :
    massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure A f) q ≤
      meanAtomDistance C Y f q / infiniteRademacherMeasure.real A := by
  rw [← smallPrimeSigmaAlgebra_eq_primeCylinder hYC] at hA
  obtain ⟨S,rfl⟩ := measurableSet_eq_primeFieldEvent hA
  exact selected_field_tv_le_mean_div_probability C Y S
    ((real_primeFieldEvent_pos_iff _ _ S).mp hpos) hf hq hq0

end
end PaperC.V282.CountablePrimeEventTransfer
