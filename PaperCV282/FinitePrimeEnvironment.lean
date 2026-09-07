import PaperCV282.CountablePrimeEventTransfer
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Actual random small-prime environments and their finite averages

The conditional distance is a measurable random variable on the original
infinite Rademacher probability space. Its expectation is precisely the
finite atom average, with no independence assumption between scales.
-/
namespace PaperC.V282.FinitePrimeEnvironment

open MeasureTheory ProbabilityTheory InfiniteRademacher InfiniteCylinderTransfer InfiniteConditionalWords
open ConditionalStartProbability PrimeFieldEventConditioning CountablePrimeEventTransfer
open InfiniteMassCoupling FiniteFieldTotalVariation ConditionedCountableLaw
open scoped ENNReal

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- Each recorded environment has the genuine uniform law on small-prime assignments. -/
theorem map_smallPrimeRestriction (C Y : ℕ) :
    infiniteRademacherMeasure.map (smallPrimeRestriction C Y) =
      (PMF.uniformOfFintype (SmallSample C Y)).toMeasure := by
  apply Measure.ext_of_singleton
  intro sigma
  rw [Measure.map_apply (measurable_smallPrimeRestriction C Y) (measurableSet_singleton _)]
  change infiniteRademacherMeasure (infiniteSmallPrimeAtom C Y sigma)=_
  rw [MaskedScalarFullConditioning.conditioningAtoms_equiprobable]
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp [PMF.uniformOfFintype_apply]

/-- A real function of finitely many prime signs is integrable. -/
theorem integrable_environment_function (C Y : ℕ) (f : SmallSample C Y → ℝ) :
    Integrable (f ∘ smallPrimeRestriction C Y) infiniteRademacherMeasure := by
  have hm := measurable_smallPrimeRestriction C Y
  have hf : Integrable f (infiniteRademacherMeasure.map (smallPrimeRestriction C Y)) := by
    exact Integrable.of_finite
  exact hf.comp_measurable hm

/-- The actual expectation is the equiprobable atom average used by the finite proofs. -/
theorem integral_environment_function (C Y : ℕ) (f : SmallSample C Y → ℝ) :
    (∫ omega, f (smallPrimeRestriction C Y omega) ∂infiniteRademacherMeasure) = uniformAverage f := by
  rw [← integral_map (measurable_smallPrimeRestriction C Y).aemeasurable
    (measurable_of_finite f).aestronglyMeasurable]
  rw [map_smallPrimeRestriction,integral_fintype Integrable.of_finite]
  simp_rw [Measure.real,PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp only [PMF.uniformOfFintype_apply,
    ENNReal.toReal_inv,ENNReal.toReal_natCast,smul_eq_mul,uniformAverage]
  rw [← Finset.mul_sum]
  ring

/-- The literal conditional distance at the observed environment. -/
def environmentDistance {α : Type*} (C Y : ℕ) (f : InfiniteSample → α) (q : α → ℝ)
    (omega : InfiniteSample) : ℝ :=
  massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure
    (infiniteSmallPrimeAtom C Y (smallPrimeRestriction C Y omega)) f) q

theorem measurable_environmentDistance {α : Type*} (C Y : ℕ)
    (f : InfiniteSample → α) (q : α → ℝ) : Measurable (environmentDistance C Y f q) :=
  (measurable_of_finite (fun sigma : SmallSample C Y =>
    massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure
      (infiniteSmallPrimeAtom C Y sigma) f) q)).comp (measurable_smallPrimeRestriction C Y)

theorem environmentDistance_nonneg {α : Type*} (C Y : ℕ)
    (f : InfiniteSample → α) (q : α → ℝ) (omega : InfiniteSample) :
    0 ≤ environmentDistance C Y f q omega := massTotalVariation_nonneg _ _

theorem integrable_environmentDistance {α : Type*} (C Y : ℕ)
    (f : InfiniteSample → α) (q : α → ℝ) :
    Integrable (environmentDistance C Y f q) infiniteRademacherMeasure :=
  integrable_environment_function C Y (fun sigma => massTotalVariation
    (conditionalObservableLaw infiniteRademacherMeasure (infiniteSmallPrimeAtom C Y sigma) f) q)

theorem integral_environmentDistance {α : Type*} (C Y : ℕ)
    (f : InfiniteSample → α) (q : α → ℝ) :
    (∫ omega, environmentDistance C Y f q omega ∂infiniteRademacherMeasure) =
      meanAtomDistance C Y f q := integral_environment_function C Y (fun sigma => massTotalVariation
    (conditionalObservableLaw infiniteRademacherMeasure (infiniteSmallPrimeAtom C Y sigma) f) q)

/-- Averaging genuine conditional event probabilities exactly recovers the source probability. -/
theorem average_conditional_event (C Y : ℕ) (A : Set InfiniteSample) (hA : MeasurableSet A) :
    uniformAverage (fun sigma : SmallSample C Y =>
      (cond infiniteRademacherMeasure (infiniteSmallPrimeAtom C Y sigma)).real A)=
      infiniteRademacherMeasure.real A := by
  have hu : primeFieldEvent C Y Finset.univ = Set.univ := by
    ext omega
    simp [primeFieldEvent]
  have h := source_event_ratio_eq_atom_average C Y Finset.univ Finset.univ_nonempty A hA
  rw [hu,Set.inter_univ] at h
  simp only [Measure.real,measure_univ,ENNReal.toReal_one,div_one] at h
  rw [uniformAverage]
  simp only [Measure.real,cond_apply (measurableSet_infiniteSmallPrimeAtom C Y _),
    ENNReal.toReal_mul,ENNReal.toReal_inv]
  simp only [Finset.card_univ] at h
  convert h.symm using 1
  congr 1
  apply Finset.sum_congr rfl
  intro sigma _
  rw [Set.inter_comm]
  ring

/-- Enlarging the ambient cylinder does not change the actual observed F_Y atom. -/
theorem observed_atom_eq {C Y : ℕ} (hYC : Y ≤ C) (omega : InfiniteSample) :
    infiniteSmallPrimeAtom C Y (smallPrimeRestriction C Y omega) =
      {eta | restrictToFinite Y eta=restrictToFinite Y omega} := by
  ext eta
  rw [mem_infiniteSmallPrimeAtom_iff hYC]
  constructor
  · intro h
    funext p
    exact h p
  · intro h p
    exact congrFun h p

/-- The conditional law is independent of its adequate finite-cylinder presentation. -/
theorem environmentDistance_eq_canonical {α : Type*} {C Y : ℕ} (hYC : Y ≤ C)
    (f : InfiniteSample → α) (q : α → ℝ) :
    environmentDistance C Y f q=environmentDistance Y Y f q := by
  funext omega
  unfold environmentDistance
  rw [observed_atom_eq hYC,observed_atom_eq (le_refl Y)]

/-- The atom mean is therefore independent of the chosen adequate ambient cutoff. -/
theorem meanAtomDistance_eq_canonical {α : Type*} {C Y : ℕ} (hYC : Y ≤ C)
    (f : InfiniteSample → α) (q : α → ℝ) :
    meanAtomDistance C Y f q=meanAtomDistance Y Y f q := by
  rw [← integral_environmentDistance,← integral_environmentDistance,
    environmentDistance_eq_canonical hYC]

end
end PaperC.V282.FinitePrimeEnvironment
