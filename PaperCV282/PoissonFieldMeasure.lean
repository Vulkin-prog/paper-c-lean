import PaperCV282.FiniteFieldPoissonCoupling
import PaperCV282.MassPushforward
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Independence.Basic

/-!
# The product Poisson mass as its actual product measure

This bridge permits probability-law identities for sums to be transported
back to the half-L1 mass convention used by the manuscript endpoints.
The space of count vectors is countable, without being finite.
-/

namespace PaperC.V282.PoissonFieldMeasure

open MeasureTheory ProbabilityTheory FiniteFieldPoissonCoupling ScalarSteinInput MassPushforward
open scoped BigOperators NNReal ENNReal

noncomputable section

/-- The actual product of the scalar Poisson probability measures. -/
def fieldMeasure {ι : Type*} [Fintype ι] (rate : ι → ℝ≥0) : Measure (ι → ℕ) :=
  Measure.pi (fun i => poissonMeasure (rate i))

instance instIsProbabilityMeasureField {ι : Type*} [Fintype ι] (rate : ι → ℝ≥0) :
    IsProbabilityMeasure (fieldMeasure rate) := by
  unfold fieldMeasure
  infer_instance

theorem fieldMeasure_real_singleton {ι : Type*} [Fintype ι]
    (rate : ι → ℝ≥0) (k : ι → ℕ) : (fieldMeasure rate).real {k} = poissonFieldMass rate k := by
  unfold fieldMeasure Measure.real poissonFieldMass poissonMass
  rw [Measure.pi_singleton,ENNReal.toReal_prod]
  rfl

/-- A countable measure assigns to a set the sum of its singleton masses. -/
theorem real_tsum_singletons {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsFiniteMeasure μ] (s : Set α) :
    (∑' a : s, μ.real {a.val}) = μ.real s := by
  have hsum : (∑' a : s, μ {a.val}) = μ s := by
    exact (tsum_subtype s (fun a => μ {a})).trans
      (μ.tsum_indicator_apply_singleton s (Set.to_countable s).measurableSet)
  have hfinite (a : s) : μ {a.val} ≠ ⊤ := measure_ne_top _ _
  rw [Measure.real,← hsum,ENNReal.tsum_toReal_eq hfinite]
  rfl

/-- The mass pushforward agrees exactly with the measure of the corresponding fibre. -/
theorem pushforward_real_singletons {α β : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsFiniteMeasure μ] (f : α → β) (b : β) :
    pushforwardMass f (fun a => μ.real {a}) b = μ.real (f ⁻¹' {b}) :=
  real_tsum_singletons μ _

theorem pushforward_poissonFieldMass_eq_measure {ι β : Type*} [Fintype ι]
    (rate : ι → ℝ≥0) (f : (ι → ℕ) → β) (b : β) :
    pushforwardMass f (poissonFieldMass rate) b = (fieldMeasure rate).real (f ⁻¹' {b}) := by
  have heq : poissonFieldMass rate = fun k => (fieldMeasure rate).real {k} :=
    funext fun k => (fieldMeasure_real_singleton rate k).symm
  rw [heq]
  exact pushforward_real_singletons _ f b

/-- Any proved law of a statistic of the product field supplies its exact target mass. -/
theorem pushforward_poissonFieldMass_of_hasLaw {ι β : Type*} [Fintype ι]
    [MeasurableSpace β] [MeasurableSingletonClass β] (rate : ι → ℝ≥0)
    (f : (ι → ℕ) → β) (ν : Measure β) (h : HasLaw f ν (fieldMeasure rate)) :
    pushforwardMass f (poissonFieldMass rate) = fun b => ν.real {b} := by
  funext b
  rw [pushforward_poissonFieldMass_eq_measure]
  exact h.measureReal_eq (measurableSet_singleton b)

/-- The coordinate projections are genuinely mutually independent. -/
theorem independent_coordinates {ι : Type*} [Fintype ι] (rate : ι → ℝ≥0) :
    iIndepFun (fun i (k : ι → ℕ) => k i) (fieldMeasure rate) := by
  exact iIndepFun_pi (fun _ => measurable_id.aemeasurable)

theorem hasLaw_coordinate {ι : Type*} [Fintype ι] (rate : ι → ℝ≥0) (i : ι) :
    HasLaw (fun k : ι → ℕ => k i) (poissonMeasure (rate i)) (fieldMeasure rate) :=
  (measurePreserving_eval (fun j => poissonMeasure (rate j)) i).hasLaw

/-- The zero-rate measure is the deterministic zero law. -/
theorem poissonMeasure_zero_eq_dirac : poissonMeasure 0 = Measure.dirac (0 : ℕ) := by
  apply Measure.ext_of_singleton
  intro n
  cases n <;> simp [poissonMeasure_singleton]

/-- The sum of an arbitrary finite set of coordinates has the sum of their rates. -/
theorem hasLaw_coordinate_sum {ι : Type*} [Fintype ι] (rate : ι → ℝ≥0) (s : Finset ι) :
    HasLaw (fun k : ι → ℕ => ∑ i ∈ s, k i) (poissonMeasure (∑ i ∈ s, rate i)) (fieldMeasure rate) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [poissonMeasure_zero_eq_dirac]
    exact hasLaw_dirac_of_ae_eq (Filter.Eventually.of_forall fun _ => rfl)
  | @insert i s hi ih =>
    have hdep := (independent_coordinates rate).indepFun_finsetSum_of_notMem
      (fun j => measurable_pi_apply j) hi
    have heq : (∑ j ∈ s, fun k : ι → ℕ => k j) = (fun k => ∑ j ∈ s, k j) := by
      funext k
      simp only [Finset.sum_apply]
    rw [heq] at hdep
    have hsum := hdep.symm.hasLaw_add_poissonMeasure (hasLaw_coordinate rate i) ih
    change HasLaw (fun k => k i + ∑ j ∈ s, k j)
      (poissonMeasure (rate i + ∑ j ∈ s, rate j)) (fieldMeasure rate) at hsum
    simpa only [Finset.sum_insert hi] using hsum

/-- Exact mass identity for any masked sum of independent Poisson coordinates. -/
theorem pushforward_poissonFieldMass_sum {ι : Type*} [Fintype ι]
    (rate : ι → ℝ≥0) (s : Finset ι) :
    pushforwardMass (fun k : ι → ℕ => ∑ i ∈ s, k i) (poissonFieldMass rate) =
      poissonMass (∑ i ∈ s, rate i) :=
  pushforward_poissonFieldMass_of_hasLaw rate _ _ (hasLaw_coordinate_sum rate s)

end
end PaperC.V282.PoissonFieldMeasure
