import PaperCV282.CountableExpectationTransfer
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Transfer of genuine weak limits from a varying countable lattice

The target weak convergence is in the topology on probability measures.
Discrete total variation supplies bounds for the actual integrals of every
bounded continuous test after embedding each lattice into the common space.
-/
namespace PaperC.V282.CountableWeakTransfer

open MeasureTheory Filter InfiniteMassCoupling FiniteFieldTotalVariation CountableExpectationTransfer
open scoped Topology BoundedContinuousFunction

noncomputable section

def imageProbabilityLaw {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → X) (hf : Measurable f) : ProbabilityMeasure X :=
  ⟨μ.map f,Measure.isProbabilityMeasure_map hf.aemeasurable⟩

theorem integral_imageProbabilityLaw {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → X) (hf : Measurable f) (F : X →ᵇ ℝ) :
    (∫ x, F x ∂(imageProbabilityLaw μ f hf : Measure X)) = ∫ ω, F (f ω) ∂μ :=
  integral_map_of_stronglyMeasurable hf F.continuous.measurable.stronglyMeasurable

/-- Vanishing errors against every bounded continuous test transfer an actual weak limit. -/
theorem weak_limit_of_integral_error {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] (p q : ℕ → ProbabilityMeasure X) (limit : ProbabilityMeasure X)
    (error : ℕ → ℝ) (herror : Tendsto error atTop (𝓝 0))
    (hbound : ∀ n, ∀ F : X →ᵇ ℝ,
      |(∫ x, F x ∂(p n : Measure X))-(∫ x, F x ∂(q n : Measure X))| ≤ 2*‖F‖*error n)
    (hq : Tendsto q atTop (𝓝 limit)) : Tendsto p atTop (𝓝 limit) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hq ⊢
  intro F
  have habs : Tendsto (fun n =>
      |(∫ x, F x ∂(p n : Measure X))-(∫ x, F x ∂(q n : Measure X))|) atTop (𝓝 0) :=
    squeeze_zero (fun _ => abs_nonneg _) (fun n => hbound n F)
      (by simpa only [mul_zero] using herror.const_mul (2*‖F‖))
  have hdiff : Tendsto (fun n =>
      (∫ x, F x ∂(p n : Measure X))-(∫ x, F x ∂(q n : Measure X))) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using habs)
  simpa only [sub_add_cancel,zero_add] using hdiff.add (hq F)

/-- Countable lattices may vary with n; all their images live in the same weak-limit space. -/
theorem countable_lattice_weak_transfer {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    (α : ℕ → Type*) [∀ n, Countable (α n)] [∀ n, MeasurableSpace (α n)]
    [∀ n, MeasurableSingletonClass (α n)]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : ∀ n, Measure (α n))
    [∀ n, IsProbabilityMeasure (ν n)] (f : ∀ n, Ω → α n) (hf : ∀ n, Measurable (f n))
    (embed : ∀ n, α n → X) (limit : ProbabilityMeasure X)
    (htv : Tendsto (fun n => massTotalVariation (observableLaw μ (f n)) (observableLaw (ν n) id))
      atTop (𝓝 0))
    (htarget : Tendsto (fun n => imageProbabilityLaw (ν n) (embed n) (measurable_of_countable _))
      atTop (𝓝 limit)) :
    Tendsto (fun n => imageProbabilityLaw μ ((embed n) ∘ (f n))
      ((measurable_of_countable _).comp (hf n))) atTop (𝓝 limit) := by
  apply weak_limit_of_integral_error _ _ limit _ htv _ htarget
  intro n F
  rw [integral_imageProbabilityLaw,integral_imageProbabilityLaw]
  exact integral_difference_le_tv μ (ν n) (hf n) measurable_id
    (fun a => F (embed n a)) ‖F‖ (fun a => by
      simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm (embed n a))

end
end PaperC.V282.CountableWeakTransfer
