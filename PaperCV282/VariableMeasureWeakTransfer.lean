import PaperCV282.CountableWeakTransfer

/-! # Weak transfer with the actual probability measures allowed to vary

Arithmetic conditioning changes the source measure with N. The estimate uses
those measures in both the observable laws and the integrals of test functions.
-/
namespace PaperC.V282.VariableMeasureWeakTransfer

open MeasureTheory Filter InfiniteMassCoupling FiniteFieldTotalVariation
open CountableExpectationTransfer CountableWeakTransfer
open scoped Topology BoundedContinuousFunction

noncomputable section

theorem variable_lattice_weak_transfer {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    (α : ℕ → Type*) [∀ n, Countable (α n)] [∀ n, MeasurableSpace (α n)]
    [∀ n, MeasurableSingletonClass (α n)]
    (mu : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (mu n)]
    (nu : ∀ n, Measure (α n)) [∀ n, IsProbabilityMeasure (nu n)]
    (f : ∀ n, Ω → α n) (hf : ∀ n, Measurable (f n))
    (embed : ∀ n, α n → X) (limit : ProbabilityMeasure X)
    (htv : Tendsto (fun n => massTotalVariation (observableLaw (mu n) (f n)) (observableLaw (nu n) id))
      atTop (𝓝 0))
    (htarget : Tendsto (fun n => imageProbabilityLaw (nu n) (embed n) (measurable_of_countable _))
      atTop (𝓝 limit)) :
    Tendsto (fun n => imageProbabilityLaw (mu n) ((embed n) ∘ (f n))
      ((measurable_of_countable _).comp (hf n))) atTop (𝓝 limit) := by
  apply weak_limit_of_integral_error _ _ limit _ htv _ htarget
  intro n F
  rw [integral_imageProbabilityLaw,integral_imageProbabilityLaw]
  exact integral_difference_le_tv (mu n) (nu n) (hf n) measurable_id
    (fun a => F (embed n a)) ‖F‖ (fun a => by
      simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm (embed n a))

end
end PaperC.V282.VariableMeasureWeakTransfer
