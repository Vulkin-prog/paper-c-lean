import PaperC.Probability.InfiniteStartProbabilityTransfer
import PaperC.Probability.ConditionalExpectationAverage
import PaperC.Probability.SectionTwelveMoments

/-!
# Genuine infinite-model moments of the dyadic run count

Every function of this finite count is an observable of its actual finite
prime cylinder. Its integral therefore agrees exactly with the retained
finite uniform expectation. In particular the second factorial moment
and the centered variance are integrals, not conclusions inferred from
total variation convergence.
-/

namespace PaperC.V282.InfiniteCountMoments

open MeasureTheory InfiniteRademacher InfiniteCylinderTransfer InfiniteStartProbabilityTransfer
open ConditionalExpectationAverage IndependentThinning SectionTwelveMoments
open InfiniteExactLengthProbabilityTransfer
open scoped BigOperators

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

/-- An arbitrary rational-valued finite-cylinder observable integrates to its exact average. -/
theorem integral_finite_rational_observable (M : ℕ) (F : SampleSpace M → ℚ) :
    (∫ sigma, (F sigma : ℝ) ∂finiteRademacherMeasure M) = (uniformExpectation F : ℝ) := by
  rw [finiteRademacherIntegral_eq_uniformPMFExpectation]
  unfold finitePMFExpectation uniformExpectation
  simp only [FinitePMF.uniform_prob, Rat.cast_div, Rat.cast_sum, Rat.cast_natCast]
  rw [← Finset.mul_sum]
  ring

/-- Arbitrary functions of the infinite count are exactly finite-cylinder observables. -/
theorem integral_count_function_eq_finite (N L : ℕ) (g : ℕ → ℚ) :
    (∫ omega, (g (infiniteDyadicStartCount N L omega) : ℝ) ∂infiniteRademacherMeasure) =
      (uniformExpectation (fun sigma : DyadicSample N L => g (dyadicCount N L sigma)) : ℝ) := by
  let F : DyadicSample N L → ℝ := fun sigma => (g (dyadicCount N L sigma) : ℝ)
  calc
    _ = ∫ omega, F (restrictToFinite (dyadicCutoff N L) omega) ∂infiniteRademacherMeasure := by
      apply integral_congr_ae
      filter_upwards [] with omega
      simp only [F, dyadicCount_restrictToFinite_eq_infiniteDyadicStartCount]
    _ = ∫ sigma, F sigma ∂finiteRademacherMeasure (dyadicCutoff N L) := by
      rw [← map_infiniteRademacherMeasure_restrictToFinite]
      exact (integral_map_of_stronglyMeasurable (measurable_restrictToFinite _)
        (measurable_of_finite F).stronglyMeasurable).symm
    _ = _ := integral_finite_rational_observable _ _

/-- The finite-valued infinite observable is integrable, including all polynomial moments. -/
theorem integrable_count_function (N L : ℕ) (g : ℕ → ℚ) :
    Integrable (fun omega => (g (infiniteDyadicStartCount N L omega) : ℝ)) infiniteRademacherMeasure := by
  let F : DyadicSample N L → ℝ := fun sigma => (g (dyadicCount N L sigma) : ℝ)
  have hF : Integrable F (finiteRademacherMeasure (dyadicCutoff N L)) :=
    ⟨(measurable_of_finite F).aestronglyMeasurable, HasFiniteIntegral.of_finite⟩
  have hpres : MeasurePreserving (restrictToFinite (dyadicCutoff N L))
      infiniteRademacherMeasure (finiteRademacherMeasure (dyadicCutoff N L)) :=
    ⟨measurable_restrictToFinite _, map_infiniteRademacherMeasure_restrictToFinite _⟩
  have hh := hpres.integrable_comp_of_integrable hF
  simpa only [Function.comp_def, F, dyadicCount_restrictToFinite_eq_infiniteDyadicStartCount] using hh

/-- The actual expectation under the infinite source measure. -/
def infiniteCountMean (N L : ℕ) : ℝ :=
  ∫ omega, (infiniteDyadicStartCount N L omega : ℝ) ∂infiniteRademacherMeasure

/-- The actual second factorial moment under the infinite source measure. -/
def infiniteCountFactorialMoment (N L : ℕ) : ℝ :=
  ∫ omega, (infiniteDyadicStartCount N L omega : ℝ) *
    ((infiniteDyadicStartCount N L omega : ℝ) - 1) ∂infiniteRademacherMeasure

/-- The centered second moment uses the same genuine infinite expectation. -/
def infiniteCountVariance (N L : ℕ) : ℝ :=
  ∫ omega, ((infiniteDyadicStartCount N L omega : ℝ) - infiniteCountMean N L) ^ 2
    ∂infiniteRademacherMeasure

theorem infiniteCountMean_eq_finite (N L : ℕ) :
    infiniteCountMean N L = (dyadicExpectation N L : ℝ) := by
  have hh := integral_count_function_eq_finite N L (fun k => (k : ℚ))
  simpa only [Rat.cast_natCast, uniformExpectation_dyadicCount, infiniteCountMean] using hh

theorem infiniteCountFactorialMoment_eq_finite (N L : ℕ) :
    infiniteCountFactorialMoment N L = (dyadicSecondFactorialMoment N L : ℝ) := by
  have hh := integral_count_function_eq_finite N L (fun k => (k : ℚ) * ((k : ℚ) - 1))
  simpa only [Rat.cast_mul, Rat.cast_sub, Rat.cast_natCast, Rat.cast_one,
    infiniteCountFactorialMoment, dyadicSecondFactorialMoment] using hh

theorem infiniteCountVariance_eq_finite (N L : ℕ) :
    infiniteCountVariance N L = (dyadicVariance N L : ℝ) := by
  have hh := integral_count_function_eq_finite N L (fun k => ((k : ℚ) - dyadicExpectation N L) ^ 2)
  simp only [Rat.cast_pow, Rat.cast_sub, Rat.cast_natCast] at hh
  unfold infiniteCountVariance
  rw [infiniteCountMean_eq_finite]
  exact hh.trans (by simp only [dyadicVariance, uniformVariance, uniformExpectation_dyadicCount])

/-- The variance identity holds for the actual infinite model without a limiting argument. -/
theorem infiniteCountVariance_eq_factorial_add_mean_sub_sq (N L : ℕ) :
    infiniteCountVariance N L = infiniteCountFactorialMoment N L + infiniteCountMean N L -
      infiniteCountMean N L ^ 2 := by
  rw [infiniteCountVariance_eq_finite, infiniteCountFactorialMoment_eq_finite,
    infiniteCountMean_eq_finite, dyadicVariance_eq_factorial_add_expectation_sub_sq]
  push_cast
  rfl

end
end PaperC.V282.InfiniteCountMoments
