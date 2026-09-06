import PaperCV282.PrimeClockDistribution
import PaperCV282.MicroscopicNonvacancy
import PaperCV282.GeometricClusterTarget

/-! # The genuine prime clock under microscopic non-vacancy

The observable is the same measurable G_L, with its specified value zero
off the border. Nested conditioning and pushforward transfer the actual
interior first moment to total variation from the fixed geometric law.
-/
namespace PaperC.V282.PrimeClockMicroscopicTransfer

open MeasureTheory ProbabilityTheory Filter InfiniteRademacher
open InfiniteStartProbabilityTransfer MicroscopicBorderEvents MicroscopicNonvacancy
open PrimeClockDistribution SharpConditioning GeometricClusterTarget
open scoped BigOperators Topology

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- The complete law of G_L under the genuine microscopic event. -/
def microscopicPrimeClockLaw (L : ℕ) : Measure ℕ :=
  (cond infiniteRademacherMeasure (microscopicEvent L)).map (primeOvershoot L)

theorem microscopicPrimeClockLaw_probability (L : ℕ) :
    IsProbabilityMeasure (microscopicPrimeClockLaw L) := by
  letI instProbabilityConditionalMicro : IsProbabilityMeasure
      (cond infiniteRademacherMeasure (microscopicEvent L)) :=
    cond_isProbabilityMeasure (ConditionedCountableLaw.measure_ne_zero_of_real_pos _
      (microscopicProbability_pos L))
  exact Measure.isProbabilityMeasure_map (measurable_primeOvershoot L).aemeasurable

/-- The border law is exactly the standard nonnegative geometric law. -/
theorem conditionalPrimeClockLaw_eq_geometric (L : ℕ) :
    conditionalPrimeClockLaw L=geometricMeasure halfSuccess := by
  letI instProbabilityClock : IsProbabilityMeasure (conditionalPrimeClockLaw L) :=
    conditionalPrimeClockLaw_probability L
  apply Measure.ext_of_measureReal_singleton
  intro k
  rw [conditionalPrimeClockLaw_singleton,geometricMeasure_real_singleton halfSuccess_ne_zero]
  norm_num [halfSuccess,pow_succ]

/-- Finite relative error, on the actual conditional source and with no independence assumption. -/
theorem microscopic_prime_clock_tv_le {L : ℕ} {epsilon : ℝ}
    (h : (∑ x ∈ Finset.Icc 2 (2 * L ^ 2), infiniteStartProbability x L) ≤ epsilon) :
    measureTotalVariation (microscopicPrimeClockLaw L) (geometricMeasure halfSuccess) ≤
      epsilon / ((2 : ℝ)⁻¹)^Nat.primeCounting L := by
  letI instProbabilityConditionalMicro : IsProbabilityMeasure
      (cond infiniteRademacherMeasure (microscopicEvent L)) :=
    cond_isProbabilityMeasure (ConditionedCountableLaw.measure_ne_zero_of_real_pos _
      (microscopicProbability_pos L))
  letI instProbabilityConditionalBorder : IsProbabilityMeasure
      (cond infiniteRademacherMeasure (borderEvent L)) :=
    cond_isProbabilityMeasure (ConditionedCountableLaw.measure_ne_zero_of_real_pos _
      (borderEvent_probability_pos L))
  rw [← conditionalPrimeClockLaw_eq_geometric L]
  exact (measureTotalVariation_map_le _ _ (measurable_primeOvershoot L)).trans
    (microscopic_conditional_tv_le h)

/-- Relative first-moment decay entails convergence of the full clock laws. -/
theorem microscopic_prime_clock_tendsto_geometric
    (hrelative : Tendsto (fun L : ℕ =>
      (∑ x ∈ Finset.Icc 2 (2 * L ^ 2), infiniteStartProbability x L) /
        ((2 : ℝ)⁻¹)^Nat.primeCounting L) atTop (𝓝 0)) :
    Tendsto (fun L : ℕ => measureTotalVariation (microscopicPrimeClockLaw L)
      (geometricMeasure halfSuccess)) atTop (𝓝 0) := by
  apply squeeze_zero _ _ hrelative
  · intro L
    letI instProbabilityClock : IsProbabilityMeasure (microscopicPrimeClockLaw L) :=
      microscopicPrimeClockLaw_probability L
    exact measureTotalVariation_nonneg _ _
  · intro L
    exact microscopic_prime_clock_tv_le (le_refl _)

end
end PaperC.V282.PrimeClockMicroscopicTransfer
