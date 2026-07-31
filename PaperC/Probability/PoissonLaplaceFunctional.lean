import PaperC.Analysis.SpatialMarkedParameters
import Mathlib.Probability.Distributions.Poisson

/-!
# Poisson Laplace functionals

This module records the algebraic identity behind the void-probability
argument of Section 14 and packages the final analytic convergence criterion.
It deliberately states convergence of Laplace functionals, which is the
source-facing endpoint needed by the manuscript and does not depend on a
separate topology-of-point-measures API.
-/

namespace PaperC
namespace PoissonLaplaceFunctional

open scoped BigOperators Topology NNReal
open Filter MeasureTheory Set ProbabilityTheory
open SpatialMarkedParameters

noncomputable section

/-- The scalar Laplace transform of a Poisson mass function. -/
def poissonLaplaceTransform (r : ℝ≥0) (s : ℝ) : ℝ :=
  ∑' k : ℕ, poissonPMFReal r k * (Real.exp (-s)) ^ k

/--
Exact scalar Poisson Laplace identity:
`E[exp(-s Z)] = exp(-r (1-exp(-s)))`.
-/
theorem poissonLaplaceTransform_eq
    (r : ℝ≥0) (s : ℝ) :
    poissonLaplaceTransform r s =
      Real.exp (-((r : ℝ) * (1 - Real.exp (-s)))) := by
  have hseries :
      HasSum
        (fun k : ℕ ↦
          (((r : ℝ) * Real.exp (-s)) ^ k) /
            (Nat.factorial k : ℝ))
        (Real.exp ((r : ℝ) * Real.exp (-s))) := by
    simpa only [Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp ℝ
        ((r : ℝ) * Real.exp (-s)))
  unfold poissonLaplaceTransform
  calc
    (∑' k : ℕ,
        poissonPMFReal r k * (Real.exp (-s)) ^ k) =
        Real.exp (-(r : ℝ)) *
          ∑' k : ℕ,
            (((r : ℝ) * Real.exp (-s)) ^ k) /
              (Nat.factorial k : ℝ) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      unfold poissonPMFReal
      rw [mul_pow]
      ring
    _ = Real.exp (-(r : ℝ)) *
        Real.exp ((r : ℝ) * Real.exp (-s)) := by
      rw [hseries.tsum_eq]
    _ = Real.exp (-((r : ℝ) * (1 - Real.exp (-s)))) := by
      rw [← Real.exp_add]
      congr 1
      ring

/--
Finite products of independent Poisson Laplace transforms combine into the
exponential of the sum of their thinned rates.
-/
theorem prod_poissonLaplaceTransform_eq
    (marks : Finset ℕ) (rate test : ℕ → ℝ≥0) :
    (∏ e ∈ marks,
        poissonLaplaceTransform (rate e) (test e : ℝ)) =
      Real.exp
        (-(∑ e ∈ marks,
          (rate e : ℝ) *
            (1 - Real.exp (-(test e : ℝ))))) := by
  simp_rw [poissonLaplaceTransform_eq]
  rw [← Real.exp_sum]
  congr 1
  rw [← Finset.sum_neg_distrib]

/--
Analytic closing lemma: if a finite-model Laplace functional differs from
`exp(-parameter)` by an error tending to zero, and the parameter tends to
`a`, then the functional tends to `exp(-a)`.
-/
theorem tendsto_laplace_of_parameter_and_error
    {ι : Type*} {l : Filter ι}
    {laplace parameter error : ι → ℝ} {a : ℝ}
    (hparameter : Tendsto parameter l (𝓝 a))
    (herror : Tendsto error l (𝓝 0))
    (happrox :
      ∀ᶠ n in l,
        |laplace n - Real.exp (-parameter n)| ≤ error n) :
    Tendsto laplace l (𝓝 (Real.exp (-a))) := by
  have habs :
      Tendsto
        (fun n ↦ |laplace n - Real.exp (-parameter n)|)
        l (𝓝 0) :=
    squeeze_zero'
      (Filter.Eventually.of_forall fun _ ↦ abs_nonneg _)
      happrox herror
  have hdiff :
      Tendsto
        (fun n ↦ laplace n - Real.exp (-parameter n))
        l (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using habs
  have hexp :
      Tendsto
        (fun n ↦ Real.exp (-parameter n))
        l (𝓝 (Real.exp (-a))) :=
    Real.continuous_exp.continuousAt.tendsto.comp hparameter.neg
  convert hdiff.add hexp using 1
  · funext n
    ring
  · simp

/--
Section 14.2 endpoint in Laplace-functional form.  The test function is
continuous and nonnegative, the arithmetic/probabilistic layer supplies only
the displayed vanishing approximation error, and the conclusion is the
Laplace functional of `PPP(rate dt)` on `[1,2)`.
-/
theorem sectionFourteenTwo_laplaceFunctional
    {N L : ℕ → ℕ} {rate : ℝ} {g : ℝ → ℝ}
    {laplace error : ℕ → ℝ}
    (hN : Tendsto N atTop atTop)
    (hscale : Tendsto
      (fun n ↦ criticalSpatialScale (N n) (L n))
      atTop (𝓝 rate))
    (hg : ContinuousOn g (Set.Icc (1 : ℝ) 2))
    (_hg0 : ∀ t, 0 ≤ g t)
    (herror : Tendsto error atTop (𝓝 0))
    (happrox :
      ∀ᶠ n in atTop,
        |laplace n -
          Real.exp
            (-spatialThinnedParameter (N n) (L n) g)| ≤
          error n) :
    Tendsto laplace atTop
      (𝓝 (Real.exp
        (-(rate * ∫ t in Set.Ico (1 : ℝ) 2,
          (1 - Real.exp (-g t)))))) := by
  have hparam :=
    tendsto_spatialThinnedParameter hN hscale hg
  simpa only [spatialRetention] using
    tendsto_laplace_of_parameter_and_error
      hparam herror happrox

/--
Section 14.4 endpoint for a fixed mark cutoff `E`.  It is the Laplace
functional of the Poisson intensity
`rate · dt ⊗ (∑_{e≤E} 2^{-(e+1)} δ_e)`.
-/
theorem sectionFourteenFour_laplaceFunctional
    {N L : ℕ → ℕ} {rate : ℝ} {E : ℕ}
    {g : ℝ → ℕ → ℝ} {laplace error : ℕ → ℝ}
    (hN : Tendsto N atTop atTop)
    (hscale : Tendsto
      (fun n ↦ criticalSpatialScale (N n) (L n))
      atTop (𝓝 rate))
    (hg : ∀ e ≤ E,
      ContinuousOn (fun t ↦ g t e) (Set.Icc (1 : ℝ) 2))
    (_hg0 : ∀ t e, 0 ≤ g t e)
    (herror : Tendsto error atTop (𝓝 0))
    (happrox :
      ∀ᶠ n in atTop,
        |laplace n -
          Real.exp
            (-markedThinnedParameter (N n) (L n) E g)| ≤
          error n) :
    Tendsto laplace atTop
      (𝓝 (Real.exp
        (-(rate * ∫ t in Set.Ico (1 : ℝ) 2,
          ∑ e ∈ Finset.range (E + 1),
            (1 / (2 : ℝ) ^ (e + 1)) *
              (1 - Real.exp (-g t e)))))) := by
  have hparam :=
    tendsto_markedThinnedParameter hN hscale hg
  simpa only [markedRetentionIntegrand, geometricMarkWeight,
    spatialRetention] using
      tendsto_laplace_of_parameter_and_error
        hparam herror happrox

end

end PoissonLaplaceFunctional
end PaperC
