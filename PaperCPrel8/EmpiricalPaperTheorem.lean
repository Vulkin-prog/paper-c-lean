import PaperCPrel8.EmpiricalPaperBudget
import PaperCPrel8.EmpiricalStartField

/-! # Corollary 7.8a at the paper's literal scales

For fixed 0<alpha<1 and tau>0, the empirical arithmetic count law converges
almost surely in total variation to Poisson(tau), on M=2^k with exactly the
paper's rounded length and window. The only external inputs are those of
the established microscopic comparison, including its explicit analytic
Stein solution premise. Numerical admissibility and summability are proved.
-/
namespace PaperC.Prel8.EmpiricalPaperTheorem
open MeasureTheory ProbabilityTheory Filter Topology
open PaperC.InfiniteRademacher PaperC.InfiniteCylinderTransfer
open PaperC.Prel8.EmpiricalPaperScales PaperC.Prel8.EmpiricalPaperBudget
open PaperC.Prel8.EmpiricalScaleBounds PaperC.Prel8.EmpiricalStartField
open PaperC.Prel8.EmpiricalWindowVariance PaperC.Prel8.MicroscopicFullTheorem
open PaperC.Prel8.MicroscopicSiteRestoration PaperC.Prel8.MicroscopicPaperBudget
open PaperC.Prel8.MicroscopicActualGeometry PaperC.Prel8.MicroscopicProfileBudget
open PaperC.Prel8.ActualSignedPalm PaperC.Prel8.MicroscopicRetainedTheorem
open PaperC.V282.FiniteFieldTotalVariation PaperC.V282.ConditionedCountableLaw
open PaperC.V282.BulkMarkedSource PaperC.V282.BulkMarkedComparison
open PaperC.V282.RareConditioningRates PaperC.V282.DirectionalSteinInput
open PaperC.V282.LaishramUniformInput PaperC.V282.PostQuadraticLiterature PaperC.V282.PrimeEulerPNT
open PaperC.V282.SaddleScales
open scoped NNReal
noncomputable section
local instance : MeasurableSpace PaperC.F₂ := ⊤
local instance : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- The genuine full-field error on the literal empirical lengths has a summable bound. -/
theorem paper_field_comparison
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeNumberTheoremRemainder) (hNR : PaperC.PellInput.NicolasRobinDivisorLogBoundStatement)
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1)
    (hsol : ∀ᶠ k in atTop, DirectionalSolutionBounds (rate (length alpha k) :
      Index (actualSites (size k) (length alpha k) 0)
        (paperExcess (size k) (length alpha k) 0) → ℝ≥0)) :
    ∀ᶠ k in atTop,
      massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure Set.univ
        (spatialMarkedSource (interiorStarts (size k) (length alpha k)) (length alpha k)))
        (spatialTargetLaw (interiorStarts (size k) (length alpha k)) (length alpha k)) ≤
      10*Real.exp (-saddleNu 1 (Real.log (size k)))+4*(size k:ℝ)^(-(1/(6:ℝ))) := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hband : 1/(2*Real.log 2) < 2/Real.log 2 := by
    apply (div_lt_iff₀ (by positivity : 0<2*Real.log 2)).mpr
    field_simp
    norm_num
  obtain ⟨Mzero,hmain⟩ := full_prime_event_comparison_eventually hLS hShorey hPNT hNR
    (1/(2*Real.log 2)) (2/Real.log 2) 2 1 (1/6) (by positivity) hband
    (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [size_tendsto.eventually (eventually_ge_atTop Mzero),length_band alpha ha.le,
    information_budget alpha 2 ha ha1,
    (intensity_tendsto alpha ha).eventually (eventually_ge_atTop (1:ℝ)),hsol] with k hk hb hi hr hs
  have h := hmain (size k) hk (length alpha k) 0 hb.2.1 hb.2.2 (by norm_num) hr
    (by simpa only [zero_add,cutoff] using hi) Set.univ MeasurableSet.univ (by simp)
    (by simp [eventInformation]) hs
  norm_num at h ⊢
  exact h

/-- Corollary 7.8a: a full-probability set for each fixed alpha and tau,
along the exact dyadic scales, with no independence between source scales. -/
theorem paper_empirical_poisson
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeNumberTheoremRemainder) (hNR : PaperC.PellInput.NicolasRobinDivisorLogBoundStatement)
    (alpha : ℝ) (tau : ℝ≥0) (ha : 0 < alpha) (ha1 : alpha < 1) (ht : 0 < tau)
    (hsol : ∀ᶠ k in atTop, DirectionalSolutionBounds (rate (length alpha k) :
      Index (actualSites (size k) (length alpha k) 0)
        (paperExcess (size k) (length alpha k) 0) → ℝ≥0)) :
    ∀ᵐ ω ∂infiniteRademacherMeasure, Tendsto (fun k => massTotalVariation
      (fun r => frequency (origins alpha tau k) (windowSize alpha tau k) r
        (actualStarts (size k) (length alpha k) ω))
      (fun r => (poissonMeasure tau).real {r})) atTop (𝓝 0) := by
  have htr : (0:ℝ)<tau := ht
  apply ae_actual_empirical_poisson size (length alpha) (origins alpha tau) (windowSize alpha tau)
    (fun k => 10*Real.exp (-saddleNu 1 (Real.log (size k)))+4*(size k:ℝ)^(-(1/(6:ℝ)))) tau
    (origins_pos alpha tau) ((window_fits alpha tau ha htr).mono (fun _ h => h.1)) ?_
    (paper_field_comparison hLS hShorey hPNT hNR alpha ha ha1 hsol) ?_
    (summable_window_origins_ratio alpha tau ha htr) (window_mean_tendsto alpha tau ha.le htr.le)
  · filter_upwards [window_fits alpha tau ha htr] with k hk
    exact (origins_comparison alpha tau hk.2).2.le
  · have h := summable_dyadic_full_error (c := 1) (epsilon := 1/6) (by norm_num) (by norm_num)
    norm_num [size] at h ⊢
    exact h

end
end PaperC.Prel8.EmpiricalPaperTheorem
