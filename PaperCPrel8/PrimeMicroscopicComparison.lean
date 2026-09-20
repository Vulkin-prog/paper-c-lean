import PaperCPrel8.PrimeWindowBudget
import PaperCPrel8.MicroscopicFullTheorem
import PaperCV282.SaddleRateConvergence

/-! # Vanishing full microscopic distance on the explicit obstruction windows

This uses the same declared directional Stein solution input as F.2.
The divergent activity is not used to prove the approximation.
-/
namespace PaperC.Prel8.PrimeMicroscopicComparison
open Filter Topology MeasureTheory InfiniteRademacher ConditionalStartProbability
open PrimeWindowScales PrimeWindowBudget MicroscopicFullTheorem MicroscopicActualGeometry
open MicroscopicProfileBudget MicroscopicRetainedTheorem ActualSignedPalm MicroscopicSiteRestoration
open V282.BulkMarkedSource V282.BulkMarkedComparison V282.ConditionedCountableLaw V282.FiniteFieldTotalVariation
open V282.RareConditioningRates V282.DirectionalSteinInput V282.SaddleRateConvergence V282.SaddleScales
open V282.LaishramUniformInput V282.PostQuadraticLiterature V282.PrimeEulerPNT
open scoped NNReal
noncomputable section
local instance : MeasurableSpace F₂ := ⊤
local instance : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

def distance (q : ℕ) : ℝ :=
  massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure Set.univ
    (spatialMarkedSource (interiorStarts (window q) (q-1)) (q-1)))
    (spatialTargetLaw (interiorStarts (window q) (q-1)) (q-1))

/-- All starts, signs and excesses converge, independently of the cumulant obstruction. -/
theorem distance_tendsto (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeNumberTheoremRemainder) (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (hsolution : ∀ᶠ q : ℕ in atTop,
      DirectionalSolutionBounds (rate (q-1) :
        Index (actualSites (window q) (q-1) 0) (paperExcess (window q) (q-1) 0) → ℝ≥0)) :
    Tendsto distance atTop (𝓝 0) := by
  obtain ⟨M0,hM⟩ := full_prime_event_comparison_eventually hLS hShorey hPNT hNR
    betaMin betaMax 2 1 (1/6) band_constants.1 band_constants.2 (by norm_num) (by norm_num) (by norm_num)
  have he := (margin_exponential_nat_tendsto_zero 1 2 0 (by norm_num) (by norm_num)).const_mul 10
  have hp := (polynomial_error_nat_tendsto_zero (1/6) (by norm_num)).const_mul 4
  have hh : Tendsto (fun q ↦ 10*Real.exp (-saddleNu 1 (Real.log (window q)))+
      4*(window q:ℝ)^(-(1/(3:ℝ))+(1/6))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (he.add hp).comp window_tendsto
  apply squeeze_zero' (Eventually.of_forall (fun q ↦ massTotalVariation_nonneg _ _)) _ hh
  filter_upwards [scalar_regime 2,window_tendsto.eventually (eventually_ge_atTop M0),hsolution]
    with q hq hM0 hsol
  have hpos : 0 < infiniteRademacherMeasure.real Set.univ := by simp
  have hinfo : (0:ℝ)=eventInformation (Set.univ : Set InfiniteSample) := by
    simp [eventInformation]
  have hb := hM (window q) hM0 (q-1) 0 (by exact_mod_cast hq.1) (by exact_mod_cast hq.2.1)
    hq.2.2.1 hq.2.2.2.1 hq.2.2.2.2 Set.univ MeasurableSet.univ hpos hinfo hsol
  simpa [distance] using hb

end
end PaperC.Prel8.PrimeMicroscopicComparison
