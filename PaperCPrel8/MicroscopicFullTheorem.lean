import PaperCPrel8.MicroscopicDeletedTarget

/-! # Uniform untruncated marked comparison on the actual retained sites -/
namespace PaperC.Prel8.MicroscopicFullTheorem
open MeasureTheory PaperC.InfiniteRademacher PaperC.ConditionalStartProbability
open PaperC.Prel8.MicroscopicConditionalSpatial PaperC.Prel8.MicroscopicRetainedTheorem
open PaperC.Prel8.MicroscopicActualGeometry PaperC.Prel8.MicroscopicProfileBudget
open PaperC.Prel8.MicroscopicPaperBudget PaperC.Prel8.MicroscopicValueProfile
open PaperC.Prel8.MicroscopicGoodField PaperC.Prel8.MicroscopicDiscardTheorem
open PaperC.Prel8.ActualSignedPalm
open PaperC.V282.RareConditioningRates PaperC.V282.SaddleParameters PaperC.V282.SaddleScales
open PaperC.V282.BulkMarkedSource PaperC.V282.BulkMarkedComparison
open PaperC.V282.ConditionedCountableLaw PaperC.V282.FiniteFieldTotalVariation
open PaperC.V282.FiniteStartMaskAverages PaperC.V282.DirectionalSteinInput
open PaperC.V282.LaishramUniformInput PaperC.V282.PostQuadraticLiterature PaperC.V282.PrimeEulerPNT
open PaperC.ArratiaGoldsteinGordonInput
open scoped NNReal
open PaperC.Prel8.MicroscopicSpatialRates PaperC.Prel8.MicroscopicDeletedTarget
open PaperC.Prel8.MicroscopicSiteRestoration
open PaperC.InfiniteCylinderTransfer PaperC.V282.InfiniteConditionalWords
open PaperC.V282.PrimeFieldEventConditioning
noncomputable section
local instance : MeasurableSpace PaperC.F₂ := ⊤


/-- All interior starts, signs and excesses with one common uniform scale threshold. -/
theorem full_spatial_comparison_eventually
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeNumberTheoremRemainder) (hNR : PaperC.PellInput.NicolasRobinDivisorLogBoundStatement)
    (betaMin betaMax c c' epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hband : betaMin < betaMax) (hc' : 0 < c') (hcc : c' < c) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ, ∀ I : ℝ,
      betaMin*Real.log M ≤ (L+1:ℝ) → (L+1:ℝ) ≤ betaMax*Real.log M →
      0 ≤ I → 1 ≤ siteRate M L →
      I+Real.log (siteRate M L) ≤ saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M) →
      ∀ A : SmallSample (sourceCylinder M L I) (primeCutoff M) → Prop,
      0 < eventProbability (FinitePMF.uniform (SampleSpace (sourceCylinder M L I)))
        (fun ω => A (restrictSmall (sourceCylinder M L I) (primeCutoff M) ω)) →
      I = -Real.log (eventProbability (FinitePMF.uniform (SampleSpace (sourceCylinder M L I)))
        (fun ω => A (restrictSmall (sourceCylinder M L I) (primeCutoff M) ω))) →
      DirectionalSolutionBounds (rate L : Index (actualSites M L I) (paperExcess M L I) → ℝ≥0) →
      massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure
        (traceEvent (sourceCylinder M L I) (primeCutoff M) A)
        (spatialMarkedSource (interiorStarts M L) L))
        (spatialTargetLaw (interiorStarts M L) L) ≤
      10*Real.exp (-c'*saddleNu 1 (Real.log M))+4*(M:ℝ)^(-(1/(3:ℝ))+epsilon) := by
  obtain ⟨Mf,hf⟩ := retained_spatial_comparison_eventually hLS hShorey hPNT hNR
    betaMin betaMax c c' epsilon hbetaMin hband hc' hcc hepsilon
  obtain ⟨Ms,hs⟩ := deleted_probability_eventually hLS hShorey hPNT hNR
    betaMin betaMax c c' epsilon hbetaMin hband hc' hcc hepsilon
  obtain ⟨Mt,ht⟩ := deleted_target_rate_eventually hPNT
    betaMin betaMax c c' epsilon hbetaMin hband hc' hcc hepsilon
  refine ⟨max Mf (max Ms Mt), ?_⟩
  intro M hM L I hlo hhi hI hr hb A hA hi hsol
  let B := traceEvent (sourceCylinder M L I) (primeCutoff M) A
  have hB : 0 < infiniteRademacherMeasure.real B := by
    dsimp only [B]
    rwa [traceEvent_probability]
  have hinfo : eventInformation B = I := by
    unfold eventInformation
    dsimp only [B]
    rw [traceEvent_probability]
    exact hi.symm
  have hfinite := hf M (by omega) L I hlo hhi hI hr hb A hA hi hsol
  have hsource := hs M (by omega) L hlo hhi B hB hr (by rwa [hinfo])
  rw [hinfo] at hsource
  have htarget := ht M (by omega) L I hlo hhi hI hr hb
  have h := conditional_restoration_by_hit (retained_subset_interior M L I) L B
    (measurableSet_traceEvent _ _ A) hB
  rw [interior_difference] at h
  linarith


/-- Every positive event of the full small-prime sigma-algebra is covered. -/
theorem full_prime_event_comparison_eventually
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeNumberTheoremRemainder) (hNR : PaperC.PellInput.NicolasRobinDivisorLogBoundStatement)
    (betaMin betaMax c c' epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hband : betaMin < betaMax) (hc' : 0 < c') (hcc : c' < c) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ, ∀ I : ℝ,
      betaMin*Real.log M ≤ (L+1:ℝ) → (L+1:ℝ) ≤ betaMax*Real.log M →
      0 ≤ I → 1 ≤ siteRate M L →
      I+Real.log (siteRate M L) ≤ saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M) →
      ∀ A : Set InfiniteSample,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (primeCutoff M)) inferInstance] A →
      0 < infiniteRademacherMeasure.real A → I = eventInformation A →
      DirectionalSolutionBounds (rate L : Index (actualSites M L I) (paperExcess M L I) → ℝ≥0) →
      massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure A
        (spatialMarkedSource (interiorStarts M L) L)) (spatialTargetLaw (interiorStarts M L) L) ≤
      10*Real.exp (-c'*saddleNu 1 (Real.log M))+4*(M:ℝ)^(-(1/(3:ℝ))+epsilon) := by
  obtain ⟨Mg,hg⟩ := actual_geometry_eventually betaMin betaMax c hbetaMin hband (by linarith)
  obtain ⟨Mf,hf⟩ := full_spatial_comparison_eventually hLS hShorey hPNT hNR
    betaMin betaMax c c' epsilon hbetaMin hband hc' hcc hepsilon
  refine ⟨max Mg Mf, ?_⟩
  intro M hM L I hlo hhi hI hr hb A hA hpos hi hsol
  have g := hg M (by omega) L I hlo hhi hI hr hb
  rw [← smallPrimeSigmaAlgebra_eq_primeCylinder g.prime_in_cylinder] at hA
  obtain ⟨S,hS⟩ := measurableSet_eq_primeFieldEvent hA
  have he : A = traceEvent (sourceCylinder M L I) (primeCutoff M) (fun σ => σ ∈ S) := hS
  have hp : 0 < eventProbability (FinitePMF.uniform (SampleSpace (sourceCylinder M L I)))
      (fun ω => restrictSmall (sourceCylinder M L I) (primeCutoff M) ω ∈ S) := by
    rw [← traceEvent_probability,← he]
    exact hpos
  have hinfo : I = -Real.log (eventProbability (FinitePMF.uniform (SampleSpace (sourceCylinder M L I)))
      (fun ω => restrictSmall (sourceCylinder M L I) (primeCutoff M) ω ∈ S)) := by
    rw [← traceEvent_probability,← he]
    exact hi
  have h := hf M (by omega) L I hlo hhi hI hr hb (fun σ => σ ∈ S) hp hinfo hsol
  rwa [← he] at h

end
end PaperC.Prel8.MicroscopicFullTheorem
