import PaperCPrel8.MicroscopicFullTheorem
import PaperCV282.MacroTransportStatistics

/-! # Arbitrary measurable readouts and vanishing uniform microscopic error -/
namespace PaperC.Prel8.MicroscopicReadouts
open MeasureTheory ProbabilityTheory Filter Topology PaperC.InfiniteRademacher
open PaperC.Prel8.MicroscopicSiteRestoration
open PaperC.V282.BulkMarkedTypes PaperC.V282.BulkMarkedSource
open PaperC.V282.BulkMarkedTarget PaperC.V282.BulkMarkedComparison
open PaperC.V282.ConditionedCountableLaw PaperC.V282.MacroTransportStatistics
open PaperC.V282.MacroTransportRestoration PaperC.V282.SharpConditioning
open PaperC.V282.FiniteFieldTotalVariation PaperC.V282.SaddleParameters PaperC.V282.SaddleScales
open PaperC.Prel8.MicroscopicFullTheorem PaperC.Prel8.MicroscopicRetainedTheorem
open PaperC.Prel8.MicroscopicActualGeometry PaperC.Prel8.MicroscopicProfileBudget
open PaperC.Prel8.MicroscopicPaperBudget PaperC.Prel8.ActualSignedPalm
open PaperC.V282.RareConditioningRates PaperC.V282.DirectionalSteinInput
open PaperC.V282.LaishramUniformInput PaperC.V282.PostQuadraticLiterature PaperC.V282.PrimeEulerPNT
open PaperC.InfiniteCylinderTransfer
open scoped NNReal
noncomputable section
local instance : MeasurableSpace PaperC.F₂ := ⊤
local instance : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- Every measurable output space is allowed, without a continuity or mesh assumption. -/
theorem measurable_readout_le {α : Type*} [MeasurableSpace α]
    (M L : ℕ) (A : Set InfiniteSample) (hpos : 0 < infiniteRademacherMeasure.real A)
    (stat : SpatialMarkedConfig (interiorStarts M L) → α) (hstat : Measurable stat) :
    measureTotalVariation
      ((cond infiniteRademacherMeasure A).map (stat ∘ spatialMarkedSource (interiorStarts M L) L))
      ((spatialTargetMeasure (interiorStarts M L) L).map stat) ≤
      massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure A
        (spatialMarkedSource (interiorStarts M L) L)) (spatialTargetLaw (interiorStarts M L) L) := by
  let : IsProbabilityMeasure (cond infiniteRademacherMeasure A) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hpos)
  let μ := (cond infiniteRademacherMeasure A).map (spatialMarkedSource (interiorStarts M L) L)
  have hsource := measurable_spatialMarkedSource (interiorStarts M L) L
  let : IsProbabilityMeasure μ := (Measure.isProbabilityMeasure_map_iff hsource.aemeasurable).mpr inferInstance
  have h := measureTotalVariation_map_le μ (spatialTargetMeasure (interiorStarts M L) L) hstat
  dsimp only [μ] at h
  rw [Measure.map_map hstat hsource,map_distance_eq_mass _ _ hsource] at h
  exact h

/-- The explicit full-field error tends to zero at precisely the stated polynomial range. -/
theorem full_error_tendsto_zero (c' epsilon : ℝ) (hc' : 0 < c') (hepsilon : epsilon < 1/3) :
    Tendsto (fun M : ℕ => 10*Real.exp (-c'*saddleNu 1 (Real.log M))+
      4*(M:ℝ)^(-(1/(3:ℝ))+epsilon)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hnu := (tendsto_saddleNu_atTop (a := 1) (by norm_num)).comp hlog
  have he := Real.tendsto_exp_atBot.comp (hnu.const_mul_atTop_of_neg (neg_neg_iff_pos.mpr hc'))
  have hp := (tendsto_rpow_neg_atTop (by linarith : (0:ℝ)<1/3-epsilon)).comp tendsto_natCast_atTop_atTop
  simpa only [Function.comp_def,mul_zero,add_zero,
    show -(1/3-epsilon)= -(1/(3:ℝ))+epsilon by ring] using (he.const_mul 10).add (hp.const_mul 4)

/-- Convergence of actual varying fields follows from the source regime, not a convergence premise. -/
theorem full_distance_tendsto_zero
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeNumberTheoremRemainder) (hNR : PaperC.PellInput.NicolasRobinDivisorLogBoundStatement)
    (betaMin betaMax c c' epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hband : betaMin < betaMax) (hc' : 0 < c') (hcc : c' < c)
    (hepsilon : 0 < epsilon) (hepsMax : epsilon < 1/3)
    (length : ℕ → ℕ) (events : ℕ → Set InfiniteSample)
    (hregime : ∀ᶠ M : ℕ in atTop,
      betaMin*Real.log M ≤ (length M+1:ℝ) ∧ (length M+1:ℝ) ≤ betaMax*Real.log M ∧
      1 ≤ siteRate M (length M) ∧
      eventInformation (events M)+Real.log (siteRate M (length M)) ≤
        saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M) ∧
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (primeCutoff M)) inferInstance] (events M) ∧
      0 < infiniteRademacherMeasure.real (events M) ∧
      DirectionalSolutionBounds (rate (length M) :
        Index (actualSites M (length M) (eventInformation (events M)))
          (paperExcess M (length M) (eventInformation (events M))) → ℝ≥0)) :
    Tendsto (fun M : ℕ => massTotalVariation
      (conditionalObservableLaw infiniteRademacherMeasure (events M)
        (spatialMarkedSource (interiorStarts M (length M)) (length M)))
      (spatialTargetLaw (interiorStarts M (length M)) (length M))) atTop (𝓝 0) := by
  obtain ⟨Mzero,hmain⟩ := full_prime_event_comparison_eventually hLS hShorey hPNT hNR
    betaMin betaMax c c' epsilon hbetaMin hband hc' hcc hepsilon
  have hbound : ∀ᶠ M : ℕ in atTop,
      massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure (events M)
        (spatialMarkedSource (interiorStarts M (length M)) (length M)))
        (spatialTargetLaw (interiorStarts M (length M)) (length M)) ≤
        10*Real.exp (-c'*saddleNu 1 (Real.log M))+4*(M:ℝ)^(-(1/(3:ℝ))+epsilon) := by
    filter_upwards [eventually_ge_atTop Mzero,hregime] with M hM hreg
    obtain ⟨hlo,hhi,hr,hb,hm,hp,hsol⟩ := hreg
    exact hmain M hM (length M) (eventInformation (events M)) hlo hhi
      (eventInformation_nonneg _ hp) hr hb (events M) hm hp rfl hsol
  exact squeeze_zero' (Eventually.of_forall fun _ => massTotalVariation_nonneg _ _)
    hbound (full_error_tendsto_zero c' epsilon hc' hepsMax)

end
end PaperC.Prel8.MicroscopicReadouts
