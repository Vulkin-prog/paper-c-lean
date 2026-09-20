import PaperCPrel8.MicroscopicConditionalSpatial

/-! # Uniform untruncated marked comparison on the actual retained sites -/
namespace PaperC.Prel8.MicroscopicSpatialRates
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
noncomputable section
local instance : MeasurableSpace PaperC.F₂ := ⊤

/-- Every retained start lies in the physical interior interval. -/
theorem actual_starts_subset {M L : ℕ} {I : ℝ} (hend : M-L+1 ≤ M) :
    retainedStarts (actualSites M L I) ⊆ Finset.Icc 2 M := by
  intro x hx
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
  have hj := Finset.mem_Icc.mp (goodSites_subset M (M-L) L (paperExcess M L I) (primeCutoff M) hj)
  exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩

/-- The Poisson excess tail is uniformly absorbed at any fixed second-scale rate. -/
theorem target_tail_eventually (c' : ℝ) (_hc' : 0 < c') :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ, ∀ I : ℝ, 0 ≤ I →
      ∀ sites : Finset ℕ, sites.card ≤ M →
      (maskRate L sites:ℝ)/(2:ℝ)^(paperExcess M L I+1) ≤
        Real.exp (-c'*saddleNu 1 (Real.log M)) := by
  obtain ⟨Mv,hv⟩ := PaperC.V282.SaddlePoissonScales.saddle_exponential_le_eventually
    1 1 c' 1 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨Mv, ?_⟩
  intro M hM L I hI sites hs
  have hbulk := PaperC.Prel8.MicroscopicInformationCutoff.cutoff_tail_bound I
    (saddleCutoff 1 (Real.log M)) (PaperC.V282.AllStartSoftPoisson.fullRate M L).coe_nonneg
  have hcard : (maskRate L sites:ℝ) ≤ (PaperC.V282.AllStartSoftPoisson.fullRate M L:ℝ) := by
    change (sites.card:ℝ)/(2:ℝ)^L ≤ (M:ℝ)/(2:ℝ)^L
    exact div_le_div_of_nonneg_right (by exact_mod_cast hs) (by positivity)
  have hei : 1 ≤ Real.exp I := Real.one_le_exp_iff.mpr hI
  have he := hv M hM
  rw [Real.exp_le_one_iff] at he
  have hexp : Real.exp (-saddleCutoff 1 (Real.log M)) ≤
      Real.exp (-c'*saddleNu 1 (Real.log M)) := Real.exp_le_exp.mpr (by nlinarith)
  calc
    _ ≤ (PaperC.V282.AllStartSoftPoisson.fullRate M L:ℝ)/(2:ℝ)^(paperExcess M L I+1) :=
      div_le_div_of_nonneg_right hcard (by positivity)
    _ ≤ Real.exp I*(PaperC.V282.AllStartSoftPoisson.fullRate M L:ℝ)/(2:ℝ)^(paperExcess M L I+1) := by gcongr; exact le_mul_of_one_le_left (by positivity) hei
    _ ≤ Real.exp (-saddleCutoff 1 (Real.log M))/2 := hbulk
    _ ≤ _ := by linarith [Real.exp_pos (-saddleCutoff 1 (Real.log M))]

/-- Genuine spatial comparison retaining all excess marks, uniformly under the literal paper budget. -/
theorem retained_spatial_comparison_eventually
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
        (spatialMarkedSource (retainedStarts (actualSites M L I)) L))
        (spatialTargetLaw (retainedStarts (actualSites M L I)) L) ≤
      6*Real.exp (-c'*saddleNu 1 (Real.log M))+2*(M:ℝ)^(-(1/(3:ℝ))+epsilon) := by
  obtain ⟨Mg,hg⟩ := actual_geometry_eventually betaMin betaMax c hbetaMin hband (by linarith)
  obtain ⟨Mf,hf⟩ := retained_comparison_eventually hPNT betaMin betaMax c c' epsilon hbetaMin hband hc' hcc hepsilon
  obtain ⟨Ms,hs⟩ := tail_probability_eventually hLS hShorey hPNT hNR betaMin betaMax c c' hbetaMin hband (by linarith) hc'
  obtain ⟨Mt,ht⟩ := target_tail_eventually c' hc'
  refine ⟨max Mg (max Mf (max Ms Mt)), ?_⟩
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
  have g := hg M (by omega) L I hlo hhi hI hr hb
  have hsites := actual_starts_subset (I := I) g.interior_end
  have hcard : (retainedStarts (actualSites M L I)).card ≤ M := by
    have hh := Finset.card_le_card hsites
    simp only [Nat.card_Icc] at hh
    omega
  have hfinite := hf M (by omega) L I hlo hhi hI hr hb A hA hi hsol
  have hsource := hs M (by omega) L hlo hhi B hB hr (by rwa [hinfo])
    (retainedStarts (actualSites M L I)) hsites
  rw [hinfo] at hsource
  have htarget := ht M (by omega) L I hI _ hcard
  have h := spatial_distance_le_finite_and_tails (retainedStarts (actualSites M L I)) L
    (paperExcess M L I) B (measurableSet_traceEvent _ _ A) hB
  dsimp only [B] at h
  rw [conditional_vector_distance] at h
  change _ ≤ _ + retainedDistance M L I A + _ at h
  linarith

end
end PaperC.Prel8.MicroscopicSpatialRates
