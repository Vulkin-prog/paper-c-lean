import PaperCPrel8.DyadicBudget

/-! # The same-grid signed dyadic field at the one-factor information budget -/
namespace PaperC.Prel8.DyadicMicroscopicTheorem
open MeasureTheory Filter Topology PaperC.InfiniteRademacher PaperC.InfiniteCylinderTransfer
open PaperC.Prel8.DyadicBudget PaperC.Prel8.DyadicRestriction
open PaperC.Prel8.MicroscopicFullTheorem PaperC.Prel8.MicroscopicNormalization
open PaperC.Prel8.MicroscopicActualGeometry PaperC.Prel8.MicroscopicProfileBudget
open PaperC.Prel8.MicroscopicRetainedTheorem PaperC.Prel8.ActualSignedPalm
open PaperC.V282.BulkMarkedSource PaperC.V282.BulkMarkedComparison
open PaperC.V282.ConditionedCountableLaw PaperC.V282.FiniteFieldTotalVariation
open PaperC.V282.RareConditioningRates PaperC.V282.AllStartSoftPoisson
open PaperC.V282.SaddleParameters PaperC.V282.SaddleScales PaperC.V282.DirectionalSteinInput
open PaperC.V282.LaishramUniformInput PaperC.V282.PostQuadraticLiterature PaperC.V282.PrimeEulerPNT
open scoped NNReal
noncomputable section
local instance : MeasurableSpace PaperC.F₂ := ⊤
local instance : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- Uniform dyadic comparison with the original smaller prime field and exact integer labels. -/
theorem dyadic_comparison_eventually
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeNumberTheoremRemainder) (hNR : PaperC.PellInput.NicolasRobinDivisorLogBoundStatement)
    (betaMin betaMax c c' epsilon : ℝ) (hmin : 0 < betaMin) (hband : betaMin < betaMax)
    (hc' : 0 < c') (hcc : c' < c) (hepsilon : 0 < epsilon) (hepsMax : epsilon < 1/3) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin*Real.log N ≤ (L+1:ℝ) → (L+1:ℝ) ≤ betaMax*Real.log N →
      1 ≤ (fullRate N L:ℝ) → ∀ A : Set InfiniteSample,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (primeCutoff N)) inferInstance] A →
      0 < infiniteRademacherMeasure.real A →
      eventInformation A+Real.log (fullRate N L:ℝ) ≤
        saddleCutoff 1 (Real.log N)-c*saddleNu 1 (Real.log N) →
      DirectionalSolutionBounds (rate L : Index (actualSites (4*N) L (eventInformation A))
        (paperExcess (4*N) L (eventInformation A)) → ℝ≥0) →
      massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure A
        (spatialMarkedSource (Finset.Ico N (2*N)) L)) (spatialTargetLaw (Finset.Ico N (2*N)) L) ≤
        10*Real.exp (-c'*saddleNu 1 (Real.log N))+4*(N:ℝ)^(-(1/(3:ℝ))+epsilon) := by
  let a := (c+c')/2
  have ha : 0 < a := by dsimp [a]; linarith
  have hca : c' < a := by dsimp [a]; linarith
  have hac : a < c := by dsimp [a]; linarith
  obtain ⟨Nf,hf⟩ := full_prime_event_comparison_eventually hLS hShorey hPNT hNR
    (betaMin/2) betaMax a c' epsilon (by positivity) (by linarith) hc' hca hepsilon
  obtain ⟨Ng,hg⟩ := enlarged_band_eventually betaMin betaMax hmin hband
  obtain ⟨Nb,hb⟩ := dyadic_budget_eventually c a ha hac
  obtain ⟨Ns,hs⟩ := hard_dilation_eventually
  refine ⟨max 2 (max Nf (max Ng (max Nb Ns))), ?_⟩
  intro N hN L hlo hhi hr A hm hp hbudget hsol
  obtain ⟨hL,hlo',hhi'⟩ := hg N (by omega) L hlo hhi
  obtain ⟨hr',hb'⟩ := hb N (by omega) L hL (eventInformation A) hr hbudget
  obtain ⟨hcut,hnu⟩ := hs N (by omega)
  have hm' : MeasurableSet[MeasurableSpace.comap (restrictToFinite (primeCutoff (4*N))) inferInstance] A :=
    prime_sigma_mono hcut A hm
  have hfull := hf (4*N) (by omega) L (eventInformation A) hlo' hhi'
    (eventInformation_nonneg A hp) hr' hb' A hm' hp rfl hsol
  have hres := spatial_restriction_tv_le (dyadic_subset_prefix (by omega : 2≤N) hL) L A hp
  have hexp := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hnu (by linarith : -c'≤0))
  have hn : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hpow : ((4*N:ℕ):ℝ)^(-(1/(3:ℝ))+epsilon) ≤ (N:ℝ)^(-(1/(3:ℝ))+epsilon) :=
    Real.rpow_le_rpow_of_nonpos hn (by push_cast; linarith) (by linarith)
  exact hres.trans (hfull.trans (by gcongr))

/-- Literal moving-depth dyadic normalization, without enlarging the allowed conditioning field. -/
theorem paper_dyadic_comparison_eventually
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeNumberTheoremRemainder) (hNR : PaperC.PellInput.NicolasRobinDivisorLogBoundStatement)
    (c c' epsilon : ℝ) (hc' : 0 < c') (hcc : c' < c)
    (hepsilon : 0 < epsilon) (hepsMax : epsilon < 1/3)
    (depth : ℕ → ℕ) (events : ℕ → Set InfiniteSample)
    (hdepth : Tendsto (fun N : ℕ => (depth N:ℝ)/Real.log N) atTop (𝓝 0))
    (hintensity : Tendsto (fun N : ℕ => (fullRate N (paperLength N (depth N)):ℝ)) atTop atTop)
    (hregime : ∀ᶠ N : ℕ in atTop,
      eventInformation (events N)+Real.log (fullRate N (paperLength N (depth N)):ℝ) ≤
        saddleCutoff 1 (Real.log N)-c*saddleNu 1 (Real.log N) ∧
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (primeCutoff N)) inferInstance] (events N) ∧
      0 < infiniteRademacherMeasure.real (events N) ∧
      DirectionalSolutionBounds (rate (paperLength N (depth N)) :
        Index (actualSites (4*N) (paperLength N (depth N)) (eventInformation (events N)))
          (paperExcess (4*N) (paperLength N (depth N)) (eventInformation (events N))) → ℝ≥0)) :
    ∀ᶠ N : ℕ in atTop,
      massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure (events N)
        (spatialMarkedSource (Finset.Ico N (2*N)) (paperLength N (depth N))))
        (spatialTargetLaw (Finset.Ico N (2*N)) (paperLength N (depth N))) ≤
      10*Real.exp (-c'*saddleNu 1 (Real.log N))+4*(N:ℝ)^(-(1/(3:ℝ))+epsilon) := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hband : 1/(2*Real.log 2) < 2/Real.log 2 := by
    apply (div_lt_iff₀ (by positivity : 0<2*Real.log 2)).mpr
    field_simp
    norm_num
  obtain ⟨Nzero,hmain⟩ := dyadic_comparison_eventually hLS hShorey hPNT hNR
    (1/(2*Real.log 2)) (2/Real.log 2) c c' epsilon (by positivity) hband hc' hcc hepsilon hepsMax
  filter_upwards [eventually_ge_atTop Nzero,paper_length_band depth hdepth,
    hintensity.eventually (eventually_ge_atTop 1),hregime] with N hN hlen hr hreg
  obtain ⟨hb,hm,hp,hsol⟩ := hreg
  exact hmain N hN (paperLength N (depth N)) hlen.2.1 hlen.2.2 hr (events N) hm hp hb hsol

end
end PaperC.Prel8.DyadicMicroscopicTheorem
