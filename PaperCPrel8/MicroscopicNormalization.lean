import PaperCPrel8.MicroscopicReadouts

/-! # The paper's moving-depth normalization supplies the fixed logarithmic band -/
namespace PaperC.Prel8.MicroscopicNormalization
open Filter Topology MeasureTheory PaperC.InfiniteRademacher PaperC.InfiniteCylinderTransfer
open PaperC.Prel8.MicroscopicFullTheorem PaperC.Prel8.MicroscopicReadouts
open PaperC.Prel8.MicroscopicSiteRestoration PaperC.Prel8.MicroscopicRetainedTheorem
open PaperC.Prel8.MicroscopicActualGeometry PaperC.Prel8.MicroscopicProfileBudget
open PaperC.Prel8.MicroscopicPaperBudget PaperC.Prel8.ActualSignedPalm
open PaperC.V282.RareConditioningRates PaperC.V282.DirectionalSteinInput
open PaperC.V282.LaishramUniformInput PaperC.V282.PostQuadraticLiterature PaperC.V282.PrimeEulerPNT
open PaperC.V282.BulkMarkedSource PaperC.V282.BulkMarkedComparison
open PaperC.V282.ConditionedCountableLaw PaperC.V282.FiniteFieldTotalVariation
open PaperC.V282.SaddleParameters PaperC.V282.SaddleScales
open scoped NNReal
noncomputable section
local instance : MeasurableSpace PaperC.F₂ := ⊤
local instance : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

def paperLength (M depth : ℕ) : ℕ := ⌊Real.log M/Real.log 2⌋₊-depth

/-- The natural subtraction is legitimate, and fixed bands follow from a=o(log M). -/
theorem paper_length_band (depth : ℕ → ℕ)
    (hdepth : Tendsto (fun M : ℕ => (depth M:ℝ)/Real.log M) atTop (𝓝 0)) :
    ∀ᶠ M : ℕ in atTop,
      depth M ≤ ⌊Real.log M/Real.log 2⌋₊ ∧
      (1/(2*Real.log 2))*Real.log M ≤ (paperLength M (depth M)+1:ℝ) ∧
      (paperLength M (depth M)+1:ℝ) ≤ (2/Real.log 2)*Real.log M := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hd := hdepth.eventually (gt_mem_nhds (by positivity : (0:ℝ)<1/(4*Real.log 2)))
  filter_upwards [hd,hlog.eventually (eventually_ge_atTop (4*Real.log 2))] with M hd hM
  have hlogpos : 0 < Real.log M := by linarith
  have hsmall : (depth M:ℝ) ≤ Real.log M/(4*Real.log 2) := by
    have := (div_lt_iff₀ hlogpos).mp hd
    nlinarith [show (1/(4*Real.log 2))*Real.log M=Real.log M/(4*Real.log 2) by ring]
  have htau : 4 ≤ Real.log M/Real.log 2 := (le_div_iff₀ htwo).mpr (by linarith)
  have hfloor := Nat.floor_le (by positivity : 0 ≤ Real.log M/Real.log 2)
  have hround := Nat.lt_floor_add_one (Real.log M/Real.log 2)
  have hscale : Real.log M/(4*Real.log 2) = (Real.log M/Real.log 2)/4 := by ring
  rw [hscale] at hsmall
  have ha : (depth M:ℝ) ≤ (⌊Real.log M/Real.log 2⌋₊:ℝ) := by linarith
  have han : depth M ≤ ⌊Real.log M/Real.log 2⌋₊ := by exact_mod_cast ha
  refine ⟨han, ?_, ?_⟩
  · unfold paperLength
    rw [Nat.cast_sub han]
    have hscale : (1/(2*Real.log 2))*Real.log M = (Real.log M/Real.log 2)/2 := by ring
    rw [hscale]
    linarith
  · unfold paperLength
    rw [Nat.cast_sub han]
    have hscale : (2/Real.log 2)*Real.log M = 2*(Real.log M/Real.log 2) := by ring
    rw [hscale]
    have := Nat.cast_nonneg (α := ℝ) (depth M)
    linarith

/-- The quantitative full-field endpoint in the literal moving-depth normalization of 7.7. -/
theorem paper_comparison_eventually
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeNumberTheoremRemainder) (hNR : PaperC.PellInput.NicolasRobinDivisorLogBoundStatement)
    (c c' epsilon : ℝ) (hc' : 0 < c') (hcc : c' < c) (hepsilon : 0 < epsilon)
    (depth : ℕ → ℕ) (events : ℕ → Set InfiniteSample)
    (hdepth : Tendsto (fun M : ℕ => (depth M:ℝ)/Real.log M) atTop (𝓝 0))
    (hintensity : Tendsto (fun M : ℕ => siteRate M (paperLength M (depth M))) atTop atTop)
    (hregime : ∀ᶠ M : ℕ in atTop,
      eventInformation (events M)+Real.log (siteRate M (paperLength M (depth M))) ≤
        saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M) ∧
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (primeCutoff M)) inferInstance] (events M) ∧
      0 < infiniteRademacherMeasure.real (events M) ∧
      DirectionalSolutionBounds (rate (paperLength M (depth M)) :
        Index (actualSites M (paperLength M (depth M)) (eventInformation (events M)))
          (paperExcess M (paperLength M (depth M)) (eventInformation (events M))) → ℝ≥0)) :
    ∀ᶠ M : ℕ in atTop,
      massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure (events M)
        (spatialMarkedSource (interiorStarts M (paperLength M (depth M))) (paperLength M (depth M))))
        (spatialTargetLaw (interiorStarts M (paperLength M (depth M))) (paperLength M (depth M))) ≤
      10*Real.exp (-c'*saddleNu 1 (Real.log M))+4*(M:ℝ)^(-(1/(3:ℝ))+epsilon) := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hband : 1/(2*Real.log 2) < 2/Real.log 2 := by
    apply (div_lt_iff₀ (by positivity : 0<2*Real.log 2)).mpr
    field_simp
    norm_num
  obtain ⟨Mzero,hmain⟩ := full_prime_event_comparison_eventually hLS hShorey hPNT hNR
    (1/(2*Real.log 2)) (2/Real.log 2) c c' epsilon (by positivity) hband hc' hcc hepsilon
  filter_upwards [eventually_ge_atTop Mzero,paper_length_band depth hdepth,
    hintensity.eventually (eventually_ge_atTop 1),hregime] with M hM hlen hr hreg
  obtain ⟨hb,hm,hp,hsol⟩ := hreg
  exact hmain M hM (paperLength M (depth M)) (eventInformation (events M)) hlen.2.1 hlen.2.2
    (eventInformation_nonneg _ hp) hr hb (events M) hm hp rfl hsol

end
end PaperC.Prel8.MicroscopicNormalization
