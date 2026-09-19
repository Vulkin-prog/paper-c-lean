import PaperCPrel8.InformationFieldPaper
import PaperCPrel8.PrescribedInformationField
import PaperCPrel8.DyadicRestriction
import PaperCV282.CentralResolutionBudget
import PaperCV282.MassPushforward

/-! # The paper's information-adapted labelled comparison, without extra band assumptions -/
namespace PaperC.Prel8.PrescribedInformationPaper
open Filter Topology MeasureTheory
open PaperC.InfiniteRademacher PaperC.InfiniteCylinderTransfer PaperC.CriticalRunWindow
open PaperC.V282.SpatialMarkedEventComparison PaperC.V282.SpatialMarkedSource PaperC.V282.SpatialMarkedTarget
open PaperC.V282.SpatialMarkedFieldComparison
open PaperC.V282.SpatialMarkedTypes PaperC.V282.ConditionedCountableLaw
open PaperC.V282.FiniteFieldTotalVariation PaperC.V282.MassPushforward
open PaperC.V282.RareConditioningRates PaperC.V282.AllStartSoftPoisson
open PaperC.V282.SaddleParameters PaperC.V282.ExponentialIntegral
open PaperC.V282.PrimeEulerPNT PaperC.V282.ProcessAGGInput PaperC.V282.CentralResolutionBudget
open PaperC.Prel8.InformationSaddle PaperC.Prel8.InformationSaddleBudget
open PaperC.Prel8.InformationFieldPaper PrescribedInformationField InformationBudget
noncomputable section
local instance : MeasurableSpace PaperC.F₂ := ⊤
local instance : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- Full-field comparison at any admissible cutoff. The support band follows from the budget. -/
theorem paper_prescribed_field (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (c c' epsilon : ℝ) (hc' : 0 < c') (hcc : c' < c)
    (hepsilon : 0 < epsilon) (heps : epsilon < 1/3) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ, ∀ w : ℝ,
      saddleCutoff 1 (Real.log N)≤w → w≤saddleCutoff 2 (Real.log N) →
      1 ≤ (fullRate N L:ℝ) → ∀ A : Set InfiniteSample,
      0 < infiniteRademacherMeasure.real A →
      eventInformation A ≤ saddleCutoff 1 (Real.log N) →
      MeasurableSet[MeasurableSpace.comap
        (restrictToFinite ⌊Real.exp (w)⌋₊) inferInstance] A →
      Real.log (fullRate N L:ℝ) ≤ budget (fun v ↦ saddleCost (Real.log N/v)) (eventInformation A) w-
        c*(Real.log N/w) →
      spatialEventDistance N L A ≤
        67*Real.exp (-c'*(Real.log N/w))+
        64*(N:ℝ)^(-(1/(3:ℝ))+epsilon) := by
  obtain ⟨Nf,hf⟩ := prescribed_field_in_band hAGG hPNT lowerConstant upperConstant c c' epsilon
    lowerConstant_pos lowerConstant_lt_upperConstant hc' hcc hepsilon heps
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Nb,hb⟩ := eventually_atTop.1 (central_common_band_eventually.and
    (hlog.eventually (eventually_ge_atTop (max (saddleThreshold 1) (saddleThreshold 2)))))
  refine ⟨max Nf Nb,?_⟩
  intro N hN L w hwV hwHat hr A hpos hIV hA hbudget
  have hdata := hb N (by omega)
  have hI := eventInformation_nonneg A hpos
  have hw := (saddleCutoff_pos (by norm_num : (0:ℝ)<1) ((le_max_left _ _).trans hdata.2)).trans_le hwV
  have hHp := (saddleThreshold_pos (by norm_num : (0:ℝ)<1)).trans_le ((le_max_left _ _).trans hdata.2)
  have hnu : 0 ≤ Real.log N/w := div_nonneg hHp.le hw.le
  have hbound : Real.log (fullRate N L:ℝ) ≤ saddleCutoff 1 (Real.log N) := by
    have hh := cutoff_two_le_twice_one hdata.2
    have hbud := min_le_right (saddleCost (Real.log N/w)-eventInformation A) ((w-eventInformation A)/2)
    change Real.log (fullRate N L:ℝ) ≤ min _ _-c*(Real.log N/w) at hbudget
    nlinarith [mul_nonneg (by linarith : 0 ≤ c) hnu]
  have hband := hdata.1 L hr hbound
  exact hf N (by omega) L w hwV hwHat hband.1 hband.2 hr A hpos hIV hA hbudget


/-- The prescribed sigma-field is respected at the constrained maximizing cutoff. -/
theorem optimized_floor_field (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (c c' epsilon : ℝ) (hc' : 0<c') (hcc : c'<c)
    (hepsilon : 0<epsilon) (heps : epsilon<1/3) :
    ∃ N0 : ℕ, ∀ N≥N0, ∀ L : ℕ, ∀ w0 : ℝ,
      saddleCutoff 1 (Real.log N)≤w0 → w0≤saddleCutoff 2 (Real.log N) →
      1≤(fullRate N L:ℝ) → ∀ A : Set InfiniteSample,
      0 < infiniteRademacherMeasure.real A → eventInformation A≤saddleCutoff 1 (Real.log N) →
      MeasurableSet[MeasurableSpace.comap (restrictToFinite ⌊Real.exp w0⌋₊) inferInstance] A →
      let w := max w0 (informationCutoff (Real.log N) (eventInformation A))
      Real.log (fullRate N L:ℝ)≤budget (fun v ↦ saddleCost (Real.log N/v)) (eventInformation A) w-c*(Real.log N/w) →
      spatialEventDistance N L A≤67*Real.exp (-c'*(Real.log N/w))+64*(N:ℝ)^(-(1/(3:ℝ))+epsilon) := by
  obtain ⟨Np,hp⟩ := paper_prescribed_field hAGG hPNT c c' epsilon hc' hcc hepsilon heps
  have hlog : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Nh,hh⟩ := eventually_atTop.mp (hlog.eventually (eventually_ge_atTop (max (saddleThreshold 1) (saddleThreshold 2))))
  refine ⟨max Np Nh,?_⟩
  intro N hN L w0 hw0 hw1 hr A hpos hI hA
  dsimp only
  intro hb
  have hs := cutoff_spec (hh N (by omega)) (eventInformation_nonneg A hpos) hI
  have hmono : ⌊Real.exp w0⌋₊≤⌊Real.exp (max w0 (informationCutoff (Real.log N) (eventInformation A)))⌋₊ :=
    Nat.floor_mono (Real.exp_le_exp.mpr (le_max_left _ _))
  exact hp N (by omega) L _ (hw0.trans (le_max_left _ _)) (max_le hw1 hs.1.2) hr A hpos hI
    (DyadicRestriction.prime_sigma_mono hmono A hA) hb

end
end PaperC.Prel8.PrescribedInformationPaper
