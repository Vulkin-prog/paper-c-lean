import PaperCPrel8.InformationFieldTheorem
import PaperCV282.CentralResolutionBudget
import PaperCV282.MassPushforward

/-! # The paper's information-adapted labelled comparison, without extra band assumptions -/
namespace PaperC.Prel8.InformationFieldPaper
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
open PaperC.Prel8.InformationFieldTheorem
noncomputable section
local instance : MeasurableSpace PaperC.F₂ := ⊤
local instance : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- The enlarged cutoff never exceeds twice the hard one on their common domain. -/
theorem cutoff_two_le_twice_one {H : ℝ} (hH : max (saddleThreshold 1) (saddleThreshold 2) ≤ H) :
    saddleCutoff 2 H ≤ 2*saddleCutoff 1 H := by
  have hu1 : 1 ≤ saddleParameter 1 H := by
    linarith [(saddleParameter_spec (by norm_num : (0:ℝ)<1) ((le_max_left _ _).trans hH)).1,saddleParameterBase_ge_two]
  have hu2 : 1 ≤ saddleParameter 2 H := by
    linarith [(saddleParameter_spec (by norm_num : (0:ℝ)<2) ((le_max_right _ _).trans hH)).1,saddleParameterBase_ge_two]
  have hc := strictMonoOn_saddleCostParam.monotoneOn hu2 hu1 (parameter_two_le_one hH)
  unfold saddleCutoff
  linarith

/-- Proposition 6.2 at the literal source regime. The support band is a conclusion. -/
theorem paper_information_field (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (c c' epsilon : ℝ) (hc' : 0 < c') (hcc : c' < c)
    (hepsilon : 0 < epsilon) (heps : epsilon < 1/3) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      1 ≤ (fullRate N L:ℝ) → ∀ A : Set InfiniteSample,
      0 < infiniteRademacherMeasure.real A →
      eventInformation A ≤ saddleCutoff 1 (Real.log N) →
      MeasurableSet[MeasurableSpace.comap
        (restrictToFinite ⌊Real.exp (informationCutoff (Real.log N) (eventInformation A))⌋₊) inferInstance] A →
      Real.log (fullRate N L:ℝ) ≤ informationBudget (Real.log N) (eventInformation A)-
        c*(Real.log N/informationCutoff (Real.log N) (eventInformation A)) →
      spatialEventDistance N L A ≤
        67*Real.exp (-c'*(Real.log N/informationCutoff (Real.log N) (eventInformation A)))+
        64*(N:ℝ)^(-(1/(3:ℝ))+epsilon) := by
  obtain ⟨Nf,hf⟩ := information_field_in_band hAGG hPNT lowerConstant upperConstant c c' epsilon
    lowerConstant_pos lowerConstant_lt_upperConstant hc' hcc hepsilon heps
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Nb,hb⟩ := eventually_atTop.1 (central_common_band_eventually.and
    (hlog.eventually (eventually_ge_atTop (max (saddleThreshold 1) (saddleThreshold 2)))))
  refine ⟨max Nf Nb,?_⟩
  intro N hN L hr A hpos hIV hA hbudget
  have hdata := hb N (by omega)
  have hI := eventInformation_nonneg A hpos
  have hs := cutoff_spec hdata.2 hI hIV
  have hw := cutoff_pos hdata.2 hI hIV
  have hHp := (saddleThreshold_pos (by norm_num : (0:ℝ)<1)).trans_le ((le_max_left _ _).trans hdata.2)
  have hnu : 0 ≤ Real.log N/informationCutoff (Real.log N) (eventInformation A) := div_nonneg hHp.le hw.le
  have hbound : Real.log (fullRate N L:ℝ) ≤ saddleCutoff 1 (Real.log N) := by
    have hh := cutoff_two_le_twice_one hdata.2
    unfold informationBudget at hbudget
    nlinarith [mul_nonneg (by linarith : 0 ≤ c) hnu,hs.1.2]
  have hband := hdata.1 L hr hbound
  exact hf N (by omega) L hband.1 hband.2 hr A hpos hIV hA hbudget

/-- Every deterministic readout contracts the actual source and target before any bound is used. -/
theorem statistic_distance_le {T : Type*} (N L : ℕ) (A : Set InfiniteSample)
    (hpos : 0 < infiniteRademacherMeasure.real A) (f : SpatialMarkedConfig N → T) :
    massTotalVariation
      (pushforwardMass f (conditionalObservableLaw infiniteRademacherMeasure A (spatialMarkedSource N L)))
      (pushforwardMass f (spatialTargetLaw N L)) ≤ spatialEventDistance N L A :=
  massTotalVariation_pushforward_le f
    (hasSum_conditionalObservableLaw _ _ hpos (measurable_spatialMarkedSource N L))
    (hasSum_spatialTargetLaw N L) (conditionalObservableLaw_nonneg _ _ _) (spatialTargetLaw_nonneg N L)

end
end PaperC.Prel8.InformationFieldPaper
