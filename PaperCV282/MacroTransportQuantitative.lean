import PaperCV282.MacroTransportHardComparison
import PaperCV282.MacroTransportInformation
import PaperCV282.RareConditioningRates

/-! # The quantitative hard macroscopic transfer with an unweighted microscopic remainder -/
namespace PaperC.V282.MacroTransportQuantitative

open MeasureTheory ProbabilityTheory Filter Topology InfiniteRademacher InfiniteCylinderTransfer
open MacroTransportModel MacroTransportHardComparison MacroTransportInformation
open HardPoissonRates SaddleParameters SaddleScales PrimeEulerPNT ProcessAGGInput AllStartSoftPoisson
open LaishramUniformInput PostQuadraticLiterature RareConditioningRates SharpConditioning ConditionedCountableLaw

noncomputable section
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- A strengthening of (7.14): the square-root restoration is absorbed into the existing polynomial term.
There is no information-budget premise; the ineffective regime is handled by TV at most one. -/
theorem equation_seven_fourteen_eventually
    (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (betaMin betaMax epsilon eta : ℝ) (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax)
    (hepsilon : 0<epsilon) (heta : 0<eta) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ,
      betaMin*Real.log M≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log M →
      1≤(fullRate M L : ℝ) → ∀ A : Set InfiniteSample,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff M)) inferInstance] A →
      0 < infiniteRademacherMeasure.real A →
      conditionalDistance M L A ≤
        37*Real.exp (eventInformation A)*(fullRate M L : ℝ)*(1+(fullRate M L : ℝ))*
          (Real.exp (-saddleCutoff 1 (Real.log M)+eta*saddleNu 1 (Real.log M))+
            (M : ℝ)^(-(1/(3 : ℝ))+epsilon)) +
          2*Real.exp (-(betaMin*Real.log 2/16)*(Real.log M/Real.log (Real.log M))) := by
  obtain ⟨Nf,hf⟩ := contained_event_hard_bound_eventually hAGG hPNT hLS hShorey hNR
    betaMin betaMax epsilon eta hbetaMin hbeta hepsilon heta
  have hd : 0<betaMin*Real.log 2/8 := by have := Real.log_pos (by norm_num : (1 : ℝ)<2);positivity
  obtain ⟨Nd,hdp⟩ := information_weighted_deep_eventually 1 1 (betaMin*Real.log 2/8) (by norm_num) hd
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Nnu,hnu⟩ := eventually_atTop.mp (((tendsto_saddleNu_atTop (a := 1) (by norm_num)).comp hlog).eventually
    (eventually_ge_atTop (0 : ℝ)))
  refine ⟨max Nf (max Nd Nnu),?_⟩
  intro M hM L hlo hhi hrate A hA hpos
  letI instProbabilityConditional : IsProbabilityMeasure (cond infiniteRademacherMeasure A) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hpos)
  letI instProbabilitySource : IsProbabilityMeasure ((cond infiniteRademacherMeasure A).map (source M L)) :=
    Measure.isProbabilityMeasure_map (measurable_source _ _).aemeasurable
  have hleOne : conditionalDistance M L A≤1 := measureTotalVariation_le_one _ _
  let R := Real.exp (-saddleCutoff 1 (Real.log M)+eta*saddleNu 1 (Real.log M))+
    (M : ℝ)^(-(1/(3 : ℝ))+epsilon)
  let T := Real.exp (eventInformation A)*(fullRate M L : ℝ)*(1+(fullRate M L : ℝ))*R
  change conditionalDistance M L A≤37*Real.exp (eventInformation A)*(fullRate M L : ℝ)*(1+(fullRate M L : ℝ))*R+_
  rw [show 37*Real.exp (eventInformation A)*(fullRate M L : ℝ)*(1+(fullRate M L : ℝ))*R=37*T by dsimp [T];ring]
  by_cases ht : 1≤37*T
  · apply hleOne.trans
    change 1≤37*T+_
    linarith [Real.exp_nonneg (-(betaMin*Real.log 2/16)*(Real.log M/Real.log (Real.log M)))]
  · have hnu0 : 0≤saddleNu 1 (Real.log M) := hnu M (by omega)
    have hR : Real.exp (-saddleCutoff 1 (Real.log M))≤R := by
      have hex : Real.exp (-saddleCutoff 1 (Real.log M))≤
          Real.exp (-saddleCutoff 1 (Real.log M)+eta*saddleNu 1 (Real.log M)) :=
        Real.exp_le_exp.mpr (by nlinarith [mul_nonneg heta.le hnu0])
      exact hex.trans (le_add_of_nonneg_right (by positivity))
    have hl : (1 : ℝ)≤(fullRate M L : ℝ)*(1+(fullRate M L : ℝ)) := by nlinarith
    have hh : Real.exp (eventInformation A-saddleCutoff 1 (Real.log M))≤T := by
      rw [sub_eq_add_neg,Real.exp_add]
      have hmul := mul_le_mul hl hR (Real.exp_nonneg _) (by positivity : (0 : ℝ)≤(fullRate M L : ℝ)*(1+(fullRate M L : ℝ)))
      have hx := mul_le_mul_of_nonneg_left hmul (Real.exp_nonneg (eventInformation A))
      simpa only [T,one_mul,mul_assoc] using hx
    have hT : 0≤T := by dsimp [T,R];positivity
    have hexp : Real.exp (eventInformation A-saddleCutoff 1 (Real.log M))<1 := by
      exact hh.trans_lt (by linarith)
    have hI : eventInformation A≤1*saddleCutoff 1 (Real.log M) := by
      have hh' := Real.exp_lt_one_iff.mp hexp
      linarith
    have hdeep := hdp M (by omega) (eventInformation A) hI
    have he : betaMin*Real.log 2/8/2=betaMin*Real.log 2/16 := by ring
    rw [he] at hdeep
    have hraw := hf M (by omega) L hlo hhi A hA hpos
    rw [div_eq_mul_inv,← exp_eventInformation A hpos] at hraw
    change conditionalDistance M L A≤37*T+_
    dsimp only [T,R]
    nlinarith only [hraw,hdeep]

end
end PaperC.V282.MacroTransportQuantitative
