import PaperCV282.MacroAggregateRestoration

/-! # The complete contained aggregate clause of the macroscopic transport theorem -/
namespace PaperC.V282.MacroAggregateTheorem

open MeasureTheory Filter Topology InfiniteRademacher InfiniteCylinderTransfer InfiniteConditionalWords
open MacroAggregateRestoration MacroAggregateHard MacroAggregateTruncation MacroTransportModel
open BulkMarkedGeometry AggregateInformationBudget RareConditioningRates SaddleParameters SaddleScales
open HardPoissonRates AllStartSoftPoisson DirectionalSteinInput PrimeEulerPNT
open LaishramUniformInput PostQuadraticLiterature FiniteFieldTotalVariation

noncomputable section

/-- Every exact excess and both signs are retained on the actual base-contained population. -/
theorem theorem_seven_six_aggregate (hStein : DirectionalSteinFactorsStatement)
    (hPNT : PrimeNumberTheoremRemainder) (hLS : UniformPrimeDivisorStatement)
    (hShorey : ShoreySquareProductStatement) (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (betaMin betaMax c c' epsilon : ℝ) (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax)
    (hc' : 0<c') (hcc : c'<c) (hepsilon : 0<epsilon) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ,
      betaMin*Real.log M≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log M →
      ∀ A : Set InfiniteSample,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff M)) inferInstance] A →
      0 < infiniteRademacherMeasure.real A → 1≤(fullRate M L : ℝ) →
      aggregateLogCost (eventInformation A) (fullRate M L)≤
        saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M) →
      containedAggregateDistance M L A≤
        2*Real.exp (-c'*saddleNu 1 (Real.log M))+2*(M : ℝ)^(-(1/3 : ℝ)+epsilon)+
        2*Real.exp (-(betaMin*Real.log 2/16)*(Real.log M/Real.log (Real.log M))) := by
  obtain ⟨Nr,hr⟩ := hard_aggregate_bulk_event_bound hStein hPNT betaMin betaMax (1/2) c c' epsilon
    hbetaMin hbeta (by norm_num) (by norm_num) hc' hcc hepsilon
  obtain ⟨Np,hp⟩ := restoration_under_budget_eventually hPNT hLS hShorey hNR betaMin betaMax c epsilon
    hbetaMin hbeta (by linarith) hepsilon
  refine ⟨max Nr (max Np 2),?_⟩
  intro M hM L hlo hhi A hA hpos hrate hbudget
  have hAm : MeasurableSet A := by
    have hm := hA
    rw [← smallPrimeSigmaAlgebra_eq_primeCylinder (le_refl (hardCutoff M))] at hm
    exact smallPrimeSigmaAlgebra_le _ _ A hm
  have hret := hr M (by omega) L hlo hhi A hA hpos hrate hbudget
  have hpre := hp M (by omega) L hlo hhi A hpos hrate hbudget
  have hrest := conditional_aggregate_restoration_le (bulkStarts_subset_contained (M := M) (L := L)
    (by omega) (by norm_num : (0 : ℝ)<1/2)) L A hAm hpos
  unfold containedAggregateDistance
  linarith

theorem aggregate_error_tendsto_zero (betaMin c' epsilon : ℝ)
    (hbetaMin : 0<betaMin) (hc' : 0<c') (hepsilon : epsilon<1/3) :
    Tendsto (fun M : ℕ =>
      2*Real.exp (-c'*saddleNu 1 (Real.log M))+2*(M : ℝ)^(-(1/3 : ℝ)+epsilon)+
      2*Real.exp (-(betaMin*Real.log 2/16)*(Real.log M/Real.log (Real.log M)))) atTop (𝓝 0) := by
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hnu := (tendsto_saddleNu_atTop (a := 1) (by norm_num)).comp hlog
  have he := Real.tendsto_exp_atBot.comp (hnu.const_mul_atTop_of_neg (by linarith : -c'<0))
  have hp := (tendsto_rpow_neg_atTop (by linarith : (0 : ℝ)<1/3-epsilon)).comp tendsto_natCast_atTop_atTop
  have hd := PrefixScalarConvergence.deep_remainder_tendsto_zero (betaMin*Real.log 2/16) (by positivity)
  simpa only [mul_zero,add_zero,Function.comp_def,show -(1/3-epsilon)= -(1/3 : ℝ)+epsilon by ring] using
    ((he.const_mul 2).add (hp.const_mul 2)).add (hd.const_mul 2)

/-- The source, conditioning event and length may all vary along an arbitrary unbounded size sequence. -/
theorem aggregate_sequence_tendsto_zero (hStein : DirectionalSteinFactorsStatement)
    (hPNT : PrimeNumberTheoremRemainder) (hLS : UniformPrimeDivisorStatement)
    (hShorey : ShoreySquareProductStatement) (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (betaMin betaMax c : ℝ) (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax) (hc : 0<c)
    (sizes lengths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop) (A : ℕ→Set InfiniteSample)
    (hband : ∀ᶠ n in atTop, betaMin*Real.log (sizes n)≤(lengths n+1 : ℝ) ∧
      (lengths n+1 : ℝ)≤betaMax*Real.log (sizes n))
    (hA : ∀ᶠ n in atTop,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff (sizes n))) inferInstance] (A n))
    (hpos : ∀ᶠ n in atTop, 0 < infiniteRademacherMeasure.real (A n))
    (hrate : ∀ᶠ n in atTop, 1≤(fullRate (sizes n) (lengths n) : ℝ))
    (hbudget : ∀ᶠ n in atTop,
      aggregateLogCost (eventInformation (A n)) (fullRate (sizes n) (lengths n))≤
        saddleCutoff 1 (Real.log (sizes n))-c*saddleNu 1 (Real.log (sizes n))) :
    Tendsto (fun n => containedAggregateDistance (sizes n) (lengths n) (A n)) atTop (𝓝 0) := by
  obtain ⟨Mzero,hzero⟩ := theorem_seven_six_aggregate hStein hPNT hLS hShorey hNR
    betaMin betaMax c (c/2) (1/6) hbetaMin hbeta (by linarith) (by linarith) (by norm_num)
  have herr := (aggregate_error_tendsto_zero betaMin (c/2) (1/6) hbetaMin (by linarith) (by norm_num)).comp hsizes
  have hbound : ∀ᶠ n in atTop, containedAggregateDistance (sizes n) (lengths n) (A n)≤
      2*Real.exp (-(c/2)*saddleNu 1 (Real.log (sizes n)))+2*(sizes n : ℝ)^(-(1/3 : ℝ)+1/6)+
      2*Real.exp (-(betaMin*Real.log 2/16)*(Real.log (sizes n)/Real.log (Real.log (sizes n)))) := by
    filter_upwards [hband,hA,hpos,hrate,hbudget,hsizes.eventually (eventually_ge_atTop Mzero)] with n hb ha hp hr hbu hn
    exact hzero (sizes n) hn (lengths n) hb.1 hb.2 (A n) ha hp hr hbu
  exact squeeze_zero' (Filter.Eventually.of_forall (fun _ => massTotalVariation_nonneg _ _)) hbound herr

/-- The physical centered length and its whole-band domain follow from a=o(log M). -/
theorem moving_aggregate_sequence_tendsto_zero (hStein : DirectionalSteinFactorsStatement)
    (hPNT : PrimeNumberTheoremRemainder) (hLS : UniformPrimeDivisorStatement)
    (hShorey : ShoreySquareProductStatement) (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (c : ℝ) (hc : 0<c) (sizes depths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop)
    (hdepths : Tendsto (fun n => (depths n : ℝ)/Real.log (sizes n)) atTop (𝓝 0))
    (A : ℕ→Set InfiniteSample)
    (hA : ∀ᶠ n in atTop,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff (sizes n))) inferInstance] (A n))
    (hpos : ∀ᶠ n in atTop, 0 < infiniteRademacherMeasure.real (A n))
    (hbudget : ∀ᶠ n in atTop,
      aggregateLogCost (eventInformation (A n)) (fullRate (sizes n) (GrowingLevelParameters.movingLength (sizes n) (depths n)))≤
        saddleCutoff 1 (Real.log (sizes n))-c*saddleNu 1 (Real.log (sizes n))) :
    Tendsto (fun n => containedAggregateDistance (sizes n)
      (GrowingLevelParameters.movingLength (sizes n) (depths n)) (A n)) atTop (𝓝 0) := by
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hdom := SignedAggregateHardBudget.moving_sequence_domain_eventually sizes depths hsizes hdepths
    (1/(2*Real.log 2)) (2/Real.log 2) (by apply (div_lt_div_iff₀ (by positivity) hlog2).mpr;nlinarith)
    (by exact div_lt_div_of_pos_right (by norm_num) hlog2)
  apply aggregate_sequence_tendsto_zero hStein hPNT hLS hShorey hNR
    (1/(2*Real.log 2)) (2/Real.log 2) c (by positivity)
    (by apply (div_lt_div_iff₀ (by positivity) hlog2).mpr;nlinarith) hc sizes _ hsizes A
    (hdom.mono (fun _ h => ⟨h.2.2.1,h.2.2.2.1⟩)) hA hpos
    (hdom.mono (fun _ h => h.2.2.2.2)) hbudget

end
end PaperC.V282.MacroAggregateTheorem
