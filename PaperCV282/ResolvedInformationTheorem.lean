import PaperCV282.PoissonResolutionBudget
import PaperCV282.UnsignedResolvedPathRates
import PaperCV282.PoissonResolvedComparison

/-! # The local information budget controls the true resolved future law

This is the budget (6.7), with an explicit remaining margin and one threshold
before the length, arithmetic event and resolved count. No Gaussian or local
limit statement is assumed. The fixed logarithmic band is explicit.
-/
namespace PaperC.V282.ResolvedInformationTheorem

open MeasureTheory ProbabilityTheory Filter Topology InfiniteRademacher InfiniteCylinderTransfer
open InfiniteConditionalWords PoissonResolutionBudget PoissonResolvedComparison PoissonResolvedTarget
open UnsignedResolvedPathRates UnsignedAggregateComparison RareConditioningRates
open HardPoissonRates AllStartSoftPoisson SaddleParameters SaddleScales SaddleRateConvergence
open DirectionalSteinInput PrimeEulerPNT SharpConditioning FiniteFieldTotalVariation

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

def resolvedBudgetRemainder (N : ℕ) (c : ℝ) : ℝ :=
  40 * poissonStirlingConstant * Real.exp (-(c/2)*saddleNu 1 (Real.log N)) +
    (N : ℝ)^(-(1/6 : ℝ))

theorem resolvedBudgetRemainder_tendsto_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N => resolvedBudgetRemainder N c) atTop (𝓝 0) := by
  have h := (margin_exponential_nat_tendsto_zero 1 (2*c) (c/2) (by norm_num) (by linarith)).const_mul
    (40 * poissonStirlingConstant)
  have hp := polynomial_error_nat_tendsto_zero (1/6) (by norm_num)
  simpa only [resolvedBudgetRemainder, show 2*c/2-c/2 = c/2 by ring,
    show -(1/3 : ℝ)+1/6 = -(1/6 : ℝ) by norm_num, mul_zero, add_zero] using h.add hp

/-- The full true comparison error divided by the actual Poisson atom tends to zero under (6.7). -/
theorem resolved_ratio_bound_eventually (hStein : DirectionalSteinFactorsStatement)
    (hPNT : PrimeNumberTheoremRemainder) (betaMin betaMax c : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax) (hc : 0 < c) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L+1 : ℝ) → (L+1 : ℝ) ≤ betaMax * Real.log N →
      ∀ C : Set InfiniteSample,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff N)) inferInstance] C →
      0 < infiniteRademacherMeasure.real C → ∀ n : ℕ, 0 < n →
      resolvedInformationCost (eventInformation C) (fullRate N L) n ≤
        saddleCutoff 1 (Real.log N) - c * saddleNu 1 (Real.log N) →
      conditionalUnsignedAggregateDistance N L C / resolutionProbability N L n ≤
        resolvedBudgetRemainder N c := by
  obtain ⟨Nr,hr⟩ := resolved_aggregate_event_bound hStein hPNT betaMin betaMax 1 (1/12) (c/2)
    hbetaMin hbeta (by norm_num) (by norm_num) (by linarith)
  obtain ⟨Np,hp⟩ := eventually_atTop.1 (poisson_resolved_polynomial_bound_eventually c (1/6)
    hc.le (by norm_num))
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Ns,hs⟩ := eventually_atTop.1 (hlog.eventually (eventually_ge_atTop (saddleThreshold 1)))
  refine ⟨max Nr (max Np (max Ns 2)), ?_⟩
  intro N hN L hlo hhi C hC hpos n hn hb
  have hI := eventInformation_nonneg C hpos
  have hrpos : 0 < (fullRate N L : ℝ) := by
    rw [fullRate_coe]
    have hnp : 0 < N := by omega
    positivity
  have hV := saddleCutoff_pos (a := 1) (by norm_num) (hs N (by omega))
  have hnu : 0 ≤ saddleNu 1 (Real.log N) := div_nonneg
    (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) hV.le
  have henv : eventInformation C + max 0 (Real.log (fullRate N L : ℝ)) ≤
      1 * saddleCutoff 1 (Real.log N) := by
    have hj := poissonLocalCost_nonneg hrpos hn
    have hf : 0 ≤ Real.log (1 + max 0 (Real.log (2*(fullRate N L : ℝ)))) :=
      Real.log_nonneg (by linarith [le_max_left 0 (Real.log (2*(fullRate N L : ℝ)))])
    unfold resolvedInformationCost at hb
    nlinarith [mul_nonneg hc.le hnu]
  have hdist := (hr N (by omega) L hlo hhi C hC hpos henv).2
  have hlead := poisson_resolved_leading_bound (K := 40) hrpos hn (by norm_num) hb
    (eta := c/2)
  have hpoly := hp N (by omega) (eventInformation C) (fullRate N L) n hI hrpos hn hb
  have hratio := div_le_div_of_nonneg_right hdist (resolutionProbability_pos (N := N) (by omega) L n).le
  rw [add_div] at hratio
  apply hratio.trans
  simpa only [resolvedBudgetRemainder, resolutionProbability,
    show c-c/2 = c/2 by ring, show (1/6 : ℝ)/2 = 1/12 by norm_num,
    show -(1/3 : ℝ)+1/6 = -(1/6 : ℝ) by norm_num] using add_le_add hlead hpoly

/-- Under the printed cost, the resolved source event is positive and its entire future is controlled. -/
theorem resolved_future_under_information_budget (hStein : DirectionalSteinFactorsStatement)
    (hPNT : PrimeNumberTheoremRemainder) (betaMin betaMax c : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax) (hc : 0 < c) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L+1 : ℝ) → (L+1 : ℝ) ≤ betaMax * Real.log N →
      ∀ C : Set InfiniteSample,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff N)) inferInstance] C →
      0 < infiniteRademacherMeasure.real C → ∀ n : ℕ, 0 < n →
      resolvedInformationCost (eventInformation C) (fullRate N L) n ≤
        saddleCutoff 1 (Real.log N) - c * saddleNu 1 (Real.log N) →
      0 < infiniteRademacherMeasure.real
        (C ∩ {omega | InfiniteStartProbabilityTransfer.infiniteDyadicStartCount N L omega=n}) ∧
      measureTotalVariation (resolvedFutureLaw N L n C) (thinningPathMeasure n) ≤
        resolvedBudgetRemainder N c := by
  obtain ⟨Nr,hr⟩ := resolved_ratio_bound_eventually hStein hPNT betaMin betaMax c hbetaMin hbeta hc
  obtain ⟨Ns,hs⟩ := eventually_atTop.1
    ((resolvedBudgetRemainder_tendsto_zero hc).eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1)))
  refine ⟨max Nr (max Ns 2), ?_⟩
  intro N hN L hlo hhi C hC hpos n hn hb
  have hratio := hr N (by omega) L hlo hhi C hC hpos n hn hb
  have hlt : conditionalUnsignedAggregateDistance N L C < resolutionProbability N L n := by
    have hh := hratio.trans_lt (hs N (by omega))
    exact (div_lt_one (resolutionProbability_pos (N := N) (by omega) L n)).mp hh
  have hCm : MeasurableSet C := by
    have hm := hC
    rw [← smallPrimeSigmaAlgebra_eq_primeCylinder (M := hardCutoff N) le_rfl] at hm
    exact smallPrimeSigmaAlgebra_le (hardCutoff N) (hardCutoff N) C hm
  obtain ⟨hpositive,hdist⟩ := theorem_six_three_future (by omega : 2 ≤ N) n C hCm hpos le_rfl hlt
  exact ⟨hpositive,hdist.trans hratio⟩

end
end PaperC.V282.ResolvedInformationTheorem
