import PaperCV282.SignedAggregateRates
import PaperCV282.AggregateActualTail

/-! # The full aggregate arithmetic ledger under the paper's one-factor information budget -/
namespace PaperC.V282.AggregateBudgetRates

open MeasureTheory Filter Topology InfiniteRademacher InfiniteCylinderTransfer
open AggregateInformationBudget AggregateCutoffRemainder AggregateActualTail SignedAggregateRates
open GrowingMarkedTruncation RareConditioningRates SaddleParameters AllStartSoftPoisson
open PrimeEulerPNT HardPoissonRates SaddleScales

noncomputable section

/-- The enlarged full-value profile and the directional Stein logarithm are both
absorbed, uniformly before choosing the length or the conditioning event. -/
theorem aggregate_ledger_under_budget (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax c c' epsilon : ℝ) (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax)
    (hc' : 0<c') (hcc : c'<c) (hepsilon : 0<epsilon) :
    ∃ Nzero : ℕ, ∀ N≥Nzero, ∀ L : ℕ,
      betaMin*Real.log N≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log N →
      ∀ C : Set InfiniteSample, 0 < infiniteRademacherMeasure.real C →
      1≤(fullRate N L : ℝ) →
      aggregateLogCost (eventInformation C) (fullRate N L)≤
        saddleCutoff 1 (Real.log N)-c*saddleNu 1 (Real.log N) →
      signedAggregateLedger N L (growingMarkCutoff N) (hardCutoff N) (dyadicBlock N)/
        infiniteRademacherMeasure.real C≤
          Real.exp (-c'*saddleNu 1 (Real.log N))+(N : ℝ)^(-(1/3 : ℝ)+epsilon) := by
  have hc : 0≤c := by linarith
  obtain ⟨Na,ha⟩ := signed_aggregate_ledger_rate_eventually hPNT betaMin (2*betaMax)
    (epsilon/2) ((c-c')/2) hbetaMin (by linarith) (by linarith) (by linarith)
  obtain ⟨Nb,hb⟩ := growing_mark_band_eventually betaMax (by linarith)
  obtain ⟨Nl,hl⟩ := eventually_atTop.1
    (aggregate_leading_bound_eventually 32 c c' (by norm_num) hc hcc)
  obtain ⟨Np,hp⟩ := eventually_atTop.1
    (aggregate_profile_bound_eventually 32 c epsilon (by norm_num) hc hepsilon)
  refine ⟨max Na (max Nb (max Nl Np)),?_⟩
  intro N hN L hlo hhi C hpos hr hbudget
  have hI := eventInformation_nonneg C hpos
  have hlead := hl N (by omega) (eventInformation C) (fullRate N L) hI hr hbudget
  have hpoly := hp N (by omega) (eventInformation C) (fullRate N L) hI hr hbudget
  have hlog : 0≤Real.log (2*(fullRate N L : ℝ)) := Real.log_nonneg (by linarith)
  have hledger := ha N (by omega) L (growingMarkCutoff N) hlo (hb N (by omega) L hhi) hr
  rw [max_eq_right hlog] at hledger
  have hpoly' : 32*Real.exp (eventInformation C)*(2 : ℝ)^(2*growingMarkCutoff N+2)*
      (fullRate N L : ℝ)^2*(N : ℝ)^(-(1/3 : ℝ)+epsilon/2)≤
        (N : ℝ)^(-(1/3 : ℝ)+epsilon) := by
    have hnonneg : 0≤32*Real.exp (eventInformation C)*(2 : ℝ)^(2*growingMarkCutoff N+2)*
        (fullRate N L : ℝ)^2*(N : ℝ)^(-(1/3 : ℝ)+epsilon/2) := by positivity
    nlinarith [mul_nonneg hnonneg hlog]
  have hweighted := mul_le_mul_of_nonneg_left hledger (Real.exp_nonneg (eventInformation C))
  rw [div_eq_mul_inv,← exp_eventInformation C hpos]
  nlinarith only [hweighted,hlead,hpoly']

/-- The precise aggregate error tends to zero whenever the polynomial exponent is negative. -/
theorem aggregate_error_tendsto_zero (c' epsilon : ℝ) (hc' : 0<c') (hepsilon : epsilon<1/3) :
    Tendsto (fun N : ℕ => 2*Real.exp (-c'*saddleNu 1 (Real.log N))+
      (N : ℝ)^(-(1/3 : ℝ)+epsilon)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hnu := (SaddleScales.tendsto_saddleNu_atTop (a := 1) (by norm_num)).comp hlog
  have he := Real.tendsto_exp_atBot.comp (hnu.const_mul_atTop_of_neg (neg_neg_iff_pos.mpr hc'))
  have hp := (tendsto_rpow_neg_atTop (by linarith : (0 : ℝ)<1/3-epsilon)).comp tendsto_natCast_atTop_atTop
  have hh := (he.const_mul 2).add hp
  simpa only [Function.comp_def,mul_zero,add_zero,
    show -(1/3-epsilon)= -(1/3 : ℝ)+epsilon by ring] using hh

end
end PaperC.V282.AggregateBudgetRates
