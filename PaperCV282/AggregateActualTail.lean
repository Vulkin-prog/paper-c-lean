import PaperCV282.SignedAggregateTruncation
import PaperCV282.AggregateCutoffRemainder
import PaperCV282.RareConditioningRates

/-! # Actual conditional aggregate tails under the one-factor information budget -/
namespace PaperC.V282.AggregateActualTail

open MeasureTheory Filter Topology InfiniteRademacher InfiniteCylinderTransfer
open ExactMarkedSourceTail InfiniteExactLengthProbabilityTransfer AllStartSoftPoisson
open SignedAggregateTruncation AggregateInformationBudget AggregateCutoffRemainder
open GrowingMarkedTruncation RareConditioningRates SaddleParameters SaddleScales MarkedDetruncation

noncomputable section

/-- The threshold is chosen before the run length and the actual conditioning event. -/
theorem aggregate_actual_tails_eventually (betaMin betaMax c c' : ℝ)
    (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax) (hc : 0≤c) :
    ∃ Nzero : ℕ, ∀ N≥Nzero, ∀ L : ℕ,
      betaMin*Real.log N≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log N →
      ∀ C : Set InfiniteSample, 0 < infiniteRademacherMeasure.real C →
      1≤(fullRate N L : ℝ) →
      aggregateLogCost (eventInformation C) (fullRate N L)≤
        saddleCutoff 1 (Real.log N)-c*saddleNu 1 (Real.log N) →
      infiniteMarkTailProbability N L (growingMarkCutoff N)/infiniteRademacherMeasure.real C+
        (fullRate N L : ℝ)/(2 : ℝ)^(growingMarkCutoff N+1)≤
          Real.exp (-c'*saddleNu 1 (Real.log N)) := by
  obtain ⟨Nt,ht⟩ := source_mark_tail_le_eventually betaMin (2*betaMax) (1/6)
    hbetaMin (by linarith) (by norm_num)
  obtain ⟨Nb,hb⟩ := growing_mark_band_eventually betaMax (by linarith)
  obtain ⟨Nm,hm⟩ := eventually_atTop.1 (aggregate_tail_le_margin_eventually c')
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Ns,hs⟩ := eventually_atTop.1 (hlog.eventually (eventually_ge_atTop (saddleThreshold 1)))
  refine ⟨max Nt (max Nb (max Nm (max Ns 2))),?_⟩
  intro N hN L hlo hhi C hpos hr hbudget
  have he : 0≤(growingMarkCutoff N : ℝ) := Nat.cast_nonneg _
  have ht' := ht N (by omega) L (growingMarkCutoff N) (by linarith) (hb N (by omega) L hhi)
  have hnp : 1≤(N : ℝ) := by exact_mod_cast (show 1≤N by omega)
  have hpow : (N : ℝ)^(-(1/(2 : ℝ))+1/6)≤1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hnp (by norm_num)
  have htail : infiniteMarkTailProbability N L (growingMarkCutoff N)≤
      2*((fullRate N L : ℝ)/(2 : ℝ)^(growingMarkCutoff N+1)) := by
    apply ht'.trans
    nlinarith [show 0≤(fullRate N L : ℝ)/(2 : ℝ)^(growingMarkCutoff N+1) by positivity]
  have hV := (saddleCutoff_pos (a := 1) (by norm_num) (hs N (by omega))).le
  have hnu : 0≤saddleNu 1 (Real.log N) := div_nonneg (Real.log_nonneg hnp) hV
  have hevent := exp_eventInformation C hpos
  have hnum := aggregate_tail_envelope (eventInformation_nonneg C hpos) hr hc hnu hbudget
  calc
    _ ≤ (2*((fullRate N L : ℝ)/(2 : ℝ)^(growingMarkCutoff N+1)))/infiniteRademacherMeasure.real C+
        (fullRate N L : ℝ)/(2 : ℝ)^(growingMarkCutoff N+1) := by
      gcongr
    _ = (2*Real.exp (eventInformation C)+1)*(fullRate N L : ℝ)/(2 : ℝ)^(growingMarkCutoff N+1) := by
      rw [hevent];ring
    _ ≤ 3*Real.exp (-2*saddleCutoff 1 (Real.log N)) := hnum
    _ ≤ _ := hm N (by omega)

/-- The infinite aggregate comparison retains its genuine finite count distance as the sole middle term. -/
theorem aggregate_detruncation_under_budget (betaMin betaMax c c' : ℝ)
    (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax) (hc : 0≤c) :
    ∃ Nzero : ℕ, ∀ N≥Nzero, ∀ L : ℕ,
      betaMin*Real.log N≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log N →
      ∀ C : Set InfiniteSample, MeasurableSet C → 0 < infiniteRademacherMeasure.real C →
      1≤(fullRate N L : ℝ) →
      aggregateLogCost (eventInformation C) (fullRate N L)≤
        saddleCutoff 1 (Real.log N)-c*saddleNu 1 (Real.log N) →
      conditionalSignedAggregateDistance N L C≤
        conditionalFiniteSignedAggregateDistance N L (growingMarkCutoff N) C+
          Real.exp (-c'*saddleNu 1 (Real.log N)) := by
  obtain ⟨Nzero,hzero⟩ := aggregate_actual_tails_eventually betaMin betaMax c c' hbetaMin hbeta hc
  refine ⟨Nzero,?_⟩
  intro N hN L hlo hhi C hC hpos hr hb
  have ht := hzero N hN L hlo hhi C hpos hr hb
  have hd := conditional_signedAggregate_tv_le_finite_and_tails N L (growingMarkCutoff N) C hC hpos
  linarith

end
end PaperC.V282.AggregateActualTail
