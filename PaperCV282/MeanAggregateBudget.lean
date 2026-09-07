import PaperCV282.MeanAggregateTruncation
import PaperCV282.AggregateBudgetRates
import PaperCV282.SignedAggregateHardBudget

/-!
# The actual averaged aggregate law under the one-factor intensity budget

This is a mean conditional distance for the entire small-prime field.
It is stronger than substituting the sure event into an event-conditioned
unconditional comparison, and is the input needed for quenched conclusions.
-/
namespace PaperC.V282.MeanAggregateBudget

open MeasureTheory Filter Topology InfiniteRademacher InfiniteCylinderTransfer
open FinitePrimeEnvironment MeanAggregateTruncation CountablePrimeEventTransfer
open SignedAggregateTruncation AggregateBudgetRates AggregateActualTail
open AggregateInformationBudget GrowingMarkedTruncation RareConditioningRates
open SaddleParameters SaddleScales SaddleCutoffAdmissibility AllStartSoftPoisson
open DirectionalSteinInput PrimeEulerPNT HardPoissonRates

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- One threshold precedes every admissible base length. The mean is over the true whole F_Y. -/
theorem mean_aggregate_hard_rate (hStein : DirectionalSteinFactorsStatement)
    (hPNT : PrimeNumberTheoremRemainder) (betaMin betaMax c c' epsilon : ℝ)
    (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax) (hc' : 0<c') (hcc : c'<c)
    (hepsilon : 0<epsilon) :
    ∃ Nzero : ℕ, ∀ N≥Nzero, ∀ L : ℕ,
      betaMin*Real.log N≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log N →
      1≤(fullRate N L : ℝ) → Real.log (fullRate N L)≤
        saddleCutoff 1 (Real.log N)-c*saddleNu 1 (Real.log N) →
      meanAtomDistance (hardCutoff N) (hardCutoff N)
        (signedAggregateSource N L) (signedAggregateTargetLaw N L) ≤
          2*Real.exp (-c'*saddleNu 1 (Real.log N))+(N : ℝ)^(-(1/3 : ℝ)+epsilon) := by
  obtain ⟨Nr,hr⟩ := aggregate_ledger_under_budget hPNT betaMin betaMax c c' epsilon
    hbetaMin hbeta hc' hcc hepsilon
  obtain ⟨Nt,ht⟩ := aggregate_actual_tails_eventually betaMin betaMax c c'
    hbetaMin hbeta (by linarith)
  obtain ⟨Nb,hb⟩ := growing_mark_band_eventually betaMax (by linarith)
  obtain ⟨Na,ha⟩ := saddleCutoff_nat_admissible_eventually 1 (4*betaMax) (by norm_num) (by linarith)
  obtain ⟨Nl,hl⟩ := TouchingPairMass.length_pos_eventually betaMin hbetaMin
  refine ⟨max Nr (max Nt (max Nb (max Na (max Nl 2)))),?_⟩
  intro N hN L hlo hhi hrate hbudget
  have hL : 1≤L := hl N (by omega) L hlo
  have hupper := hb N (by omega) L hhi
  have hupper' : ((L+growingMarkCutoff N+2 : ℕ)+1 : ℝ)≤(4*betaMax)*Real.log N := by
    push_cast
    have hE : (0 : ℝ)≤growingMarkCutoff N := Nat.cast_nonneg _
    have hLL : (1 : ℝ)≤L := by exact_mod_cast hL
    nlinarith
  have hY : 2*(L+growingMarkCutoff N+2)≤hardCutoff N :=
    (ha N (by omega) (L+growingMarkCutoff N+2) hupper').2.2.1
  let C := max (hardCutoff N) (dyadicCutoff N (L+growingMarkCutoff N+1))
  have hmean := mean_signed_aggregate_le_ledger_and_tails hStein
    (C := C) (by omega : 2≤N) hL (le_max_right _ _) hY
  have hp : 0 < infiniteRademacherMeasure.real Set.univ := by simp
  have hbud : aggregateLogCost (eventInformation Set.univ) (fullRate N L)≤
      saddleCutoff 1 (Real.log N)-c*saddleNu 1 (Real.log N) := by
    simpa [aggregateLogCost,eventInformation] using hbudget
  have hledger := hr N (by omega) L hlo hhi Set.univ hp hrate hbud
  have htail := ht N (by omega) L hlo hhi Set.univ hp hrate hbud
  simp only [probReal_univ,div_one] at hledger htail
  rw [meanAtomDistance_eq_canonical (le_max_left _ _)] at hmean
  linarith

/-- The actual random conditional distance has the same bound on its expectation. -/
theorem integral_environment_aggregate_hard_rate (hStein : DirectionalSteinFactorsStatement)
    (hPNT : PrimeNumberTheoremRemainder) (betaMin betaMax c c' epsilon : ℝ)
    (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax) (hc' : 0<c') (hcc : c'<c)
    (hepsilon : 0<epsilon) :
    ∃ Nzero : ℕ, ∀ N≥Nzero, ∀ L : ℕ,
      betaMin*Real.log N≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log N →
      1≤(fullRate N L : ℝ) → Real.log (fullRate N L)≤
        saddleCutoff 1 (Real.log N)-c*saddleNu 1 (Real.log N) →
      (∫ omega, environmentDistance (hardCutoff N) (hardCutoff N)
        (signedAggregateSource N L) (signedAggregateTargetLaw N L) omega ∂infiniteRademacherMeasure) ≤
          2*Real.exp (-c'*saddleNu 1 (Real.log N))+(N : ℝ)^(-(1/3 : ℝ)+epsilon) := by
  simpa only [integral_environmentDistance] using
    mean_aggregate_hard_rate hStein hPNT betaMin betaMax c c' epsilon hbetaMin hbeta hc' hcc hepsilon

end
end PaperC.V282.MeanAggregateBudget
