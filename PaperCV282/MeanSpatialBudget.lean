import PaperCV282.MeanSpatialTruncation
import PaperCV282.QuenchedSaddleBudget

/-! # The true mean full spatial law in its labelled information domain -/
namespace PaperC.V282.MeanSpatialBudget

open MeasureTheory Filter Topology InfiniteRademacher InfiniteCylinderTransfer
open FinitePrimeEnvironment MeanSpatialTruncation QuenchedSaddleBudget
open CountablePrimeEventTransfer SpatialMarkedFieldComparison
open SpatialMarkedSource SpatialMarkedTarget ExactMarkedRates ExactMarkedSourceTail
open LabelledInformationBudget GrowingMarkedTruncation AllStartSoftPoisson
open HardPoissonRates SaddleParameters SaddleScales PrimeEulerPNT ProcessAGGInput

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- Mean of the actual full-field conditional distances, uniformly over the logarithmic band. -/
theorem mean_spatial_hard_rate (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax c c' : ℝ) (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax)
    (hc' : 0<c') (hcc : c'<c) :
    ∃ Nzero : ℕ, ∀ N≥Nzero, ∀ L : ℕ,
      betaMin*Real.log N≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log N →
      1≤(fullRate N L : ℝ) → labelledLogCost 0 (fullRate N L)≤
        saddleCutoff 1 (Real.log N)-c*saddleNu 1 (Real.log N) →
      meanAtomDistance (hardCutoff N) (hardCutoff N)
        (spatialMarkedSource N L) (spatialTargetLaw N L) ≤
          67*Real.exp (-c'*saddleNu 1 (Real.log N)) := by
  obtain ⟨Ne,he⟩ := growing_mark_band_eventually betaMax (hbetaMin.trans hbeta)
  obtain ⟨Nf,hf⟩ := theorem_five_six_signed_full_band hAGG hPNT betaMin (2*betaMax) (1/6) (c-c')
    hbetaMin (by linarith) (by norm_num) (by linarith)
  obtain ⟨Nt,ht⟩ := source_mark_tail_le_eventually betaMin (2*betaMax) (1/6)
    hbetaMin (by linarith) (by norm_num)
  obtain ⟨Nb,hb⟩ := labelled_budget_rate c c' hc' hcc
  refine ⟨max Ne (max Nf (max Nt Nb)),?_⟩
  intro N hN L hlo hhi hr hbu
  have hhi' := he N (by omega) L hhi
  have hlo' : betaMin*Real.log N≤(L+growingMarkCutoff N+2 : ℝ) := by
    have hh : (0 : ℝ)≤growingMarkCutoff N := Nat.cast_nonneg _
    linarith
  have hfin := (hf N (by omega) L (growingMarkCutoff N) hlo hhi').2.1
  have htail := ht N (by omega) L (growingMarkCutoff N) hlo' hhi'
  have hm := mean_spatial_le_finite_and_tails
    (max (hardCutoff N) (dyadicCutoff N (L+growingMarkCutoff N+1))) N L (growingMarkCutoff N)
    (hardCutoff N)
  rw [meanAtomDistance_eq_canonical (le_max_left _ _)] at hm
  have hbound := hb N (by omega) (fullRate N L) hr hbu
  unfold exactMarkedRate at hfin
  norm_num only [show -(1/(3 : ℝ))+1/6= -(1/(6 : ℝ)) by norm_num] at hfin
  norm_num only [show -(1/(2 : ℝ))+1/6= -(1/(3 : ℝ)) by norm_num] at htail
  nlinarith

/-- The same estimate is the expectation of the actual random environment distance. -/
theorem integral_spatial_hard_rate (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax c c' : ℝ) (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax)
    (hc' : 0<c') (hcc : c'<c) :
    ∃ Nzero : ℕ, ∀ N≥Nzero, ∀ L : ℕ,
      betaMin*Real.log N≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log N →
      1≤(fullRate N L : ℝ) → labelledLogCost 0 (fullRate N L)≤
        saddleCutoff 1 (Real.log N)-c*saddleNu 1 (Real.log N) →
      (∫ omega, environmentDistance (hardCutoff N) (hardCutoff N)
        (spatialMarkedSource N L) (spatialTargetLaw N L) omega ∂infiniteRademacherMeasure) ≤
          67*Real.exp (-c'*saddleNu 1 (Real.log N)) := by
  simpa only [integral_environmentDistance] using
    mean_spatial_hard_rate hAGG hPNT betaMin betaMax c c' hbetaMin hbeta hc' hcc

end
end PaperC.V282.MeanSpatialBudget
