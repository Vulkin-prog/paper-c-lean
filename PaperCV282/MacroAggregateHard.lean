import PaperCV282.MacroAggregateBudget
import PaperCV282.MacroAggregateGeometry
import PaperCV282.SignedAggregateHardBudget

/-! # Complete conditional aggregate budgets on genuine retained macroscopic masks -/
namespace PaperC.V282.MacroAggregateHard

open MeasureTheory Filter Topology InfiniteRademacher InfiniteCylinderTransfer InfiniteConditionalWords
open MacroAggregateComparison MacroAggregateTruncation MacroAggregateBudget MacroAggregateGeometry
open AggregateInformationBudget GrowingMarkedTruncation GrowingLevelParameters RareConditioningRates
open HardPoissonRates SaddleParameters SaddleScales SaddleCutoffAdmissibility DirectionalSteinInput
open PrimeEulerPNT AllStartSoftPoisson FiniteFieldTotalVariation BulkMarkedGeometry

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

/-- The genuine complete aggregate on a dense macroscopic mask obeys the one-factor budget. -/
theorem hard_aggregate_mask_event_bound (hStein : DirectionalSteinFactorsStatement)
    (hPNT : PrimeNumberTheoremRemainder) (betaMin betaMax delta c c' epsilon : ℝ)
    (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax) (hdelta : 0<delta) (hc' : 0<c') (hcc : c'<c)
    (hepsilon : 0<epsilon) :
    ∃ Nzero : ℕ, ∀ N≥Nzero, ∀ L : ℕ,
      betaMin*Real.log N≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log N →
      ∀ A : Set InfiniteSample,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff N)) inferInstance] A →
      0 < infiniteRademacherMeasure.real A → 1≤(fullRate N L : ℝ) →
      aggregateLogCost (eventInformation A) (fullRate N L)≤
        saddleCutoff 1 (Real.log N)-c*saddleNu 1 (Real.log N) →
      ∀ mask : Finset ℕ, mask⊆Finset.Icc ⌈(N : ℝ)^delta⌉₊ N → (N : ℝ)/2≤mask.card →
      conditionalSignedAggregateDistance mask L A≤
        2*Real.exp (-c'*saddleNu 1 (Real.log N))+(N : ℝ)^(-(1/3 : ℝ)+epsilon) := by
  have hbmax : 0<betaMax := hbetaMin.trans hbeta
  obtain ⟨Nr,hr⟩ := aggregate_ledger_under_budget hPNT betaMin betaMax delta c c' epsilon
    hbetaMin hbeta hdelta hc' hcc hepsilon
  obtain ⟨Nt,ht⟩ := aggregate_actual_tails_eventually betaMin betaMax delta c c'
    hbetaMin hbeta hdelta (by linarith)
  obtain ⟨Nb,hb⟩ := growing_mark_band_eventually betaMax hbmax
  obtain ⟨Na,ha⟩ := saddleCutoff_nat_admissible_eventually 1 (4*betaMax) (by norm_num) (by positivity)
  obtain ⟨Nl,hl⟩ := TouchingPairMass.length_pos_eventually betaMin hbetaMin
  refine ⟨max Nr (max Nt (max Nb (max Na (max Nl 2)))),?_⟩
  intro N hN L hlo hhi A hA hpos hrate hbudget mask hmask hcard
  have hbounded : mask⊆Finset.Icc 2 N := fun x hx =>
    MacroscopicArithmeticBounds.closed_macroscopic_subset_Icc (by omega) hdelta (hmask hx)
  have hsite : ∀x∈mask,2≤x := fun x hx => (Finset.mem_Icc.mp (hbounded hx)).1
  have hne : mask.Nonempty := Finset.card_pos.mp (by
    have hn : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
    exact_mod_cast (show (0 : ℝ)<mask.card by linarith))
  have hL : 1≤L := hl N (by omega) L hlo
  have hupper := hb N (by omega) L hhi
  have hupper' : ((L+growingMarkCutoff N+2 : ℕ)+1 : ℝ)≤(4*betaMax)*Real.log N := by
    push_cast
    have hE : (0 : ℝ)≤growingMarkCutoff N := Nat.cast_nonneg _
    have hLL : (1 : ℝ)≤L := by exact_mod_cast hL
    nlinarith
  have hY : 2*(L+growingMarkCutoff N+2)≤hardCutoff N :=
    (ha N (by omega) (L+growingMarkCutoff N+2) hupper').2.2.1
  let C : ℕ := max (hardCutoff N) (N+(L+growingMarkCutoff N+1))
  have hAm : MeasurableSet A := by
    have hm := hA
    rw [← smallPrimeSigmaAlgebra_eq_primeCylinder (M := C) (le_max_left _ _)] at hm
    exact smallPrimeSigmaAlgebra_le C (hardCutoff N) A hm
  have hcut : ∀x∈mask,x+L+growingMarkCutoff N+1≤C := by
    intro x hx
    have hh := (Finset.mem_Icc.mp (hbounded hx)).2
    exact (by omega : x+L+growingMarkCutoff N+1≤N+(L+growingMarkCutoff N+1)).trans (le_max_right _ _)
  have hfinite := conditional_finite_signed_aggregate_le_ledger hStein
    (C := C) hne hsite hL hcut hY (le_max_left _ _) A hA hpos
  have hledger := hr N (by omega) L hlo hhi A hpos hrate hbudget C (le_max_right _ _) mask hmask hcard
  have htail := ht N (by omega) L hlo hhi A hpos hrate hbudget mask hmask
  have htotal := conditional_signedAggregate_tv_le_finite_and_tails mask L (growingMarkCutoff N) A hAm hpos
  linarith

/-- The density condition is proved for the literal base-contained bulk, before L and A. -/
theorem hard_aggregate_bulk_event_bound (hStein : DirectionalSteinFactorsStatement)
    (hPNT : PrimeNumberTheoremRemainder) (betaMin betaMax delta c c' epsilon : ℝ)
    (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hc' : 0<c') (hcc : c'<c) (hepsilon : 0<epsilon) :
    ∃ Nzero : ℕ, ∀ N≥Nzero, ∀ L : ℕ,
      betaMin*Real.log N≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log N →
      ∀ A : Set InfiniteSample,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff N)) inferInstance] A →
      0 < infiniteRademacherMeasure.real A → 1≤(fullRate N L : ℝ) →
      aggregateLogCost (eventInformation A) (fullRate N L)≤
        saddleCutoff 1 (Real.log N)-c*saddleNu 1 (Real.log N) →
      conditionalSignedAggregateDistance (bulkStarts N L delta) L A≤
        2*Real.exp (-c'*saddleNu 1 (Real.log N))+(N : ℝ)^(-(1/3 : ℝ)+epsilon) := by
  obtain ⟨Nr,hr⟩ := hard_aggregate_mask_event_bound hStein hPNT betaMin betaMax delta c c' epsilon
    hbetaMin hbeta hdelta hc' hcc hepsilon
  obtain ⟨Nd,hd⟩ := card_bulkStarts_ge_half_eventually betaMax delta (hbetaMin.trans hbeta).le hdeltaOne
  obtain ⟨Nl,hl⟩ := TouchingPairMass.length_pos_eventually betaMin hbetaMin
  refine ⟨max Nr (max Nd (max Nl 2)),?_⟩
  intro N hN L hlo hhi A hA hpos hrate hbudget
  exact hr N (by omega) L hlo hhi A hA hpos hrate hbudget _
    (bulkStarts_subset_closed (by omega) (hl N (by omega) L hlo)) (hd N (by omega) L hhi)

end
end PaperC.V282.MacroAggregateHard
