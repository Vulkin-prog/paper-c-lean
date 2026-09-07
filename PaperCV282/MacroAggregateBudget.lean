import PaperCV282.MacroAggregateRates
import PaperCV282.MacroAggregateTruncation
import PaperCV282.AggregateBudgetRates

/-! # Actual aggregate arithmetic and tails under the single-intensity information budget -/
namespace PaperC.V282.MacroAggregateBudget

open MeasureTheory Filter Topology InfiniteRademacher InfiniteCylinderTransfer
open AggregateInformationBudget AggregateCutoffRemainder MacroAggregateRates MacroAggregateArithmetic
open MacroAggregateTruncation BulkMarkedSource FiniteStartMaskAverages MaskedArithmeticGeometry
open GrowingMarkedTruncation RareConditioningRates SaddleParameters AllStartSoftPoisson
open PrimeEulerPNT HardPoissonRates SaddleScales

noncomputable section

/-- The enlarged full-value profile and the directional Stein logarithm are both
absorbed, uniformly before choosing the length or the conditioning event. -/
theorem aggregate_ledger_under_budget (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax delta c c' epsilon : ℝ) (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax)
    (hdelta : 0<delta) (hc' : 0<c') (hcc : c'<c) (hepsilon : 0<epsilon) :
    ∃ Nzero : ℕ, ∀ N≥Nzero, ∀ L : ℕ,
      betaMin*Real.log N≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log N →
      ∀ C : Set InfiniteSample, 0 < infiniteRademacherMeasure.real C →
      1≤(fullRate N L : ℝ) →
      aggregateLogCost (eventInformation C) (fullRate N L)≤
        saddleCutoff 1 (Real.log N)-c*saddleNu 1 (Real.log N) →
      ∀ K : ℕ, N+(L+growingMarkCutoff N+1)≤K →
      ∀ mask : Finset ℕ, mask ⊆ Finset.Icc ⌈(N : ℝ)^delta⌉₊ N → (N : ℝ)/2≤mask.card →
      aggregateLedger K L (growingMarkCutoff N) (hardCutoff N) mask/
        infiniteRademacherMeasure.real C≤
          Real.exp (-c'*saddleNu 1 (Real.log N))+(N : ℝ)^(-(1/3 : ℝ)+epsilon) := by
  have hc : 0≤c := by linarith
  obtain ⟨Na,ha⟩ := signed_aggregate_ledger_rate_eventually hPNT betaMin (2*betaMax) delta
    (epsilon/2) ((c-c')/2) hbetaMin (by linarith) hdelta (by linarith) (by linarith)
  obtain ⟨Nb,hb⟩ := growing_mark_band_eventually betaMax (by linarith)
  obtain ⟨Nl,hl⟩ := eventually_atTop.1
    (aggregate_leading_bound_eventually 64 c c' (by norm_num) hc hcc)
  obtain ⟨Np,hp⟩ := eventually_atTop.1
    (aggregate_profile_bound_eventually 64 c epsilon (by norm_num) hc hepsilon)
  refine ⟨max Na (max Nb (max Nl Np)),?_⟩
  intro N hN L hlo hhi C hpos hr hbudget K hK mask hmask hcard
  have hI := eventInformation_nonneg C hpos
  have hlead := hl N (by omega) (eventInformation C) (fullRate N L) hI hr hbudget
  have hpoly := hp N (by omega) (eventInformation C) (fullRate N L) hI hr hbudget
  have hlog : 0≤Real.log (2*(fullRate N L : ℝ)) := Real.log_nonneg (by linarith)
  have hledger := ha N (by omega) L (growingMarkCutoff N) hlo (hb N (by omega) L hhi) hr K hK mask hmask hcard
  rw [max_eq_right hlog] at hledger
  have hpoly' : 64*Real.exp (eventInformation C)*(2 : ℝ)^(2*growingMarkCutoff N+2)*
      (fullRate N L : ℝ)^2*(N : ℝ)^(-(1/3 : ℝ)+epsilon/2)≤
        (N : ℝ)^(-(1/3 : ℝ)+epsilon) := by
    have hnonneg : 0≤64*Real.exp (eventInformation C)*(2 : ℝ)^(2*growingMarkCutoff N+2)*
        (fullRate N L : ℝ)^2*(N : ℝ)^(-(1/3 : ℝ)+epsilon/2) := by positivity
    nlinarith [mul_nonneg hnonneg hlog]
  have hweighted := mul_le_mul_of_nonneg_left hledger (Real.exp_nonneg (eventInformation C))
  rw [div_eq_mul_inv,← exp_eventInformation C hpos]
  nlinarith only [hweighted,hlead,hpoly']

/-- The actual macroscopic source tail is bounded before all lengths and masks. -/
theorem source_tail_le_two_eventually (betaMin betaMax delta : ℝ)
    (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax) (hdelta : 0<delta) :
    ∃ Nzero : ℕ, ∀ N≥Nzero, ∀ L E : ℕ,
      betaMin*Real.log N≤(L+1 : ℝ) → (L+E+2 : ℝ)≤betaMax*Real.log N →
      ∀ mask : Finset ℕ, mask⊆Finset.Icc ⌈(N : ℝ)^delta⌉₊ N →
      infiniteRademacherMeasure.real (spatialSourceTail mask L E)≤
        2*((fullRate N L : ℝ)/(2 : ℝ)^(E+1)) := by
  obtain ⟨Nm,hm⟩ := MacroscopicArithmeticBounds.fullDefectMass_le_half_power_eventually
    betaMin betaMax delta (1/4) hbetaMin hbeta hdelta (by norm_num)
  refine ⟨max Nm 2,?_⟩
  intro N hN L E hlo hhi mask hmask
  have hbounded : mask⊆Finset.Icc 2 N := fun x hx =>
    MacroscopicArithmeticBounds.closed_macroscopic_subset_Icc (by omega) hdelta (hmask hx)
  have hsite : ∀x∈mask,2≤x := fun x hx => (Finset.mem_Icc.mp (hbounded hx)).1
  have hqlo : betaMin*Real.log N≤((L+E+1 : ℕ)+1 : ℝ) := by
    push_cast
    have hE : (0 : ℝ)≤E := by positivity
    linarith
  have hqhi : ((L+E+1 : ℕ)+1 : ℝ)≤betaMax*Real.log N := by push_cast;linarith
  have hmass := hm N (by omega) (L+E+1) hqlo hqhi mask hmask
  have hmN : (fullDefectMass (L+E+1) mask : ℝ)≤N := by
    apply hmass.trans
    calc
      _ ≤ (N : ℝ)^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1≤N by omega)) (by norm_num)
      _ = _ := Real.rpow_one _
  have hcard : (mask.card : ℝ)≤N := by exact_mod_cast MacroscopicMaskGeometry.card_mask_le hbounded
  apply (spatial_source_tail_le_full_defects L E hsite).trans
  calc
    _ ≤ (2*N : ℝ)/(2 : ℝ)^(L+E+1) := div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by rw [fullRate_coe,show L+E+1=L+(E+1) by omega,pow_add];ring

/-- The threshold is chosen before the run length and the actual conditioning event. -/
theorem aggregate_actual_tails_eventually (betaMin betaMax delta c c' : ℝ)
    (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax) (hdelta : 0<delta) (hc : 0≤c) :
    ∃ Nzero : ℕ, ∀ N≥Nzero, ∀ L : ℕ,
      betaMin*Real.log N≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log N →
      ∀ C : Set InfiniteSample, 0 < infiniteRademacherMeasure.real C →
      1≤(fullRate N L : ℝ) →
      aggregateLogCost (eventInformation C) (fullRate N L)≤
        saddleCutoff 1 (Real.log N)-c*saddleNu 1 (Real.log N) →
      ∀ mask : Finset ℕ, mask⊆Finset.Icc ⌈(N : ℝ)^delta⌉₊ N →
      infiniteRademacherMeasure.real (spatialSourceTail mask L (growingMarkCutoff N))/infiniteRademacherMeasure.real C+
        (maskRate L mask : ℝ)/(2 : ℝ)^(growingMarkCutoff N+1)≤
          Real.exp (-c'*saddleNu 1 (Real.log N)) := by
  obtain ⟨Nt,ht⟩ := source_tail_le_two_eventually betaMin (2*betaMax) delta
    hbetaMin (by linarith) hdelta
  obtain ⟨Nb,hb⟩ := growing_mark_band_eventually betaMax (by linarith)
  obtain ⟨Nm,hm⟩ := eventually_atTop.1 (aggregate_tail_le_margin_eventually c')
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Ns,hs⟩ := eventually_atTop.1 (hlog.eventually (eventually_ge_atTop (saddleThreshold 1)))
  refine ⟨max Nt (max Nb (max Nm (max Ns 2))),?_⟩
  intro N hN L hlo hhi C hpos hr hbudget mask hmask
  have he : 0≤(growingMarkCutoff N : ℝ) := Nat.cast_nonneg _
  have htail := ht N (by omega) L (growingMarkCutoff N) hlo (hb N (by omega) L hhi) mask hmask
  have hnp : 1≤(N : ℝ) := by exact_mod_cast (show 1≤N by omega)
  have hbounded : mask⊆Finset.Icc 2 N := fun x hx =>
    MacroscopicArithmeticBounds.closed_macroscopic_subset_Icc (by omega) hdelta (hmask hx)
  have hcard : (mask.card : ℝ)≤N := by exact_mod_cast MacroscopicMaskGeometry.card_mask_le hbounded
  have hrate : (maskRate L mask : ℝ)≤(fullRate N L : ℝ) :=
    div_le_div_of_nonneg_right hcard (by positivity)
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


end
end PaperC.V282.MacroAggregateBudget
