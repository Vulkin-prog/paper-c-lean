import PaperCV282.SignedAggregateComparison
import PaperCV282.AggregateBudgetRates
import PaperCV282.UnsignedAggregateComparison
import PaperCV282.GrowingLevelParameters

/-! # The genuine aggregate hard information budget

The threshold precedes the length and actual arithmetic conditioning event.
Both signs and every excess are retained in the stronger comparison; forgetting
signs and replacing exact counts by the whole threshold path are exact statistics.
-/
namespace PaperC.V282.SignedAggregateHardBudget

open MeasureTheory Filter Topology InfiniteRademacher InfiniteCylinderTransfer InfiniteConditionalWords
open SignedAggregateComparison SignedAggregateTruncation UnsignedAggregateComparison
open AggregateBudgetRates AggregateActualTail AggregateInformationBudget GrowingMarkedTruncation
open GrowingLevelParameters RareConditioningRates HardPoissonRates SaddleParameters SaddleScales
open SaddleCutoffAdmissibility DirectionalSteinInput PrimeEulerPNT AllStartSoftPoisson
open FiniteFieldTotalVariation

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

/-- The full signed and unsigned laws satisfy the same sharp one-factor budget. -/
theorem hard_aggregate_event_bound (hStein : DirectionalSteinFactorsStatement)
    (hPNT : PrimeNumberTheoremRemainder) (betaMin betaMax c c' epsilon : ℝ)
    (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax) (hc' : 0<c') (hcc : c'<c)
    (hepsilon : 0<epsilon) :
    ∃ Nzero : ℕ, ∀ N≥Nzero, ∀ L : ℕ,
      betaMin*Real.log N≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log N →
      ∀ A : Set InfiniteSample,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff N)) inferInstance] A →
      0 < infiniteRademacherMeasure.real A → 1≤(fullRate N L : ℝ) →
      aggregateLogCost (eventInformation A) (fullRate N L)≤
        saddleCutoff 1 (Real.log N)-c*saddleNu 1 (Real.log N) →
      conditionalSignedAggregateDistance N L A≤
        2*Real.exp (-c'*saddleNu 1 (Real.log N))+(N : ℝ)^(-(1/3 : ℝ)+epsilon) ∧
      conditionalUnsignedAggregateDistance N L A≤
        2*Real.exp (-c'*saddleNu 1 (Real.log N))+(N : ℝ)^(-(1/3 : ℝ)+epsilon) := by
  have hbmax : 0<betaMax := hbetaMin.trans hbeta
  obtain ⟨Nr,hr⟩ := aggregate_ledger_under_budget hPNT betaMin betaMax c c' epsilon
    hbetaMin hbeta hc' hcc hepsilon
  obtain ⟨Nt,ht⟩ := aggregate_detruncation_under_budget betaMin betaMax c c'
    hbetaMin hbeta (by linarith)
  obtain ⟨Nb,hb⟩ := growing_mark_band_eventually betaMax hbmax
  obtain ⟨Na,ha⟩ := saddleCutoff_nat_admissible_eventually 1 (4*betaMax) (by norm_num) (by positivity)
  obtain ⟨Nl,hl⟩ := TouchingPairMass.length_pos_eventually betaMin hbetaMin
  refine ⟨max Nr (max Nt (max Nb (max Na (max Nl 2)))),?_⟩
  intro N hN L hlo hhi A hA hpos hrate hbudget
  have hL : 1≤L := hl N (by omega) L hlo
  have hupper := hb N (by omega) L hhi
  have hupper' : ((L+growingMarkCutoff N+2 : ℕ)+1 : ℝ)≤(4*betaMax)*Real.log N := by
    push_cast
    have hE : (0 : ℝ)≤growingMarkCutoff N := Nat.cast_nonneg _
    have hLL : (1 : ℝ)≤L := by exact_mod_cast hL
    nlinarith
  have hY : 2*(L+growingMarkCutoff N+2)≤hardCutoff N :=
    (ha N (by omega) (L+growingMarkCutoff N+2) hupper').2.2.1
  let C : ℕ := max (hardCutoff N) (dyadicCutoff N (L+growingMarkCutoff N+1))
  have hAm : MeasurableSet A := by
    have hm := hA
    rw [← smallPrimeSigmaAlgebra_eq_primeCylinder (M := C) (le_max_left _ _)] at hm
    exact smallPrimeSigmaAlgebra_le C (hardCutoff N) A hm
  have hfinite := conditional_finite_signed_aggregate_le_ledger hStein
    (C := C) (by omega : 2≤N) hL (le_max_right _ _) hY (le_max_left _ _) A hA hpos
  have hledger := hr N (by omega) L hlo hhi A hpos hrate hbudget
  have htail := ht N (by omega) L hlo hhi A hAm hpos hrate hbudget
  have hfull : conditionalSignedAggregateDistance N L A≤
      2*Real.exp (-c'*saddleNu 1 (Real.log N))+(N : ℝ)^(-(1/3 : ℝ)+epsilon) := by
    linarith
  exact ⟨hfull,(conditional_unsigned_le_signed N L A hpos).trans hfull⟩

/-- Arbitrary size sequences use the same true laws and arithmetic sigma-algebras. -/
theorem hard_aggregate_sequence_tendsto_zero (hStein : DirectionalSteinFactorsStatement)
    (hPNT : PrimeNumberTheoremRemainder) (betaMin betaMax c : ℝ)
    (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax) (hc : 0<c)
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop)
    (A : ℕ → Set InfiniteSample)
    (hband : ∀ᶠ n in atTop, betaMin*Real.log (sizes n)≤(lengths n+1 : ℝ) ∧
      (lengths n+1 : ℝ)≤betaMax*Real.log (sizes n))
    (hA : ∀ᶠ n in atTop,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff (sizes n))) inferInstance] (A n))
    (hpos : ∀ᶠ n in atTop, 0 < infiniteRademacherMeasure.real (A n))
    (hrate : ∀ᶠ n in atTop, 1≤(fullRate (sizes n) (lengths n) : ℝ))
    (hbudget : ∀ᶠ n in atTop,
      aggregateLogCost (eventInformation (A n)) (fullRate (sizes n) (lengths n))≤
        saddleCutoff 1 (Real.log (sizes n))-c*saddleNu 1 (Real.log (sizes n))) :
    Tendsto (fun n => conditionalSignedAggregateDistance (sizes n) (lengths n) (A n)) atTop (𝓝 0) ∧
    Tendsto (fun n => conditionalUnsignedAggregateDistance (sizes n) (lengths n) (A n)) atTop (𝓝 0) := by
  obtain ⟨Nzero,hzero⟩ := hard_aggregate_event_bound hStein hPNT betaMin betaMax c (c/2) (1/6)
    hbetaMin hbeta (by linarith) (by linarith) (by norm_num)
  have herr := (aggregate_error_tendsto_zero (c/2) (1/6) (by linarith) (by norm_num)).comp hsizes
  have hbound : ∀ᶠ n in atTop,
      conditionalSignedAggregateDistance (sizes n) (lengths n) (A n)≤
        2*Real.exp (-(c/2)*saddleNu 1 (Real.log (sizes n)))+(sizes n : ℝ)^(-(1/3 : ℝ)+1/6) ∧
      conditionalUnsignedAggregateDistance (sizes n) (lengths n) (A n)≤
        2*Real.exp (-(c/2)*saddleNu 1 (Real.log (sizes n)))+(sizes n : ℝ)^(-(1/3 : ℝ)+1/6) := by
    filter_upwards [hband,hA,hpos,hrate,hbudget,hsizes.eventually (eventually_ge_atTop Nzero)]
      with n hb hA hp hr hbud hn
    exact hzero (sizes n) hn (lengths n) hb.1 hb.2 (A n) hA hp hr hbud
  exact ⟨squeeze_zero' (Filter.Eventually.of_forall (fun _ => massTotalVariation_nonneg _ _))
    (hbound.mono (fun _ h => h.1)) herr,
    squeeze_zero' (Filter.Eventually.of_forall (fun _ => massTotalVariation_nonneg _ _))
      (hbound.mono (fun _ h => h.2)) herr⟩

/-- Physical subtraction is eventually valid for arbitrary sequences of growing sizes. -/
theorem moving_sequence_depth_eventually (sizes depths : ℕ → ℕ)
    (hsizes : Tendsto sizes atTop atTop)
    (hdepths : Tendsto (fun n => (depths n : ℝ)/Real.log (sizes n)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, depths n+1≤criticalBase (sizes n) := by
  have hlog : Tendsto (fun n => Real.log (sizes n)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hsizes)
  have hplus : Tendsto (fun n => ((depths n : ℝ)+1)/Real.log (sizes n)) atTop (𝓝 0) := by
    simpa only [add_div,add_zero] using hdepths.add
      ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop hlog)
  have htwo : 0<Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hsmall := hplus.eventually (gt_mem_nhds (by positivity : (0 : ℝ)<1/Real.log 2))
  filter_upwards [hsmall,hsizes.eventually (eventually_ge_atTop (2 : ℕ))] with n hn hsize
  have hln : 0<Real.log (sizes n : ℝ) := Real.log_pos (by exact_mod_cast hsize)
  have hbase : ((depths n : ℝ)+1)≤Real.log (sizes n)/Real.log 2 := by
    have h := (div_lt_iff₀ hln).mp hn
    simpa only [one_div,mul_comm,div_eq_mul_inv,one_mul] using h.le
  unfold criticalBase
  apply (Nat.le_floor_iff (div_nonneg hln.le htwo.le)).mpr
  simpa only [Nat.cast_add,Nat.cast_one] using hbase

/-- Arbitrary size sequences keep the same logarithmic scale of the physical length. -/
theorem moving_sequence_length_ratio (sizes depths : ℕ → ℕ)
    (hsizes : Tendsto sizes atTop atTop)
    (hdepths : Tendsto (fun n => (depths n : ℝ)/Real.log (sizes n)) atTop (𝓝 0)) :
    Tendsto (fun n => ((movingLength (sizes n) (depths n) : ℝ)+1)/Real.log (sizes n))
      atTop (𝓝 (1/Real.log 2)) := by
  have hzero : Tendsto (fun N : ℕ => ((0 : ℕ) : ℝ)/Real.log N) atTop (𝓝 0) := by simp
  have hbase := (moving_length_div_log_tendsto (fun _ => 0) hzero).comp hsizes
  simp only [movingLength,Nat.sub_zero] at hbase
  have h := hbase.sub hdepths
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [moving_sequence_depth_eventually sizes depths hsizes hdepths] with n hn
  have hd : depths n≤criticalBase (sizes n) := by omega
  unfold movingLength
  rw [Nat.cast_sub hd]
  dsimp only [Function.comp_apply]
  ring

/-- The sequence domain and intensity lower bound are deduced, not postulated. -/
theorem moving_sequence_domain_eventually (sizes depths : ℕ → ℕ)
    (hsizes : Tendsto sizes atTop atTop)
    (hdepths : Tendsto (fun n => (depths n : ℝ)/Real.log (sizes n)) atTop (𝓝 0))
    (betaMin betaMax : ℝ) (hmin : betaMin<1/Real.log 2) (hmax : 1/Real.log 2<betaMax) :
    ∀ᶠ n in atTop, depths n+1≤criticalBase (sizes n) ∧
      1≤movingLength (sizes n) (depths n) ∧
      betaMin*Real.log (sizes n)≤(movingLength (sizes n) (depths n) : ℝ)+1 ∧
      (movingLength (sizes n) (depths n) : ℝ)+1≤betaMax*Real.log (sizes n) ∧
      1≤(fullRate (sizes n) (movingLength (sizes n) (depths n)) : ℝ) := by
  have hlim := moving_sequence_length_ratio sizes depths hsizes hdepths
  filter_upwards [moving_sequence_depth_eventually sizes depths hsizes hdepths,
    hlim.eventually (lt_mem_nhds hmin),hlim.eventually (gt_mem_nhds hmax),
    hsizes.eventually (eventually_ge_atTop (2 : ℕ))] with n hd hlo hhi hn
  have hln : 0<Real.log (sizes n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hdep : depths n≤criticalBase (sizes n) := by omega
  have hrate := (fullRate_depth_bounds (by omega : 1≤sizes n) hdep).1
  refine ⟨hd,by unfold movingLength;omega,((lt_div_iff₀ hln).mp hlo).le,
    ((div_lt_iff₀ hln).mp hhi).le,?_⟩
  exact (one_le_pow₀ (by norm_num : (1 : ℝ)≤2)).trans hrate

/-- The aggregate clause of 5.8 and its signed extension along every admissible size sequence. -/
theorem theorem_five_eight_aggregate_hard_sequences (hStein : DirectionalSteinFactorsStatement)
    (hPNT : PrimeNumberTheoremRemainder) (c : ℝ) (hc : 0<c)
    (sizes depths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop)
    (hdepths : Tendsto (fun n => (depths n : ℝ)/Real.log (sizes n)) atTop (𝓝 0))
    (A : ℕ → Set InfiniteSample)
    (hA : ∀ᶠ n in atTop,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff (sizes n))) inferInstance] (A n))
    (hpos : ∀ᶠ n in atTop, 0 < infiniteRademacherMeasure.real (A n))
    (hbudget : ∀ᶠ n in atTop,
      aggregateLogCost (eventInformation (A n)) (fullRate (sizes n) (movingLength (sizes n) (depths n)))≤
        saddleCutoff 1 (Real.log (sizes n))-c*saddleNu 1 (Real.log (sizes n))) :
    Tendsto (fun n => conditionalSignedAggregateDistance (sizes n) (movingLength (sizes n) (depths n)) (A n))
      atTop (𝓝 0) ∧
    Tendsto (fun n => conditionalUnsignedAggregateDistance (sizes n) (movingLength (sizes n) (depths n)) (A n))
      atTop (𝓝 0) := by
  have hlog2 : 0<Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let lo : ℝ := (1/Real.log 2)/2
  let hi : ℝ := 2*(1/Real.log 2)
  have hlo : 0<lo := by dsimp [lo];positivity
  have hlo' : lo<1/Real.log 2 := by
    dsimp [lo]
    have h : (0 : ℝ)<1/Real.log 2 := by positivity
    linarith
  have hhi : 1/Real.log 2<hi := by
    dsimp [hi]
    have h : (0 : ℝ)<1/Real.log 2 := by positivity
    linarith
  have hd := moving_sequence_domain_eventually sizes depths hsizes hdepths lo hi hlo' hhi
  exact hard_aggregate_sequence_tendsto_zero hStein hPNT lo hi c hlo (hlo'.trans hhi) hc
    sizes (fun n => movingLength (sizes n) (depths n)) hsizes A
    (hd.mono (fun _ h => ⟨h.2.2.1,h.2.2.2.1⟩)) hA hpos (hd.mono (fun _ h => h.2.2.2.2)) hbudget

/-- The usual indexing N is a specialization, with unrestricted depth o(log N). -/
theorem theorem_five_eight_aggregate_hard (hStein : DirectionalSteinFactorsStatement)
    (hPNT : PrimeNumberTheoremRemainder) (c : ℝ) (hc : 0<c)
    (depths : ℕ → ℕ)
    (hdepths : Tendsto (fun N => (depths N : ℝ)/Real.log N) atTop (𝓝 0))
    (A : ℕ → Set InfiniteSample)
    (hA : ∀ᶠ N in atTop,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff N)) inferInstance] (A N))
    (hpos : ∀ᶠ N in atTop, 0 < infiniteRademacherMeasure.real (A N))
    (hbudget : ∀ᶠ N in atTop,
      aggregateLogCost (eventInformation (A N)) (fullRate N (movingLength N (depths N)))≤
        saddleCutoff 1 (Real.log N)-c*saddleNu 1 (Real.log N)) :
    Tendsto (fun N => conditionalSignedAggregateDistance N (movingLength N (depths N)) (A N)) atTop (𝓝 0) ∧
    Tendsto (fun N => conditionalUnsignedAggregateDistance N (movingLength N (depths N)) (A N)) atTop (𝓝 0) :=
  theorem_five_eight_aggregate_hard_sequences hStein hPNT c hc id depths tendsto_id hdepths A hA hpos hbudget

end
end PaperC.V282.SignedAggregateHardBudget
