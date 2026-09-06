import PaperCV282.UnsignedLowIntensityRates
import PaperCV282.SignedAggregateHardBudget

/-! # Resolved aggregate paths at every positive intensity

The actual conditioning event and the whole countable configuration are retained.
Only a fixed information envelope is used to absorb the enlarged-window polynomial
cost. No lower bound of one on the Poisson intensity is needed.
-/
namespace PaperC.V282.UnsignedResolvedPathRates

open MeasureTheory Filter Topology InfiniteRademacher InfiniteCylinderTransfer InfiniteConditionalWords
open UnsignedLowIntensityRates SignedAggregateRates SignedAggregateComparison SignedAggregateTruncation
open UnsignedAggregateComparison AggregateCutoffRemainder GrowingMarkedTruncation RareConditioningRates
open HardPoissonRates SaddleParameters SaddleScales SaddleCutoffAdmissibility DirectionalSteinInput
open PrimeEulerPNT AllStartSoftPoisson ExactMarkedSourceTail MarkedDetruncation FiniteFieldTotalVariation

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

/-- The information envelope controls small as well as large intensities. -/
theorem profile_envelope_all_intensities {I rate A : ℝ} {N : ℕ}
    (hI : 0≤I) (hr : 0<rate) (hA : 0≤A)
    (hV : 0≤saddleCutoff 1 (Real.log N))
    (hb : I+max 0 (Real.log rate)≤A*saddleCutoff 1 (Real.log N)) :
    Real.exp I*(2 : ℝ)^(2*growingMarkCutoff N+2)*(rate^2+rate)≤
      512*Real.exp ((3*A+6)*saddleCutoff 1 (Real.log N)) := by
  let V := saddleCutoff 1 (Real.log N)
  have hAV : 0≤A*V := mul_nonneg hA hV
  have hIV : I≤A*V := by have h := le_max_left 0 (Real.log rate); dsimp [V]; linarith
  have hlV : Real.log rate≤A*V := by
    have h := le_max_right 0 (Real.log rate); dsimp [V]; linarith
  have hrV : rate≤Real.exp (A*V) := by
    rw [← Real.exp_log hr]
    exact Real.exp_le_exp.mpr hlV
  have he1 : 1≤Real.exp (A*V) := Real.one_le_exp_iff.mpr hAV
  have hrs : rate^2+rate≤2*Real.exp (2*A*V) := by
    have hsq : rate^2≤(Real.exp (A*V))^2 := by nlinarith [Real.exp_nonneg (A*V)]
    have hex : (Real.exp (A*V))^2=Real.exp (2*A*V) := by
      rw [pow_two,← Real.exp_add];congr 1;ring
    rw [← hex]
    nlinarith [Real.exp_nonneg (A*V)]
  have hf := growingMarkCutoff_profile_cost N hV
  calc
    _ ≤ (Real.exp (A*V)*(256*Real.exp (6*V)))*(2*Real.exp (2*A*V)) :=
      mul_le_mul (mul_le_mul (Real.exp_le_exp.mpr hIV) hf (by positivity) (by positivity))
        hrs (by positivity) (by positivity)
    _ = _ := by
      calc
        _ = 512*(Real.exp (A*V)*Real.exp (6*V)*Real.exp (2*A*V)) := by ring
        _ = _ := by rw [← Real.exp_add,← Real.exp_add];congr 2;dsimp [V];ring

/-- The threshold precedes both the information cost and the actual intensity. -/
theorem profile_bound_all_intensities_eventually (A epsilon : ℝ)
    (hA : 0≤A) (hepsilon : 0<epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ I rate : ℝ, 0≤I → 0<rate →
      I+max 0 (Real.log rate)≤A*saddleCutoff 1 (Real.log N) →
      32*Real.exp I*(2 : ℝ)^(2*growingMarkCutoff N+2)*(rate^2+rate)*
        (N : ℝ)^(-(1/3 : ℝ)+epsilon/2)≤(N : ℝ)^(-(1/3 : ℝ)+epsilon) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [constant_exp_saddle_le_power_eventually 16384 (3*A+6) (epsilon/2)
    (by norm_num) (by linarith),
    hlog.eventually (eventually_ge_atTop (saddleThreshold 1)),eventually_ge_atTop (1 : ℕ)]
    with N hp hN hn
  intro I rate hI hr hb
  have hV := (saddleCutoff_pos (a := 1) (by norm_num) hN).le
  have he := profile_envelope_all_intensities hI hr hA hV hb
  have hmain : 32*Real.exp I*(2 : ℝ)^(2*growingMarkCutoff N+2)*(rate^2+rate)≤
      (N : ℝ)^(epsilon/2) := by nlinarith only [he,hp]
  calc
    _ ≤ (N : ℝ)^(epsilon/2)*(N : ℝ)^(-(1/3 : ℝ)+epsilon/2) :=
      mul_le_mul_of_nonneg_right hmain (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    _ = _ := by rw [← Real.rpow_add (by exact_mod_cast (show 0<N by omega))];congr 1;ring

/-- The same geometric cutoff controls tails without any lower intensity restriction. -/
theorem tail_envelope_all_intensities {I rate eta : ℝ} {N : ℕ}
    (hI : 0≤I) (hr : 0≤rate) (heta : 0≤eta)
    (hV : 0≤saddleCutoff 1 (Real.log N)) (hnu : 0≤saddleNu 1 (Real.log N)) :
    (2*Real.exp I+1)*rate/(2 : ℝ)^(growingMarkCutoff N+1)≤
      3*Real.exp I*rate*(1+max 0 (Real.log (2*rate)))*
        Real.exp (-saddleCutoff 1 (Real.log N)+eta*saddleNu 1 (Real.log N)) := by
  have he : 1≤Real.exp I := Real.one_le_exp_iff.mpr hI
  have ht := growingMarkCutoff_geometric_tail N
  have hell : 1≤1+max 0 (Real.log (2*rate)) := by have h := le_max_left 0 (Real.log (2*rate));linarith
  have hex : Real.exp (-3*saddleCutoff 1 (Real.log N))≤
      Real.exp (-saddleCutoff 1 (Real.log N)+eta*saddleNu 1 (Real.log N)) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_nonneg heta hnu])
  calc
    _ ≤ 3*Real.exp I*rate*(1/(2 : ℝ)^(growingMarkCutoff N+1)) := by
      have hh := mul_le_mul_of_nonneg_right (show 2*Real.exp I+1≤3*Real.exp I by linarith) hr
      exact (div_le_div_of_nonneg_right hh (by positivity)).trans_eq (by ring)
    _ ≤ 3*Real.exp I*rate*Real.exp (-3*saddleCutoff 1 (Real.log N)) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ ≤ 3*Real.exp I*rate*Real.exp (-saddleCutoff 1 (Real.log N)+eta*saddleNu 1 (Real.log N)) :=
      mul_le_mul_of_nonneg_left hex (by positivity)
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hell
        (show 0≤3*Real.exp I*rate*Real.exp (-saddleCutoff 1 (Real.log N)+eta*saddleNu 1 (Real.log N)) by positivity)
      nlinarith only [hh]

/-- A true full-path error at all positive intensities. The sole literature
premises are the directional Stein solution bounds and the ordinary PNT. -/
theorem resolved_aggregate_event_bound (hStein : DirectionalSteinFactorsStatement)
    (hPNT : PrimeNumberTheoremRemainder) (betaMin betaMax A epsilon eta : ℝ)
    (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax) (hA : 0≤A)
    (hepsilon : 0<epsilon) (heta : 0<eta) :
    ∃ Nzero : ℕ, ∀ N≥Nzero, ∀ L : ℕ,
      betaMin*Real.log N≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log N →
      ∀ C : Set InfiniteSample,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff N)) inferInstance] C →
      0 < infiniteRademacherMeasure.real C →
      eventInformation C+max 0 (Real.log (fullRate N L : ℝ))≤A*saddleCutoff 1 (Real.log N) →
      conditionalSignedAggregateDistance N L C≤
        40*Real.exp (eventInformation C)*(fullRate N L : ℝ)*
          (1+max 0 (Real.log (2*(fullRate N L : ℝ))))*
          Real.exp (-saddleCutoff 1 (Real.log N)+eta*saddleNu 1 (Real.log N))+
          (N : ℝ)^(-(1/3 : ℝ)+epsilon) ∧
      conditionalUnsignedAggregateDistance N L C≤
        40*Real.exp (eventInformation C)*(fullRate N L : ℝ)*
          (1+max 0 (Real.log (2*(fullRate N L : ℝ))))*
          Real.exp (-saddleCutoff 1 (Real.log N)+eta*saddleNu 1 (Real.log N))+
          (N : ℝ)^(-(1/3 : ℝ)+epsilon) := by
  have hbmax : 0<betaMax := hbetaMin.trans hbeta
  obtain ⟨Nr,hr⟩ := signed_aggregate_ledger_all_intensities_eventually hPNT betaMin (2*betaMax)
    (epsilon/2) eta hbetaMin (by linarith) (by linarith) heta
  obtain ⟨Nt,ht⟩ := source_mark_tail_le_eventually betaMin (2*betaMax) (1/6)
    hbetaMin (by linarith) (by norm_num)
  obtain ⟨Nb,hb⟩ := growing_mark_band_eventually betaMax hbmax
  obtain ⟨Na,ha⟩ := saddleCutoff_nat_admissible_eventually 1 (4*betaMax) (by norm_num) (by positivity)
  obtain ⟨Nl,hl⟩ := TouchingPairMass.length_pos_eventually betaMin hbetaMin
  obtain ⟨Np,hp⟩ := eventually_atTop.1 (profile_bound_all_intensities_eventually A epsilon hA hepsilon)
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Ns,hs⟩ := eventually_atTop.1 (hlog.eventually (eventually_ge_atTop (saddleThreshold 1)))
  refine ⟨max Nr (max Nt (max Nb (max Na (max Nl (max Np (max Ns 2)))))),?_⟩
  intro N hN L hlo hhi C hC hpos hbudget
  have hL : 1≤L := hl N (by omega) L hlo
  have hupper := hb N (by omega) L hhi
  have hupper' : ((L+growingMarkCutoff N+2 : ℕ)+1 : ℝ)≤(4*betaMax)*Real.log N := by
    push_cast
    have hE : (0 : ℝ)≤growingMarkCutoff N := Nat.cast_nonneg _
    have hLL : (1 : ℝ)≤L := by exact_mod_cast hL
    nlinarith
  have hY : 2*(L+growingMarkCutoff N+2)≤hardCutoff N :=
    (ha N (by omega) (L+growingMarkCutoff N+2) hupper').2.2.1
  let M : ℕ := max (hardCutoff N) (dyadicCutoff N (L+growingMarkCutoff N+1))
  have hCm : MeasurableSet C := by
    have hm := hC
    rw [← smallPrimeSigmaAlgebra_eq_primeCylinder (M := M) (le_max_left _ _)] at hm
    exact smallPrimeSigmaAlgebra_le M (hardCutoff N) C hm
  have hfinite := conditional_finite_signed_aggregate_le_ledger hStein
    (C := M) (by omega : 2≤N) hL (le_max_right _ _) hY (le_max_left _ _) C hC hpos
  have hledger := hr N (by omega) L (growingMarkCutoff N) hlo hupper
  have hrate : 0<(fullRate N L : ℝ) := by
    rw [fullRate_coe]
    have hn : 0<N := by omega
    positivity
  have hpoly := hp N (by omega) (eventInformation C) (fullRate N L)
    (eventInformation_nonneg C hpos) hrate hbudget
  have hweight := mul_le_mul_of_nonneg_left hledger (Real.exp_nonneg (eventInformation C))
  have hevent := exp_eventInformation C hpos
  rw [div_eq_mul_inv,← hevent] at hfinite
  have hsource := ht N (by omega) L (growingMarkCutoff N) (by
    have he : (0 : ℝ)≤growingMarkCutoff N := Nat.cast_nonneg _
    linarith) hupper
  have hnp : 1≤(N : ℝ) := by exact_mod_cast (show 1≤N by omega)
  have hpow : (N : ℝ)^(-(1/(2 : ℝ))+1/6)≤1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hnp (by norm_num)
  have hsource' : infiniteMarkTailProbability N L (growingMarkCutoff N)≤
      2*((fullRate N L : ℝ)/(2 : ℝ)^(growingMarkCutoff N+1)) := by
    nlinarith [show 0≤(fullRate N L : ℝ)/(2 : ℝ)^(growingMarkCutoff N+1) by positivity]
  have hV := (saddleCutoff_pos (a := 1) (by norm_num) (hs N (by omega))).le
  have hnu : 0≤saddleNu 1 (Real.log N) := div_nonneg (Real.log_nonneg hnp) hV
  have htailnum := tail_envelope_all_intensities (eventInformation_nonneg C hpos)
    hrate.le heta.le hV hnu
  have htails : infiniteMarkTailProbability N L (growingMarkCutoff N)/infiniteRademacherMeasure.real C+
      (fullRate N L : ℝ)/(2 : ℝ)^(growingMarkCutoff N+1)≤
      3*Real.exp (eventInformation C)*(fullRate N L : ℝ)*(1+max 0 (Real.log (2*(fullRate N L : ℝ))))*
        Real.exp (-saddleCutoff 1 (Real.log N)+eta*saddleNu 1 (Real.log N)) := by
    apply le_trans (add_le_add (div_le_div_of_nonneg_right hsource' hpos.le) (le_refl _)) ?_
    calc
      _ = (2*Real.exp (eventInformation C)+1)*(fullRate N L : ℝ)/
          (2 : ℝ)^(growingMarkCutoff N+1) := by rw [hevent];ring
      _ ≤ _ := htailnum
  have hfull := conditional_signedAggregate_tv_le_finite_and_tails N L (growingMarkCutoff N) C hCm hpos
  have hlead : 0≤Real.exp (eventInformation C)*(fullRate N L : ℝ)*
      (1+max 0 (Real.log (2*(fullRate N L : ℝ))))*
      Real.exp (-saddleCutoff 1 (Real.log N)+eta*saddleNu 1 (Real.log N)) := by positivity
  have hbound : conditionalSignedAggregateDistance N L C≤
      40*Real.exp (eventInformation C)*(fullRate N L : ℝ)*
        (1+max 0 (Real.log (2*(fullRate N L : ℝ))))*
        Real.exp (-saddleCutoff 1 (Real.log N)+eta*saddleNu 1 (Real.log N))+
        (N : ℝ)^(-(1/3 : ℝ)+epsilon) := by
    nlinarith only [hfinite,hweight,hpoly,htails,hfull,hlead]
  exact ⟨hbound,(conditional_unsigned_le_signed N L C hpos).trans hbound⟩

end
end PaperC.V282.UnsignedResolvedPathRates
