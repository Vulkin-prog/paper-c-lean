import PaperCV282.AggregateInformationBudget

/-!
# Uniform control of the enlarged value profile in the aggregate budget

The cutoff used here is the actual integer 3 ceil(V/log 2). Its exponential
cost is retained explicitly before being absorbed into an arbitrary power
margin. The same cutoff removes conditional and target tails under I+log λ.
-/
namespace PaperC.V282.AggregateCutoffRemainder

open Filter Topology SaddleParameters SaddleScales SaddlePoissonScales
open SaddleMarkTruncation GrowingMarkedTruncation AggregateInformationBudget
open SaddleCutoffAdmissibility SaddleAsymptotics PrimeEulerSaddle

noncomputable section

theorem growingMarkCutoff_cost_upper (N : ℕ)
    (hV : 0≤saddleCutoff 1 (Real.log N)) :
    (growingMarkCutoff N : ℝ)*Real.log 2≤3*saddleCutoff 1 (Real.log N)+3*Real.log 2 := by
  have hl : 0<Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hc := (Nat.ceil_lt_add_one (div_nonneg hV hl.le)).le
  change (criticalMarkCutoff N : ℝ)≤saddleCutoff 1 (Real.log N)/Real.log 2+1 at hc
  have h := mul_le_mul_of_nonneg_right hc hl.le
  rw [add_mul,div_mul_cancel₀ _ hl.ne',one_mul] at h
  unfold growingMarkCutoff
  push_cast
  linarith

theorem growingMarkCutoff_profile_cost (N : ℕ)
    (hV : 0≤saddleCutoff 1 (Real.log N)) :
    (2 : ℝ)^(2*growingMarkCutoff N+2)≤256*Real.exp (6*saddleCutoff 1 (Real.log N)) := by
  have hc := growingMarkCutoff_cost_upper N hV
  have hp : (2 : ℝ)^(2*growingMarkCutoff N+2)=
      Real.exp (((2*growingMarkCutoff N+2 : ℕ) : ℝ)*Real.log 2) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]
  rw [hp]
  have hh : ((2*growingMarkCutoff N+2 : ℕ) : ℝ)*Real.log 2≤
      6*saddleCutoff 1 (Real.log N)+8*Real.log 2 := by push_cast;linarith
  calc
    _ ≤ Real.exp (6*saddleCutoff 1 (Real.log N)+8*Real.log 2) := Real.exp_le_exp.mpr hh
    _ = _ := by
      rw [Real.exp_add]
      have h8 : Real.exp (8*Real.log (2 : ℝ))=256 := by
        have h := Real.exp_nat_mul (Real.log 2) 8
        norm_num [Real.exp_log (by norm_num : (0 : ℝ)<2)] at h
        exact h
      rw [h8];ring

/-- Fixed constants as well as exp(O(V)) fit into every positive power margin. -/
theorem constant_exp_saddle_le_power_eventually (C K epsilon : ℝ)
    (hC : 0<C) (hepsilon : 0<epsilon) :
    ∀ᶠ N : ℕ in atTop,
      C*Real.exp (K*saddleCutoff 1 (Real.log N))≤(N : ℝ)^epsilon := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim := (tendsto_const_nhds (x := Real.log C)).div_atTop hlog |>.add
    (((tendsto_saddleCutoff_div_height (a := 1) (by norm_num)).comp hlog).const_mul K)
  have hs := hlim.eventually (gt_mem_nhds (by simpa using hepsilon))
  filter_upwards [hs,eventually_ge_atTop (2 : ℕ)] with N hs hN
  have hn : 0<Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hp : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hratio : (Real.log C+K*saddleCutoff 1 (Real.log N))/Real.log N<epsilon := by
    simpa only [add_div,mul_div_assoc,Function.comp_apply] using hs
  rw [Real.rpow_def_of_pos hp,← Real.exp_log hC,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simpa only [mul_comm] using ((div_lt_iff₀ hn).mp hratio).le

/-- The unconditioned profile can be bounded before using the improvement in
its Hessian factor: the whole exponential cost is still subpolynomial. -/
theorem aggregate_profile_envelope {I rate V c nu : ℝ} {N : ℕ}
    (hI : 0≤I) (hr : 1≤rate) (hc : 0≤c) (hnu : 0≤nu)
    (hV : V=saddleCutoff 1 (Real.log N))
    (hb : aggregateLogCost I rate≤V-c*nu) :
    Real.exp I*rate^2*(1+Real.log (2*rate))*(2 : ℝ)^(2*growingMarkCutoff N+2)≤
      512*Real.exp (9*V) := by
  obtain ⟨hIV,hrV,hweight⟩ := aggregate_parameters_le hI hr hc hnu hb
  have hV0 : 0≤V := hI.trans hIV
  have hrate : rate≤Real.exp V := by rw [← Real.exp_log (by linarith : 0<rate)];exact Real.exp_le_exp.mpr hrV
  have hlog2 : Real.log (2 : ℝ)≤1 := by nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)]
  have hlog0 : 0≤Real.log (2*rate) := Real.log_nonneg (by linarith)
  have hfac : 1+Real.log (2*rate)≤2*Real.exp V := by
    rw [Real.log_mul (by norm_num) (by linarith : rate≠0)]
    have he := Real.add_one_le_exp V
    linarith
  have hp := growingMarkCutoff_profile_cost N (hV ▸ hV0)
  rw [← hV] at hp
  have hw : Real.exp I*rate^2≤Real.exp (2*V) := by
    have hh := mul_le_mul hweight hrate (by linarith : 0≤rate) (Real.exp_nonneg V)
    rw [← Real.exp_add] at hh
    simpa only [pow_two,mul_assoc,two_mul] using hh
  calc
    _ ≤ (Real.exp (2*V)*(2*Real.exp V))*(256*Real.exp (6*V)) :=
      mul_le_mul (mul_le_mul hw hfac (by positivity) (Real.exp_nonneg _)) hp (by positivity) (by positivity)
    _ = _ := by
      calc
        _ = 512*(Real.exp (2*V)*Real.exp V*Real.exp (6*V)) := by ring
        _ = _ := by rw [← Real.exp_add,← Real.exp_add];congr 2;ring

/-- The actual enlarged profile, multiplied by its conditional cost, preserves
an arbitrary polynomial error exponent. -/
theorem aggregate_profile_bound_eventually (K c epsilon : ℝ)
    (hK : 0<K) (hc : 0≤c) (hepsilon : 0<epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ I rate : ℝ, 0≤I → 1≤rate →
      aggregateLogCost I rate≤saddleCutoff 1 (Real.log N)-c*saddleNu 1 (Real.log N) →
      K*Real.exp I*rate^2*(1+Real.log (2*rate))*(2 : ℝ)^(2*growingMarkCutoff N+2)*
        (N : ℝ)^(-(1/3 : ℝ)+epsilon/2)≤(N : ℝ)^(-(1/3 : ℝ)+epsilon) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [constant_exp_saddle_le_power_eventually (512*K) 9 (epsilon/2) (by positivity) (by linarith),
    hlog.eventually (eventually_ge_atTop (saddleThreshold 1)),eventually_ge_atTop (1 : ℕ)] with N hp hN hn
  intro I rate hI hr hb
  have hV := saddleCutoff_pos (a := 1) (by norm_num) hN
  have hnu : 0≤saddleNu 1 (Real.log N) := div_nonneg
    (((saddleThreshold_pos (a := 1) (by norm_num)).trans_le hN).le) hV.le
  have he := aggregate_profile_envelope hI hr hc hnu rfl hb
  have hh := mul_le_mul_of_nonneg_left he hK.le
  have hmain : K*Real.exp I*rate^2*(1+Real.log (2*rate))*(2 : ℝ)^(2*growingMarkCutoff N+2)≤
      (N : ℝ)^(epsilon/2) := by nlinarith
  calc
    _ ≤ (N : ℝ)^(epsilon/2)*(N : ℝ)^(-(1/3 : ℝ)+epsilon/2) :=
      mul_le_mul_of_nonneg_right hmain (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    _ = _ := by rw [← Real.rpow_add (by exact_mod_cast (show 0<N by omega))];congr 1;ring

/-- The crude conditional first-moment tail suffices at the chosen larger cutoff. -/
theorem aggregate_tail_envelope {I rate c nu : ℝ} {N : ℕ}
    (hI : 0≤I) (hr : 1≤rate) (hc : 0≤c) (hnu : 0≤nu)
    (hb : aggregateLogCost I rate≤saddleCutoff 1 (Real.log N)-c*nu) :
    (2*Real.exp I+1)*rate/(2 : ℝ)^(growingMarkCutoff N+1)≤
      3*Real.exp (-2*saddleCutoff 1 (Real.log N)) := by
  obtain ⟨_,_,hw⟩ := aggregate_parameters_le hI hr hc hnu hb
  have he : 1≤Real.exp I := Real.one_le_exp_iff.mpr hI
  have ht := growingMarkCutoff_geometric_tail N
  have hn : 0≤rate := by linarith
  calc
    _ ≤ 3*(Real.exp I*rate)*(1/(2 : ℝ)^(growingMarkCutoff N+1)) := by
      have hden : 0<(2 : ℝ)^(growingMarkCutoff N+1) := by positivity
      apply (div_le_iff₀ hden).mpr
      field_simp
      nlinarith
    _ ≤ 3*Real.exp (saddleCutoff 1 (Real.log N))*Real.exp (-3*saddleCutoff 1 (Real.log N)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hw (by norm_num)) ht (by positivity) (by positivity)
    _ = _ := by rw [mul_assoc,← Real.exp_add];congr 2;ring

/-- This tail is smaller than every fixed positive nu-scale remainder. -/
theorem aggregate_tail_le_margin_eventually (c' : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      3*Real.exp (-2*saddleCutoff 1 (Real.log N))≤Real.exp (-c'*saddleNu 1 (Real.log N)) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hv := (tendsto_saddleCutoff_atTop (a := 1) (by norm_num)).comp hlog
  have hlim := (tendsto_const_nhds (x := Real.log 3)).div_atTop hv |>.add
    (((tendsto_nu_div_saddleCutoff (a := 1) (by norm_num)).comp hlog).const_mul c')
  have hs := hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)+c'*0<2))
  filter_upwards [hs,hv.eventually (eventually_gt_atTop (0 : ℝ))] with N hs hp
  have hh : (Real.log 3+c'*saddleNu 1 (Real.log N))/saddleCutoff 1 (Real.log N)<2 := by
    simpa only [add_div,mul_div_assoc,Function.comp_apply] using hs
  have h := (div_lt_iff₀ hp).mp hh
  simp only [Function.comp_apply] at h
  rw [← Real.exp_log (by norm_num : (0 : ℝ)<3),← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

end
end PaperC.V282.AggregateCutoffRemainder
