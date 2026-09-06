import PaperCV282.LabelledInformationBudget

/-!
# The movable labelled information budget

The two source-weighted errors retain their separate linear and quadratic
intensities. The rounded mark cutoff is fixed before the event and length.
-/
namespace PaperC.V282.MovableMarkedBudget

open Filter Topology SaddleParameters SaddleScales SaddlePoissonScales SaddleCutoffAdmissibility

noncomputable section

def movableLogCost (I rate : ℝ) : ℝ := I+Real.log rate

def movableMarkCutoff (N : ℕ) : ℕ := 3*⌈saddleCutoff 2 (Real.log N)/Real.log 2⌉₊

theorem movableMarkCutoff_cost (N : ℕ) :
    3*saddleCutoff 2 (Real.log N) ≤ (movableMarkCutoff N : ℝ)*Real.log 2 := by
  have h := (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ)<2))).mp
    (Nat.le_ceil (saddleCutoff 2 (Real.log N)/Real.log 2))
  unfold movableMarkCutoff
  push_cast
  linarith

theorem movableMarkCutoff_geometric_tail (N : ℕ) :
    1/(2 : ℝ)^(movableMarkCutoff N+1) ≤ Real.exp (-3*saddleCutoff 2 (Real.log N)) := by
  have hcost := movableMarkCutoff_cost N
  have hlog : 0<Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hpow : (2 : ℝ)^(movableMarkCutoff N+1) =
      Real.exp (((movableMarkCutoff N+1 : ℕ) : ℝ)*Real.log 2) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]
  rw [hpow,one_div,← Real.exp_neg]
  apply Real.exp_le_exp.mpr
  push_cast
  linarith

theorem movableMarkCutoff_div_log_tendsto_zero :
    Tendsto (fun N : ℕ => ((movableMarkCutoff N : ℝ)+1)/Real.log N) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ =>
      3*(saddleCutoff 2 (Real.log N)/Real.log N)/Real.log 2+4/Real.log N)
      atTop (𝓝 0) := by
    simpa using (((tendsto_saddleCutoff_div_height (a := 2) (by norm_num)).comp hlog).const_mul 3).div_const
      (Real.log 2) |>.add (tendsto_const_nhds.div_atTop hlog)
  apply squeeze_zero' _ _ hlim
  · filter_upwards [hlog.eventually (eventually_gt_atTop (0 : ℝ))] with N hN
    positivity
  · filter_upwards [hlog.eventually (eventually_ge_atTop (saddleThreshold 2)),
      hlog.eventually (eventually_gt_atTop (0 : ℝ))] with N hN hn
    have hv := saddleCutoff_pos (a := 2) (by norm_num) hN
    have hc := (Nat.ceil_lt_add_one (div_nonneg hv.le
      (Real.log_pos (by norm_num : (1 : ℝ)<2)).le)).le
    calc
      _ ≤ (3*(saddleCutoff 2 (Real.log N)/Real.log 2)+4)/Real.log N := by
        apply div_le_div_of_nonneg_right _ hn.le
        unfold movableMarkCutoff
        push_cast
        linarith
      _ = _ := by ring

theorem movable_mark_band_eventually (beta : ℝ) (hbeta : 0<beta) :
    ∃ Nzero : ℕ, ∀ N≥Nzero, ∀ L : ℕ,
      (L+1 : ℝ)≤beta*Real.log N →
      (L+movableMarkCutoff N+2 : ℝ)≤(2*beta)*Real.log N := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Ne,he⟩ := eventually_atTop.1 (movableMarkCutoff_div_log_tendsto_zero.eventually (gt_mem_nhds hbeta))
  obtain ⟨Np,hp⟩ := eventually_atTop.1 (hlog.eventually (eventually_gt_atTop (0 : ℝ)))
  refine ⟨max Ne Np,?_⟩
  intro N hN L hL
  have hE := (div_lt_iff₀ (hp N (by omega))).mp (he N (by omega))
  linarith

/-- Positivity of information controls the quadratic cost from the same linear budget. -/
theorem movable_product_bounds {I rate V c nu : ℝ} (hI : 0≤I) (hr : 1≤rate)
    (hc : 0≤c) (hnu : 0≤nu) (hb : movableLogCost I rate≤V/2-c*nu) :
    Real.exp I*rate ≤ Real.exp (V/2-c*nu) ∧
    Real.exp I*rate^2 ≤ Real.exp (V-2*c*nu) ∧
    Real.exp I*rate*(1+rate) ≤ 2*Real.exp V := by
  have hrp : 0<rate := by linarith
  have hlinear : Real.exp I*rate=Real.exp (I+Real.log rate) := by
    rw [Real.exp_add,Real.exp_log hrp]
  have hquadratic : Real.exp I*rate^2=Real.exp (I+2*Real.log rate) := by
    rw [show I+2*Real.log rate=I+Real.log rate+Real.log rate by ring,
      Real.exp_add,Real.exp_add,Real.exp_log hrp]
    ring
  have hfirst : Real.exp I*rate ≤ Real.exp (V/2-c*nu) := by
    rw [hlinear]
    exact Real.exp_le_exp.mpr hb
  have hsecond : Real.exp I*rate^2 ≤ Real.exp (V-2*c*nu) := by
    rw [hquadratic]
    apply Real.exp_le_exp.mpr
    unfold movableLogCost at hb
    linarith
  have hsecond' : Real.exp I*rate^2 ≤ Real.exp V := hsecond.trans (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hc hnu]))
  refine ⟨hfirst,hsecond,?_⟩
  have hp : 0≤Real.exp I*rate*(rate-1) := mul_nonneg (by positivity) (sub_nonneg.mpr hr)
  nlinarith

/-- A fixed power absorbs the movable saddle, uniformly before all information costs. -/
theorem movable_polynomial_factor_eventually :
    ∃ Nzero : ℕ, ∀ N≥Nzero,
      Real.exp (saddleCutoff 2 (Real.log N))*(N : ℝ)^(-(1/(6 : ℝ))) ≤
        (N : ℝ)^(-(1/(12 : ℝ))) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio := ((tendsto_saddleCutoff_div_height (a := 2) (by norm_num)).comp hlog).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ)<1/12))
  apply eventually_atTop.1
  filter_upwards [hratio,eventually_ge_atTop (2 : ℕ)] with N hv hN
  have hn : 0<Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hcost := (div_lt_iff₀ hn).mp hv
  have hNp : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  rw [Real.rpow_def_of_pos hNp,Real.rpow_def_of_pos hNp,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

theorem movable_budget_bound_eventually (c : ℝ) (hc : 0<c) :
    ∃ Nzero : ℕ, ∀ N≥Nzero, ∀ I rate : ℝ, 0≤I → 1≤rate →
      movableLogCost I rate≤saddleCutoff 2 (Real.log N)/2-c*saddleNu 2 (Real.log N) →
      Real.exp I*(32*(rate*Real.exp (-saddleCutoff 2 (Real.log N)/2+(c/2)*saddleNu 2 (Real.log N))+
        rate^2*Real.exp (-saddleCutoff 2 (Real.log N)+(c/2)*saddleNu 2 (Real.log N))+
        rate*(1+rate)*(N : ℝ)^(-(1/(6 : ℝ))))+
        (rate/(2 : ℝ)^(movableMarkCutoff N+1))*(2+(N : ℝ)^(-(1/(3 : ℝ))))) ≤
      64*Real.exp (-(c/2)*saddleNu 2 (Real.log N))+
        64*(N : ℝ)^(-(1/(12 : ℝ)))+3*Real.exp (-saddleCutoff 2 (Real.log N)) := by
  obtain ⟨Np,hp⟩ := movable_polynomial_factor_eventually
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Ns,hs⟩ := eventually_atTop.1 (hlog.eventually (eventually_ge_atTop (saddleThreshold 2)))
  refine ⟨max Np (max Ns 2),?_⟩
  intro N hN I rate hI hr hb
  have hv := saddleCutoff_pos (a := 2) (by norm_num) (hs N (by omega))
  have hn : 1≤(N : ℝ) := by exact_mod_cast (show 1≤N by omega)
  have hnu : 0≤saddleNu 2 (Real.log N) := by
    unfold saddleNu
    exact div_nonneg (Real.log_nonneg hn) hv.le
  obtain ⟨hlinear,hquadratic,hprod⟩ := movable_product_bounds hI hr hc.le hnu hb
  have hfirst : Real.exp I*rate*
      Real.exp (-saddleCutoff 2 (Real.log N)/2+(c/2)*saddleNu 2 (Real.log N)) ≤
        Real.exp (-(c/2)*saddleNu 2 (Real.log N)) := by
    apply (mul_le_mul_of_nonneg_right hlinear (Real.exp_nonneg _)).trans
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    ring_nf
    exact le_rfl
  have hsecond : Real.exp I*rate^2*
      Real.exp (-saddleCutoff 2 (Real.log N)+(c/2)*saddleNu 2 (Real.log N)) ≤
        Real.exp (-(c/2)*saddleNu 2 (Real.log N)) := by
    apply (mul_le_mul_of_nonneg_right hquadratic (Real.exp_nonneg _)).trans
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hc.le hnu]
  have hpoly := (mul_le_mul_of_nonneg_right hprod
    (Real.rpow_nonneg (by positivity : (0 : ℝ)≤N) (-(1/(6 : ℝ)))))
  have hp' := hp N (by omega)
  have htail : Real.exp I*(rate/(2 : ℝ)^(movableMarkCutoff N+1))*
      (2+(N : ℝ)^(-(1/(3 : ℝ)))) ≤ 3*Real.exp (-saddleCutoff 2 (Real.log N)) := by
    have hw : Real.exp I*rate ≤ Real.exp (saddleCutoff 2 (Real.log N)) :=
      hlinear.trans (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hc.le hnu]))
    have hh := mul_le_mul hw (movableMarkCutoff_geometric_tail N) (by positivity) (Real.exp_nonneg _)
    have hh' : Real.exp I*(rate/(2 : ℝ)^(movableMarkCutoff N+1)) ≤
        Real.exp (-2*saddleCutoff 2 (Real.log N)) := by
      have heq : Real.exp (saddleCutoff 2 (Real.log N))*Real.exp (-3*saddleCutoff 2 (Real.log N)) =
          Real.exp (-2*saddleCutoff 2 (Real.log N)) := by rw [← Real.exp_add];congr 1;ring
      rw [heq] at hh
      simpa only [mul_one_div,mul_div_assoc] using hh
    have hh'' := hh'.trans (Real.exp_le_exp.mpr (by linarith : -2*saddleCutoff 2 (Real.log N)≤
      -saddleCutoff 2 (Real.log N)))
    have hpow : (N : ℝ)^(-(1/(3 : ℝ)))≤1 := Real.rpow_le_one_of_one_le_of_nonpos hn (by norm_num)
    have hm := mul_le_mul hh'' (by linarith : 2+(N : ℝ)^(-(1/(3 : ℝ)))≤3)
      (by positivity) (Real.exp_nonneg _)
    nlinarith
  nlinarith

theorem movable_budget_error_tendsto_zero (c : ℝ) (hc : 0<c) :
    Tendsto (fun N : ℕ => 64*Real.exp (-(c/2)*saddleNu 2 (Real.log N))+
      64*(N : ℝ)^(-(1/(12 : ℝ)))+3*Real.exp (-saddleCutoff 2 (Real.log N))) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hnu := (tendsto_saddleNu_atTop (a := 2) (by norm_num)).comp hlog
  have he := Real.tendsto_exp_atBot.comp (hnu.const_mul_atTop_of_neg (by linarith : -(c/2)<0))
  have hp := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<1/12)).comp tendsto_natCast_atTop_atTop
  have hv := saddle_exponential_nat_tendsto_zero 2 1 0 (by norm_num) (by norm_num)
  simpa only [one_mul,neg_mul,zero_mul,add_zero,mul_zero,Function.comp_def] using
    ((he.const_mul 64).add (hp.const_mul 64)).add (hv.const_mul 3)

end
end PaperC.V282.MovableMarkedBudget
