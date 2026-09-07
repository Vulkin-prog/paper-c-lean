import PaperCV282.GrowingMarkedTruncation
import PaperCV282.SaddleErrorExponent

/-!
# The labelled hard information budget, with all polynomial and tail costs

These numerical inequalities apply to the exact product exp(I)*lambda*(1+lambda).
They preserve a positive c*nu margin and the actual rounded mark cutoff.
-/
namespace PaperC.V282.LabelledInformationBudget

open Filter Topology SaddleParameters SaddleScales SaddlePoissonScales
open SaddleCutoffAdmissibility GrowingMarkedTruncation

noncomputable section

def labelledLogCost (I rate : ℝ) : ℝ := I+Real.log rate+Real.log (1+rate)

theorem exp_labelledLogCost (I rate : ℝ) (hr : 0 < rate) :
    Real.exp (labelledLogCost I rate)=Real.exp I*rate*(1+rate) := by
  unfold labelledLogCost
  rw [Real.exp_add,Real.exp_add,Real.exp_log hr,Real.exp_log (by positivity)]

theorem labelled_product_le {I rate V c nu : ℝ} (hr : 0 < rate)
    (hbudget : labelledLogCost I rate ≤ V-c*nu) :
    Real.exp I*rate*(1+rate) ≤ Real.exp (V-c*nu) := by
  rw [← exp_labelledLogCost I rate hr]
  exact Real.exp_le_exp.mpr hbudget

theorem source_weight_le {I rate V c nu : ℝ} (hr : 1 ≤ rate) (hc : 0 ≤ c) (hnu : 0 ≤ nu)
    (hbudget : labelledLogCost I rate ≤ V-c*nu) : Real.exp I*rate ≤ Real.exp V := by
  have hlog : 0 ≤ Real.log (1+rate) := Real.log_nonneg (by linarith)
  have hcost : I+Real.log rate ≤ V := by
    unfold labelledLogCost at hbudget
    nlinarith [mul_nonneg hc hnu]
  calc
    _ = Real.exp (I+Real.log rate) := by rw [Real.exp_add,Real.exp_log (by linarith)]
    _ ≤ _ := Real.exp_le_exp.mpr hcost

/-- A fixed negative power still wins after multiplication by exp(V). -/
theorem hard_polynomial_factor_eventually :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero,
      Real.exp (saddleCutoff 1 (Real.log N))*(N : ℝ)^(-(1/(6 : ℝ))) ≤
        (N : ℝ)^(-(1/(12 : ℝ))) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio := ((tendsto_saddleCutoff_div_height (a := 1) (by norm_num)).comp hlog).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ)<1/12))
  apply eventually_atTop.1
  filter_upwards [hratio,eventually_ge_atTop (2 : ℕ)] with N hv hN
  have hn : 0<Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hcost := (div_lt_iff₀ hn).mp hv
  have hNp : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  rw [Real.rpow_def_of_pos hNp,Real.rpow_def_of_pos hNp,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

/-- The finite comparison and both source-weighted tails vanish under the printed hard budget. -/
theorem labelled_budget_bound_eventually (c : ℝ) (hc : 0 < c) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ I rate : ℝ, 1 ≤ rate →
      labelledLogCost I rate ≤ saddleCutoff 1 (Real.log N)-c*saddleNu 1 (Real.log N) →
      Real.exp I*(32*rate*(1+rate)*
        (Real.exp (-saddleCutoff 1 (Real.log N)+(c/2)*saddleNu 1 (Real.log N))+
          (N : ℝ)^(-(1/(6 : ℝ))))+
        (rate/(2 : ℝ)^(growingMarkCutoff N+1))*(2+(N : ℝ)^(-(1/(3 : ℝ))))) ≤
      32*Real.exp (-(c/2)*saddleNu 1 (Real.log N))+
        32*(N : ℝ)^(-(1/(12 : ℝ)))+3*Real.exp (-saddleCutoff 1 (Real.log N)) := by
  obtain ⟨Np,hp⟩ := hard_polynomial_factor_eventually
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Ns,hs⟩ := eventually_atTop.1 (hlog.eventually (eventually_ge_atTop (saddleThreshold 1)))
  refine ⟨max Np (max Ns 2),?_⟩
  intro N hN I rate hr hb
  have hv := saddleCutoff_pos (a := 1) (by norm_num) (hs N (by omega))
  have hn : 1≤(N : ℝ) := by exact_mod_cast (show 1≤N by omega)
  have hnu : 0 ≤ saddleNu 1 (Real.log N) := by
    unfold saddleNu
    exact div_nonneg (Real.log_nonneg hn) hv.le
  have hprod := labelled_product_le (by linarith : 0<rate) hb
  have hw := source_weight_le hr hc.le hnu hb
  have hpow : (N : ℝ)^(-(1/(3 : ℝ))) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn (by norm_num)
  have hfirst : Real.exp I*rate*(1+rate)*
      Real.exp (-saddleCutoff 1 (Real.log N)+(c/2)*saddleNu 1 (Real.log N)) ≤
        Real.exp (-(c/2)*saddleNu 1 (Real.log N)) := by
    apply (mul_le_mul_of_nonneg_right hprod (Real.exp_nonneg _)).trans
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    ring_nf
    exact le_rfl
  have hprodV : Real.exp I*rate*(1+rate) ≤ Real.exp (saddleCutoff 1 (Real.log N)) :=
    hprod.trans (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hc.le hnu]))
  have hpoly := (mul_le_mul_of_nonneg_right hprodV
    (Real.rpow_nonneg (by positivity : (0 : ℝ)≤N) (-(1/(6 : ℝ))))).trans (hp N (by omega))
  have htail : Real.exp I*(rate/(2 : ℝ)^(growingMarkCutoff N+1))*
      (2+(N : ℝ)^(-(1/(3 : ℝ)))) ≤ 3*Real.exp (-saddleCutoff 1 (Real.log N)) := by
    have hg := growingMarkCutoff_geometric_tail N
    have hh := mul_le_mul hw hg (by positivity) (Real.exp_nonneg _)
    have hh' : Real.exp I*(rate/(2 : ℝ)^(growingMarkCutoff N+1)) ≤
        Real.exp (-2*saddleCutoff 1 (Real.log N)) := by
      have heq : Real.exp (saddleCutoff 1 (Real.log N))*Real.exp (-3*saddleCutoff 1 (Real.log N)) =
          Real.exp (-2*saddleCutoff 1 (Real.log N)) := by rw [← Real.exp_add]; congr 1; ring
      rw [heq] at hh
      simpa only [mul_one_div,mul_div_assoc] using hh
    have hh'' := hh'.trans (Real.exp_le_exp.mpr (by linarith : -2*saddleCutoff 1 (Real.log N) ≤
      -saddleCutoff 1 (Real.log N)))
    have hm := mul_le_mul hh'' (by linarith : 2+(N : ℝ)^(-(1/(3 : ℝ)))≤3)
      (by positivity) (Real.exp_nonneg _)
    nlinarith
  nlinarith

/-- The explicit numerical upper bound actually tends to zero. -/
theorem labelled_budget_error_tendsto_zero (c : ℝ) (hc : 0 < c) :
    Tendsto (fun N : ℕ => 32*Real.exp (-(c/2)*saddleNu 1 (Real.log N))+
      32*(N : ℝ)^(-(1/(12 : ℝ)))+3*Real.exp (-saddleCutoff 1 (Real.log N))) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hnu := (tendsto_saddleNu_atTop (a := 1) (by norm_num)).comp hlog
  have he := Real.tendsto_exp_atBot.comp (hnu.const_mul_atTop_of_neg (by linarith : -(c/2)<0))
  have hp := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<1/12)).comp tendsto_natCast_atTop_atTop
  have hv := saddle_exponential_nat_tendsto_zero 1 1 0 (by norm_num) (by norm_num)
  simpa only [one_mul,neg_mul,zero_mul,add_zero,mul_zero,Function.comp_def] using
    ((he.const_mul 32).add (hp.const_mul 32)).add (hv.const_mul 3)

end
end PaperC.V282.LabelledInformationBudget
