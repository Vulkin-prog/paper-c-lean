import PaperCV282.GrowingMarkedTruncation
import PaperCV282.SaddleErrorExponent

/-!
# The one-factor information budget and its uniform small remainders

The information and intensity are genuine numerical parameters, not assumed
comparison errors. The enlarged marked support costs exp(O(V)), which is
absorbed only after retaining its explicit dependence on the cutoff.
-/
namespace PaperC.V282.AggregateInformationBudget

open Filter Topology SaddleParameters SaddleScales SaddlePoissonScales
open SaddleCutoffAdmissibility GrowingMarkedTruncation SaddleMarkTruncation

noncomputable section

def aggregateLogCost (I rate : ℝ) : ℝ := I+Real.log rate

theorem exp_aggregateLogCost (I rate : ℝ) (hr : 0<rate) :
    Real.exp (aggregateLogCost I rate)=Real.exp I*rate := by
  rw [aggregateLogCost,Real.exp_add,Real.exp_log hr]

theorem aggregate_weight_le {I rate V c nu : ℝ} (hr : 0<rate)
    (hbudget : aggregateLogCost I rate≤V-c*nu) :
    Real.exp I*rate≤Real.exp (V-c*nu) := by
  rw [← exp_aggregateLogCost I rate hr]
  exact Real.exp_le_exp.mpr hbudget

theorem aggregate_parameters_le {I rate V c nu : ℝ} (hI : 0≤I) (hr : 1≤rate)
    (hc : 0≤c) (hnu : 0≤nu) (hbudget : aggregateLogCost I rate≤V-c*nu) :
    I≤V ∧ Real.log rate≤V ∧ Real.exp I*rate≤Real.exp V := by
  have hlog : 0≤Real.log rate := Real.log_nonneg hr
  have hb : I+Real.log rate≤V := by
    unfold aggregateLogCost at hbudget
    nlinarith [mul_nonneg hc hnu]
  refine ⟨by linarith,by linarith,?_⟩
  rw [← exp_aggregateLogCost I rate (by linarith)]
  exact Real.exp_le_exp.mpr hb

/-- Every fixed exponential cost at the saddle remains subpolynomial in N. -/
theorem exp_saddle_le_power_eventually (K epsilon : ℝ) (hepsilon : 0<epsilon) :
    ∀ᶠ N : ℕ in atTop,
      Real.exp (K*saddleCutoff 1 (Real.log N))≤(N : ℝ)^epsilon := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio := ((tendsto_saddleCutoff_div_height (a := 1) (by norm_num)).comp hlog).const_mul K
  have hsmall := hratio.eventually (gt_mem_nhds (by simpa using hepsilon))
  filter_upwards [hsmall,eventually_ge_atTop (2 : ℕ)] with N hs hN
  have hlogpos : 0<Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hp : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  rw [Real.rpow_def_of_pos hp]
  apply Real.exp_le_exp.mpr
  have h := (div_lt_iff₀ hlogpos).mp (show (K*saddleCutoff 1 (Real.log N))/Real.log N<epsilon by
    simpa only [mul_div_assoc,Function.comp_apply] using hs)
  linarith

/-- Logarithmic Stein factors fit into any positive nu margin. -/
theorem linear_saddle_le_exp_nu_eventually (K eta : ℝ) (hK : 0<K) (heta : 0<eta) :
    ∀ᶠ N : ℕ in atTop,
      K*(1+saddleCutoff 1 (Real.log N))≤Real.exp (eta*saddleNu 1 (Real.log N)) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun H : ℝ => (Real.log (2*K)+Real.log H)/saddleNu 1 H)
      atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := Real.log (2*K))).div_atTop
      (tendsto_saddleNu_atTop (a := 1) (by norm_num))
    simpa only [add_div,zero_add] using h.add (tendsto_log_div_saddleNu (a := 1) (by norm_num))
  have hsmall := (hlim.comp hlog).eventually (gt_mem_nhds heta)
  have hvsmall := ((tendsto_saddleCutoff_div_height (a := 1) (by norm_num)).comp hlog).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ)<1))
  filter_upwards [hsmall,hvsmall,hlog.eventually (eventually_ge_atTop (max 1 (saddleThreshold 1)))]
    with N hs hv hN
  have hn : 0<Real.log (N : ℝ) := lt_of_lt_of_le (by norm_num) (le_trans (le_max_left _ _) hN)
  have hV : 0<saddleCutoff 1 (Real.log N) := saddleCutoff_pos (by norm_num) (le_trans (le_max_right _ _) hN)
  have hnu : 0<saddleNu 1 (Real.log N) := div_pos hn hV
  have hvle : saddleCutoff 1 (Real.log N)≤Real.log N := by
    have hh := (div_lt_iff₀ hn).mp hv
    simpa only [one_mul] using hh.le
  have hc : Real.log (2*K)+Real.log (Real.log N)≤eta*saddleNu 1 (Real.log N) :=
    ((div_lt_iff₀ hnu).mp hs).le
  calc
    _ ≤ (2*K)*Real.log N := by nlinarith [le_trans (le_max_left _ _) hN]
    _ = Real.exp (Real.log (2*K)+Real.log (Real.log N)) := by
      rw [Real.exp_add,Real.exp_log (by positivity),Real.exp_log hn]
    _ ≤ _ := Real.exp_le_exp.mpr hc

/-- The exact one-factor budget absorbs both the Stein logarithm and every
smaller positive exponential margin. -/
theorem aggregate_leading_bound_eventually (K c c' : ℝ)
    (hK : 0<K) (hc : 0≤c) (hcc : c'<c) :
    ∀ᶠ N : ℕ in atTop, ∀ I rate : ℝ, 0≤I → 1≤rate →
      aggregateLogCost I rate≤saddleCutoff 1 (Real.log N)-c*saddleNu 1 (Real.log N) →
      K*Real.exp I*rate*(1+Real.log (2*rate))*
        Real.exp (-saddleCutoff 1 (Real.log N)+((c-c')/2)*saddleNu 1 (Real.log N))≤
          Real.exp (-c'*saddleNu 1 (Real.log N)) := by
  have hlogtwo : 0<Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hpref := linear_saddle_le_exp_nu_eventually (K*(2+Real.log 2)) ((c-c')/2)
    (by positivity) (by linarith)
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hpref,hlog.eventually (eventually_ge_atTop (saddleThreshold 1))] with N hp hN
  intro I rate hI hr hb
  have hV := (saddleCutoff_pos (a := 1) (by norm_num) hN).le
  have hnu : 0≤saddleNu 1 (Real.log N) := by
    unfold saddleNu
    exact div_nonneg (((saddleThreshold_pos (a := 1) (by norm_num)).trans_le hN).le) hV
  have hprod := aggregate_weight_le (by linarith : 0<rate) hb
  have hlograte : Real.log rate≤saddleCutoff 1 (Real.log N)-c*saddleNu 1 (Real.log N) := by
    unfold aggregateLogCost at hb
    linarith
  have hlogr : 0≤Real.log rate := Real.log_nonneg hr
  have hcnu : 0≤c*saddleNu 1 (Real.log N) := mul_nonneg hc hnu
  have hlogle : Real.log rate≤saddleCutoff 1 (Real.log N) := by linarith
  have hfac : K*(1+Real.log (2*rate))≤Real.exp (((c-c')/2)*saddleNu 1 (Real.log N)) := by
    apply le_trans _ hp
    rw [Real.log_mul (by norm_num) (by linarith : rate≠0)]
    nlinarith [mul_nonneg hV hlogtwo.le]
  have hfac0 : 0≤K*(1+Real.log (2*rate)) := by
    have : 0≤Real.log (2*rate) := Real.log_nonneg (by linarith)
    positivity
  have h := mul_le_mul hprod hfac hfac0 (Real.exp_nonneg _)
  have h' := mul_le_mul_of_nonneg_right h (Real.exp_nonneg
    (-saddleCutoff 1 (Real.log N)+((c-c')/2)*saddleNu 1 (Real.log N)))
  calc
    _ ≤ (Real.exp (saddleCutoff 1 (Real.log N)-c*saddleNu 1 (Real.log N))*
      Real.exp (((c-c')/2)*saddleNu 1 (Real.log N)))*
      Real.exp (-saddleCutoff 1 (Real.log N)+((c-c')/2)*saddleNu 1 (Real.log N)) := by nlinarith
    _ = _ := by rw [← Real.exp_add,← Real.exp_add];congr 1;ring

end
end PaperC.V282.AggregateInformationBudget
