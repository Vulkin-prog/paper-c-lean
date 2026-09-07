import PaperCV282.LabelledInformationBudget
import PaperCV282.PrefixScalarConvergence

/-! # Information costs versus the restored microscopic remainder -/
namespace PaperC.V282.MacroTransportInformation

open Filter Topology SaddleParameters SaddleScales SaddleCutoffAdmissibility SaddlePoissonScales
open LabelledInformationBudget

noncomputable section

/-- The microscopic scale log M/loglog M dominates every fixed multiple of either saddle. -/
theorem saddle_le_deep_scale_eventually (a K c : ℝ) (ha : 0<a) (hc : 0<c) :
    ∃ Mzero : ℕ, ∀ M≥Mzero,
      K*saddleCutoff a (Real.log M)≤c*(Real.log M/Real.log (Real.log M)) := by
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim := ((tendsto_log_div_saddleNu ha).comp hlog).const_mul K
  have hh := hlim.eventually (gt_mem_nhds (by simpa using hc))
  apply eventually_atTop.mp
  filter_upwards [hh,hlog.eventually (eventually_gt_atTop (1 : ℝ))] with M hm hM
  have hS : 0<Real.log M/Real.log (Real.log M) :=
    div_pos (by linarith) (Real.log_pos hM)
  have he : K*(Real.log (Real.log M)/saddleNu a (Real.log M))=
      (K*saddleCutoff a (Real.log M))/(Real.log M/Real.log (Real.log M)) := by
    unfold saddleNu
    field_simp
  dsimp only [Function.comp_apply] at hm
  rw [he] at hm
  exact ((div_lt_iff₀ hS).mp hm).le

/-- A real information factor is absorbed without changing or assuming the conditioning event. -/
theorem information_weighted_deep_eventually (a K c : ℝ) (ha : 0<a) (hc : 0<c) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ I : ℝ, I≤K*saddleCutoff a (Real.log M) →
      Real.exp I*Real.exp (-c*(Real.log M/Real.log (Real.log M)))≤
        Real.exp (-(c/2)*(Real.log M/Real.log (Real.log M))) := by
  obtain ⟨Mzero,hMzero⟩ := saddle_le_deep_scale_eventually a K (c/2) ha (by positivity)
  refine ⟨Mzero,?_⟩
  intro M hM I hI
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := hMzero M hM
  linarith

/-- Explicit uniform numerical hard budget for the restored full field. -/
theorem hard_restored_budget_eventually (c d : ℝ) (hc : 0<c) (hd : 0<d) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ I rate : ℝ, 1≤rate →
      labelledLogCost I rate≤saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M) →
      Real.exp I*(37*rate*(1+rate)*
        (Real.exp (-saddleCutoff 1 (Real.log M)+(c/2)*saddleNu 1 (Real.log M))+
          (M : ℝ)^(-(1/(6 : ℝ))))+
        2*Real.exp (-d*(Real.log M/Real.log (Real.log M))))≤
      37*Real.exp (-(c/2)*saddleNu 1 (Real.log M))+37*(M : ℝ)^(-(1/(12 : ℝ)))+
        2*Real.exp (-(d/2)*(Real.log M/Real.log (Real.log M))) := by
  obtain ⟨Np,hp⟩ := hard_polynomial_factor_eventually
  obtain ⟨Nd,hdp⟩ := information_weighted_deep_eventually 1 1 d (by norm_num) hd
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hnul := (tendsto_saddleNu_atTop (a := 1) (by norm_num)).comp hlog
  obtain ⟨Nnu,hnu⟩ := eventually_atTop.mp (hnul.eventually (eventually_ge_atTop (0 : ℝ)))
  refine ⟨max Np (max Nd Nnu),?_⟩
  intro M hM I rate hr hb
  have hnu0 := hnu M (by omega)
  dsimp only [Function.comp_apply] at hnu0
  have hprod := labelled_product_le (by linarith : 0<rate) hb
  have hprodV : Real.exp I*rate*(1+rate)≤Real.exp (saddleCutoff 1 (Real.log M)) :=
    hprod.trans (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hc.le hnu0]))
  have hfirst : Real.exp I*rate*(1+rate)*
      Real.exp (-saddleCutoff 1 (Real.log M)+(c/2)*saddleNu 1 (Real.log M))≤
        Real.exp (-(c/2)*saddleNu 1 (Real.log M)) := by
    apply (mul_le_mul_of_nonneg_right hprod (Real.exp_nonneg _)).trans
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    ring_nf
    exact le_rfl
  have hpoly := (mul_le_mul_of_nonneg_right hprodV
    (Real.rpow_nonneg (by positivity : (0 : ℝ)≤M) (-(1/(6 : ℝ))))).trans (hp M (by omega))
  have hI : I≤1*saddleCutoff 1 (Real.log M) := by
    have hl := Real.log_nonneg hr
    have hl' := Real.log_nonneg (by linarith : (1 : ℝ)≤1+rate)
    unfold labelledLogCost at hb
    nlinarith [mul_nonneg hc.le hnu0]
  have hdeep := hdp M (by omega) I hI
  nlinarith only [hfirst,hpoly,hdeep]

theorem hard_restored_error_tendsto_zero (c d : ℝ) (hc : 0<c) (hd : 0<d) :
    Tendsto (fun M : ℕ =>
      37*Real.exp (-(c/2)*saddleNu 1 (Real.log M))+37*(M : ℝ)^(-(1/(12 : ℝ)))+
        2*Real.exp (-(d/2)*(Real.log M/Real.log (Real.log M)))) atTop (𝓝 0) := by
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hnu := (tendsto_saddleNu_atTop (a := 1) (by norm_num)).comp hlog
  have he := Real.tendsto_exp_atBot.comp (hnu.const_mul_atTop_of_neg (by linarith : -(c/2)<0))
  have hp := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<1/12)).comp tendsto_natCast_atTop_atTop
  have hd' := PrefixScalarConvergence.deep_remainder_tendsto_zero (d/2) (by positivity)
  simpa only [mul_zero,add_zero,Function.comp_def] using ((he.const_mul 37).add (hp.const_mul 37)).add (hd'.const_mul 2)

end
end PaperC.V282.MacroTransportInformation
