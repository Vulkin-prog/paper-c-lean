import PaperCV282.LabelledInformationBudget

/-! # Retaining any strictly smaller margin in the labelled information budget -/
namespace PaperC.V282.QuenchedSaddleBudget

open Filter Topology LabelledInformationBudget SaddleParameters SaddleScales SaddlePoissonScales
open SaddleCutoffAdmissibility GrowingMarkedTruncation SaddleErrorExponent

noncomputable section

/-- The full labelled ledger retains every strictly smaller saddle margin. -/
theorem labelled_budget_bound (c c' : ℝ) (hc' : 0 < c') (hcc : c' < c) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ I rate : ℝ, 1 ≤ rate →
      labelledLogCost I rate ≤ saddleCutoff 1 (Real.log N)-c*saddleNu 1 (Real.log N) →
      Real.exp I*(32*rate*(1+rate)*
        (Real.exp (-saddleCutoff 1 (Real.log N)+(c-c')*saddleNu 1 (Real.log N))+
          (N : ℝ)^(-(1/(6 : ℝ))))+
        (rate/(2 : ℝ)^(growingMarkCutoff N+1))*(2+(N : ℝ)^(-(1/(3 : ℝ))))) ≤
      32*Real.exp (-c'*saddleNu 1 (Real.log N))+
        32*(N : ℝ)^(-(1/(12 : ℝ)))+3*Real.exp (-saddleCutoff 1 (Real.log N)) := by
  have hc : 0 < c := hc'.trans hcc
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
      Real.exp (-saddleCutoff 1 (Real.log N)+(c-c')*saddleNu 1 (Real.log N)) ≤
        Real.exp (-c'*saddleNu 1 (Real.log N)) := by
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


/-- The hard cutoff eventually dominates any fixed multiple of its saddle remainder. -/
theorem cutoff_dominates_nu (c : ℝ) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, c*saddleNu 1 (Real.log N) ≤ saddleCutoff 1 (Real.log N) := by
  have hl : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hr := ((tendsto_nu_div_saddleCutoff (a := 1) (by norm_num)).comp hl).eventually
    (gt_mem_nhds (one_div_pos.mpr hc))
  filter_upwards [hr,hl.eventually (eventually_ge_atTop (saddleThreshold 1))] with N hr hN
  have hv := saddleCutoff_pos (a := 1) (by norm_num) hN
  have hh := (div_lt_iff₀ hv).mp hr
  have he : (1/c)*saddleCutoff 1 (Real.log N)*c=saddleCutoff 1 (Real.log N) := by
    field_simp
  nlinarith [mul_lt_mul_of_pos_right hh hc]

/-- Both the polynomial and the stronger exponential tail fit the same positive margin. -/
theorem remainders_le_margin (c delta : ℝ) (hc : 0<c) (hd : 0<delta) :
    ∀ᶠ N : ℕ in atTop,
      Real.exp (-saddleCutoff 1 (Real.log N)) ≤ Real.exp (-c*saddleNu 1 (Real.log N)) ∧
      (N : ℝ)^(-delta) ≤ Real.exp (-c*saddleNu 1 (Real.log N)) := by
  filter_upwards [cutoff_dominates_nu c hc,
    polynomial_le_saddle_eventually delta 0 hd (by norm_num)] with N hv hp
  have he := Real.exp_le_exp.mpr (by linarith : -saddleCutoff 1 (Real.log N) ≤
    -c*saddleNu 1 (Real.log N))
  have hp' : (N : ℝ)^(-delta) ≤ Real.exp (-saddleCutoff 1 (Real.log N)) := by
    simpa only [zero_mul,add_zero] using hp
  exact ⟨he,hp'.trans he⟩

/-- Uniform decay of the actual numerical ledger with no sacrifice of half the margin. -/
theorem labelled_budget_rate (c c' : ℝ) (hc' : 0<c') (hcc : c'<c) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ rate : ℝ, 1 ≤ rate →
      labelledLogCost 0 rate ≤ saddleCutoff 1 (Real.log N)-c*saddleNu 1 (Real.log N) →
      32*rate*(1+rate)*
        (Real.exp (-saddleCutoff 1 (Real.log N)+(c-c')*saddleNu 1 (Real.log N))+
          (N : ℝ)^(-(1/(6 : ℝ))))+
        (rate/(2 : ℝ)^(growingMarkCutoff N+1))*(2+(N : ℝ)^(-(1/(3 : ℝ)))) ≤
      67*Real.exp (-c'*saddleNu 1 (Real.log N)) := by
  obtain ⟨Nb,hb⟩ := labelled_budget_bound c c' hc' hcc
  obtain ⟨Nt,ht⟩ := eventually_atTop.1 (remainders_le_margin c' (1/12) hc' (by norm_num))
  refine ⟨max Nb Nt,?_⟩
  intro N hN rate hr hbu
  have h := hb N (by omega) 0 rate hr hbu
  simp only [Real.exp_zero,one_mul] at h
  have ht := ht N (by omega)
  linarith

end
end PaperC.V282.QuenchedSaddleBudget
