import PaperCPrel8.InformationFieldBudget

/-! # The field error budget at every admissible cutoff, not only the crossing -/
namespace PaperC.Prel8.PrescribedInformationBudget
open Filter Topology V282.SaddleParameters V282.SaddleScales V282.SaddlePoissonScales InformationSaddleBudget
noncomputable section

theorem free_exponential_products {I lambda w nu D c c' : ℝ}
    (hI : 0 ≤ I) (hlambda : 1 ≤ lambda) (hnu : 0 ≤ nu) (hc' : 0 < c') (hcc : c' < c)
    (hbudget : Real.log lambda ≤ min (D-I) ((w-I)/2)-c*nu) :
    Real.exp I*lambda*Real.exp (-D+(c-c')*nu) ≤ Real.exp (-c'*nu) ∧
    Real.exp I*lambda^2*Real.exp (-w+(c-c')*nu) ≤ Real.exp (-c'*nu) ∧
    Real.exp I*lambda*(1+lambda) ≤ 2*Real.exp w ∧ Real.exp I*lambda ≤ Real.exp w := by
  have hp : 0 < lambda := by linarith
  have hell := Real.log_nonneg hlambda
  have hb1 := (min_le_left (D-I) ((w-I)/2))
  have hb2 := (min_le_right (D-I) ((w-I)/2))
  have hmargin : I+Real.log lambda-D≤-c*nu ∧ I+2*Real.log lambda-w≤-2*c*nu :=
    ⟨by linarith,by linarith⟩
  have hlinear : Real.exp I*lambda=Real.exp (I+Real.log lambda) := by rw [Real.exp_add,Real.exp_log hp]
  have hquad : Real.exp I*lambda^2=Real.exp (I+2*Real.log lambda) := by
    rw [show I+2*Real.log lambda=I+Real.log lambda+Real.log lambda by ring,
      Real.exp_add,Real.exp_add,Real.exp_log hp]
    ring
  have hw : I+2*Real.log lambda ≤ w := by nlinarith
  have hq : Real.exp I*lambda^2 ≤ Real.exp w := by rw [hquad]; exact Real.exp_le_exp.mpr hw
  have hl : Real.exp I*lambda ≤ Real.exp w := by rw [hlinear]; apply Real.exp_le_exp.mpr; linarith
  refine ⟨?_,?_,?_,hl⟩
  · rw [hlinear,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [hmargin.1]
  · rw [hquad,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hmargin.2]
  · nlinarith [mul_nonneg (Real.exp_nonneg I) (mul_nonneg (by linarith : 0 ≤ lambda) (sub_nonneg.mpr hlambda))]

theorem free_tail_absorption (c' : ℝ) (hc' : 0 < c') :
    ∀ᶠ N : ℕ in atTop, ∀ w : ℝ, saddleCutoff 1 (Real.log N)≤w →
      Real.exp (-2*saddleCutoff 2 (Real.log N)) ≤
        Real.exp (-c'*(Real.log N/w)) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hr := ((tendsto_saddleCutoff_div_nu (a:=1) (by norm_num)).comp hlog).eventually (eventually_ge_atTop c')
  filter_upwards [hr,hlog.eventually (eventually_ge_atTop (max (saddleThreshold 1) (saddleThreshold 2)))] with N hR hH
  intro w hw
  have hv := saddleCutoff_pos (by norm_num : (0:ℝ)<1) ((le_max_left _ _).trans hH)
  have hHp := (saddleThreshold_pos (by norm_num : (0:ℝ)<1)).trans_le ((le_max_left _ _).trans hH)
  have hn : 0 < saddleNu 1 (Real.log N) := div_pos hHp hv
  have hh := (le_div_iff₀ hn).mp hR
  have hnu : Real.log N/w ≤ saddleNu 1 (Real.log N) :=
    div_le_div_of_nonneg_left hHp.le hv hw
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_left hnu hc'.le
  have hvv := PaperC.Prel8.InformationSaddle.cutoff_one_le_two hH
  nlinarith


end
end PaperC.Prel8.PrescribedInformationBudget
