import PaperCPrel8.InformationSaddleLimit
import PaperCV282.SpatialMarkedMovableBudget

/-! # The two distinct field errors at the constructed information saddle -/
namespace PaperC.Prel8.InformationFieldBudget
open Filter Topology
open PaperC.V282.SaddleParameters PaperC.V282.SaddleScales PaperC.V282.SaddleCutoffAdmissibility
open PaperC.V282.SaddlePoissonScales PaperC.V282.MovableMarkedBudget
open PaperC.Prel8.InformationSaddleBudget
noncomputable section

/-- The information margin controls both intensity powers and the polynomial multiplier. -/
theorem exponential_products {I lambda w nu D c c' : ℝ}
    (hI : 0 ≤ I) (hlambda : 1 ≤ lambda) (hnu : 0 ≤ nu) (hc' : 0 < c') (hcc : c' < c)
    (hcross : 2*D=w+I) (hbudget : Real.log lambda ≤ (w-I)/2-c*nu) :
    Real.exp I*lambda*Real.exp (-D+(c-c')*nu) ≤ Real.exp (-c'*nu) ∧
    Real.exp I*lambda^2*Real.exp (-w+(c-c')*nu) ≤ Real.exp (-c'*nu) ∧
    Real.exp I*lambda*(1+lambda) ≤ 2*Real.exp w ∧ Real.exp I*lambda ≤ Real.exp w := by
  have hp : 0 < lambda := by linarith
  have hell := Real.log_nonneg hlambda
  have hmargin := PaperC.Prel8.InformationBudget.two_error_margins hcross hbudget
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

/-- A fixed power absorbs the enlarged saddle, uniformly over all smaller cutoffs. -/
theorem polynomial_absorption (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop,
      Real.exp (saddleCutoff 2 (Real.log N))*(N:ℝ)^(-(1/(3:ℝ))+epsilon/2) ≤
        (N:ℝ)^(-(1/(3:ℝ))+epsilon) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hr := ((tendsto_saddleCutoff_div_height (a:=2) (by norm_num)).comp hlog).eventually (gt_mem_nhds (by linarith : (0:ℝ)<epsilon/2))
  filter_upwards [hr,eventually_ge_atTop (2:ℕ)] with N hR hN
  have hp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hl : 0 < Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have h := (div_lt_iff₀ hl).mp hR
  rw [Real.rpow_def_of_pos hp,Real.rpow_def_of_pos hp,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

/-- Every information-dependent tail is smaller than a fixed secondary-scale exponential. -/
theorem tail_absorption (c' : ℝ) (hc' : 0 < c') :
    ∀ᶠ N : ℕ in atTop, ∀ I : ℝ, 0 ≤ I → I ≤ saddleCutoff 1 (Real.log N) →
      Real.exp (-2*saddleCutoff 2 (Real.log N)) ≤
        Real.exp (-c'*(Real.log N/informationCutoff (Real.log N) I)) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hr := ((tendsto_saddleCutoff_div_nu (a:=1) (by norm_num)).comp hlog).eventually (eventually_ge_atTop c')
  filter_upwards [hr,hlog.eventually (eventually_ge_atTop (max (saddleThreshold 1) (saddleThreshold 2)))] with N hR hH
  intro I hi hiv
  have hs := cutoff_spec hH hi hiv
  have hv := saddleCutoff_pos (by norm_num : (0:ℝ)<1) ((le_max_left _ _).trans hH)
  have hHp := (saddleThreshold_pos (by norm_num : (0:ℝ)<1)).trans_le ((le_max_left _ _).trans hH)
  have hn : 0 < saddleNu 1 (Real.log N) := div_pos hHp hv
  have hh := (le_div_iff₀ hn).mp hR
  have hnu : Real.log N/informationCutoff (Real.log N) I ≤ saddleNu 1 (Real.log N) :=
    div_le_div_of_nonneg_left hHp.le hv hs.1.1
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_left hnu hc'.le
  have hvv := PaperC.Prel8.InformationSaddle.cutoff_one_le_two hH
  nlinarith

end
end PaperC.Prel8.InformationFieldBudget
