import PaperCV282.SaddlePoissonScales
import PaperCV282.SaddleCutoffAdmissibility

/-! # Every logarithmic cost fits every fixed second-order saddle margin -/
namespace PaperC.Prel8.LogarithmicSaddleBudget
open Filter Topology V282.SaddleParameters V282.SaddleScales
open V282.PrimeEulerSaddle V282.SaddleAsymptotics V282.SaddlePoissonScales V282.SaddleCutoffAdmissibility
noncomputable section

theorem logarithmic_budget (A B c : ℝ) :
    ∀ᶠ H : ℝ in atTop, A+B*Real.log H≤saddleCutoff 1 H-c*saddleNu 1 H := by
  have hc : Tendsto (fun H ↦ A/saddleCutoff 1 H) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_saddleCutoff_atTop (by norm_num : (0:ℝ)<1)).inv_tendsto_atTop.const_mul A
  have hl := (tendsto_log_div_saddleCutoff (by norm_num : (0:ℝ)<1)).const_mul B
  have hn := (tendsto_nu_div_saddleCutoff (by norm_num : (0:ℝ)<1)).const_mul c
  have hh := (hc.add hl).add hn
  have he := hh.eventually (gt_mem_nhds (by norm_num : (0:ℝ)+B*0+c*0<1))
  filter_upwards [he,eventually_ge_atTop (saddleThreshold 1)] with H hH hth
  have hv := saddleCutoff_pos (by norm_num : (0:ℝ)<1) hth
  have heq : A/saddleCutoff 1 H+B*(Real.log H/saddleCutoff 1 H)+
      c*(saddleNu 1 H/saddleCutoff 1 H)=
        (A+B*Real.log H+c*saddleNu 1 H)/saddleCutoff 1 H := by ring
  rw [heq] at hH
  have hh := (div_lt_one hv).mp hH
  linarith

end
end PaperC.Prel8.LogarithmicSaddleBudget
