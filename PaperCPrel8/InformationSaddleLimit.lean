import PaperCPrel8.InformationSaddleScales

/-! # The literal first-order information budget of section 6.2 -/
namespace PaperC.Prel8.InformationSaddleLimit
open Filter Topology
open PaperC.V282.SaddleParameters PaperC.V282.SaddleScales
open PaperC.Prel8.InformationSaddleBudget PaperC.Prel8.InformationSaddleScales
noncomputable section

/-- In hard-cutoff units, the quadratic tends to two without assuming a root asymptotic. -/
theorem hard_normalized_quadratic_tendsto (I : ℝ → ℝ)
    (hI : ∀ᶠ H in atTop, 0 ≤ I H ∧ I H ≤ saddleCutoff 1 H) :
    Tendsto (fun H => (informationCutoff H (I H)/saddleCutoff 1 H)^2+
      (I H/saddleCutoff 1 H)*(informationCutoff H (I H)/saddleCutoff 1 H)) atTop (𝓝 2) := by
  have h := (quadratic_normalized_tendsto I hI).div
    (tendsto_saddleCutoff_square_normalized (by norm_num : (0:ℝ)<1)) (by norm_num)
  have ht : Tendsto (fun H =>
      (((informationCutoff H (I H))^2+I H*informationCutoff H (I H))/(H*Real.log H))/
      ((saddleCutoff 1 H)^2/(H*Real.log H))) atTop (𝓝 2) := by
    convert h using 1 <;> norm_num
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with H hH
  field_simp [ne_of_gt (Real.log_pos hH),show H ≠ 0 by linarith]

/-- Elementary positive-root identity used only after constructing the actual saddle. -/
theorem budget_quadratic_formula {x j : ℝ} (hx : 0 ≤ x) (hj : 0 ≤ j) :
    (x-j)/2=(Real.sqrt (j^2+4*(x^2+j*x))-3*j)/4 := by
  have he : j^2+4*(x^2+j*x)=(2*x+j)^2 := by ring
  rw [he,Real.sqrt_sq (by positivity : 0 ≤ 2*x+j)]
  ring

/-- The displayed information-leading limit: the optimized leading budget at every admissible information profile. -/
theorem information_budget_limit (I : ℝ → ℝ) (theta : ℝ)
    (hI : ∀ᶠ H in atTop, 0 ≤ I H ∧ I H ≤ saddleCutoff 1 H)
    (htheta : Tendsto (fun H => I H/saddleCutoff 1 H) atTop (𝓝 theta)) :
    Tendsto (fun H => informationBudget H (I H)/saddleCutoff 1 H) atTop
      (𝓝 ((Real.sqrt (theta^2+8)-3*theta)/4)) := by
  have hq := hard_normalized_quadratic_tendsto I hI
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp ((htheta.pow 2).add (hq.const_mul 4))
  have h := (hr.sub (htheta.const_mul 3)).div_const 4
  have ht : Tendsto (fun H =>
      (Real.sqrt ((I H/saddleCutoff 1 H)^2+
        4*((informationCutoff H (I H)/saddleCutoff 1 H)^2+
          (I H/saddleCutoff 1 H)*(informationCutoff H (I H)/saddleCutoff 1 H)))-
        3*(I H/saddleCutoff 1 H))/4) atTop (𝓝 ((Real.sqrt (theta^2+8)-3*theta)/4)) := by
    convert h using 1 <;> norm_num
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (max (saddleThreshold 1) (saddleThreshold 2)),hI] with H hH hi
  have hv := saddleCutoff_pos (by norm_num : (0:ℝ)<1) ((le_max_left _ _).trans hH)
  have hw := cutoff_pos hH hi.1 hi.2
  rw [← budget_quadratic_formula (div_nonneg hw.le hv.le) (div_nonneg hi.1 hv.le)]
  unfold informationBudget
  ring

end
end PaperC.Prel8.InformationSaddleLimit
