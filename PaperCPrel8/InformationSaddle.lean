import PaperCV282.SaddleParameters
import PaperCPrel8.InformationBudget

/-! # Existence and uniqueness of the actual information-adapted saddle

The crossing is constructed from the continuous parameterized saddle, so no
continuity or root-existence premise is imposed on the application.
-/
namespace PaperC.Prel8.InformationSaddle
open Set
open PaperC.V282.SaddleParameters PaperC.V282.SaddleBranch PaperC.V282.ExponentialIntegral
open PaperC.Prel8.InformationBudget
noncomputable section

/-- Increasing the coefficient from one to two decreases the saddle parameter. -/
theorem parameter_two_le_one {H : ℝ} (hH : max (saddleThreshold 1) (saddleThreshold 2) ≤ H) :
    saddleParameter 2 H ≤ saddleParameter 1 H := by
  have h1 := saddleParameter_spec (by norm_num : (0:ℝ)<1) ((le_max_left _ _).trans hH)
  have h2 := saddleParameter_spec (by norm_num : (0:ℝ)<2) ((le_max_right _ _).trans hH)
  have hHp := (saddleThreshold_pos (by norm_num : (0:ℝ)<1)).trans_le ((le_max_left _ _).trans hH)
  by_contra hn
  have h := strictMonoOn_saddleHeight (by norm_num : (0:ℝ)<2) h1.1 h2.1 (lt_of_not_ge hn)
  have he : saddleHeight 2 (saddleParameter 1 H)=2*H := by
    calc
      _ = 2*saddleHeight 1 (saddleParameter 1 H) := by unfold saddleHeight; ring
      _ = 2*H := by rw [h1.2]
  rw [he,h2.2] at h
  linarith

/-- The hard cutoff is the lower endpoint of the enlarged-cutoff interval. -/
theorem cutoff_one_le_two {H : ℝ} (hH : max (saddleThreshold 1) (saddleThreshold 2) ≤ H) :
    saddleCutoff 1 H ≤ saddleCutoff 2 H := by
  have h1 := saddleCutoff_pos (by norm_num : (0:ℝ)<1) ((le_max_left _ _).trans hH)
  have h2 := saddleCutoff_pos (by norm_num : (0:ℝ)<2) ((le_max_right _ _).trans hH)
  have hHp := (saddleThreshold_pos (by norm_num : (0:ℝ)<1)).trans_le ((le_max_left _ _).trans hH)
  have hu1 : 1 ≤ saddleParameter 1 H := by
    linarith [(saddleParameter_spec (by norm_num : (0:ℝ)<1) ((le_max_left _ _).trans hH)).1,saddleParameterBase_ge_two]
  have hu2 : 1 ≤ saddleParameter 2 H := by
    linarith [(saddleParameter_spec (by norm_num : (0:ℝ)<2) ((le_max_right _ _).trans hH)).1,saddleParameterBase_ge_two]
  have h := strictMonoOn_saddleRatio.monotoneOn hu2 hu1 (parameter_two_le_one hH)
  rw [← div_saddleCutoff_eq_ratio (by norm_num : (0:ℝ)<1) ((le_max_left _ _).trans hH),
    ← div_saddleCutoff_eq_ratio (by norm_num : (0:ℝ)<2) ((le_max_right _ _).trans hH)] at h
  have hh := (div_le_div_iff₀ h2 h1).mp h
  nlinarith

/-- On this exact interval the arithmetic deletion exponent is decreasing. -/
theorem deletion_antitone {H : ℝ} (hH : max (saddleThreshold 1) (saddleThreshold 2) ≤ H) :
    AntitoneOn (fun w => saddleCost (H/w)) (Icc (saddleCutoff 1 H) (saddleCutoff 2 H)) := by
  have hp := saddleCutoff_pos (by norm_num : (0:ℝ)<1) ((le_max_left _ _).trans hH)
  have hHp := (saddleThreshold_pos (by norm_num : (0:ℝ)<1)).trans_le ((le_max_left _ _).trans hH)
  have hdom := saddleCutoff_domain (by norm_num : (0:ℝ)<2) ((le_max_right _ _).trans hH)
  intro x hx y hy hxy
  have hd (z : ℝ) (hz : z ∈ Icc (saddleCutoff 1 H) (saddleCutoff 2 H)) : Real.exp 1 ≤ H/z :=
    hdom.trans (div_le_div_of_nonneg_left hHp.le (hp.trans_le hz.1) hz.2)
  exact strictMonoOn_saddleCost.monotoneOn (hd y hy) (hd x hx)
    (div_le_div_of_nonneg_left hHp.le (hp.trans_le hx.1) hxy)

/-- The root exists and is unique for every admissible information cost. -/
theorem existsUnique_crossing {H I : ℝ}
    (hH : max (saddleThreshold 1) (saddleThreshold 2) ≤ H)
    (hI : 0 ≤ I) (hIV : I ≤ saddleCutoff 1 H) :
    ∃! w : ℝ, w ∈ Icc (saddleCutoff 1 H) (saddleCutoff 2 H) ∧
      2*saddleCost (H/w)=w+I := by
  have hH1 := (le_max_left _ _).trans hH
  have hH2 := (le_max_right _ _).trans hH
  have hHp := (saddleThreshold_pos (by norm_num : (0:ℝ)<1)).trans_le hH1
  let u1 := saddleParameter 1 H
  let u2 := saddleParameter 2 H
  have hu1 : 1 ≤ u1 := by linarith [(saddleParameter_spec (by norm_num : (0:ℝ)<1) hH1).1,saddleParameterBase_ge_two]
  have hu2 : 1 ≤ u2 := by linarith [(saddleParameter_spec (by norm_num : (0:ℝ)<2) hH2).1,saddleParameterBase_ge_two]
  have horder : u2 ≤ u1 := parameter_two_le_one hH
  have hrat (u : ℝ) (hu : 1 ≤ u) : 0 < saddleRatio u := div_pos (Real.exp_pos u) (by linarith)
  let G := fun u => saddleHeight 2 u-I*saddleRatio u
  have hcont : ContinuousOn G (Icc u2 u1) := by
    have hs : Icc u2 u1 ⊆ Ici saddleParameterBase := fun u hu =>
      (saddleParameter_spec (by norm_num : (0:ℝ)<2) hH2).1.trans hu.1
    have hs' : Icc u2 u1 ⊆ Ici 1 := fun u hu => hu2.trans hu.1
    exact ((continuousOn_saddleHeight 2).mono hs).sub
      (continuousOn_const.mul (continuousOn_saddleRatio.mono hs'))
  have hleft : G u2 ≤ H := by
    dsimp [G,u2]
    rw [(saddleParameter_spec (by norm_num : (0:ℝ)<2) hH2).2]
    exact sub_le_self _ (mul_nonneg hI (hrat u2 hu2).le)
  have hright : H ≤ G u1 := by
    have hh := (saddleParameter_spec (by norm_num : (0:ℝ)<1) hH1).2
    have hi := mul_le_mul_of_nonneg_left hIV (hrat u1 hu1).le
    dsimp [G,saddleHeight,saddleCutoff,u1] at *
    nlinarith
  obtain ⟨u,hu,he⟩ := intermediate_value_Icc horder hcont ⟨hleft,hright⟩
  have huone := hu2.trans hu.1
  have hr := hrat u huone
  let w := H/saddleRatio u
  have hw1 : saddleCutoff 1 H ≤ w := by
    have ht := strictMonoOn_saddleRatio.monotoneOn huone hu1 hu.2
    have hh := (div_eq_iff (ne_of_gt (saddleCutoff_pos (by norm_num : (0:ℝ)<1) hH1))).mp
      (div_saddleCutoff_eq_ratio (by norm_num : (0:ℝ)<1) hH1)
    apply (le_div_iff₀ hr).mpr
    have hp := saddleCutoff_pos (by norm_num : (0:ℝ)<1) hH1
    nlinarith
  have hw2 : w ≤ saddleCutoff 2 H := by
    have ht := strictMonoOn_saddleRatio.monotoneOn hu2 huone hu.1
    have hh := (div_eq_iff (ne_of_gt (saddleCutoff_pos (by norm_num : (0:ℝ)<2) hH2))).mp
      (div_saddleCutoff_eq_ratio (by norm_num : (0:ℝ)<2) hH2)
    apply (div_le_iff₀ hr).mpr
    have hp := saddleCutoff_pos (by norm_num : (0:ℝ)<2) hH2
    nlinarith
  have hnu : H/w=saddleRatio u := by dsimp [w]; field_simp
  have hcross : 2*saddleCost (H/w)=w+I := by
    rw [hnu,saddleCost_saddleRatio huone]
    dsimp [G,saddleHeight] at he
    dsimp [w]
    have hh : H/saddleRatio u = 2*saddleCostParam u-I := by
      apply (div_eq_iff (ne_of_gt hr)).mpr
      nlinarith
    linarith
  refine ⟨w,⟨⟨hw1,hw2⟩,hcross⟩,?_⟩
  intro v hv
  exact crossing_unique (deletion_antitone hH) hv.1 ⟨hw1,hw2⟩ hv.2 hcross

end
end PaperC.Prel8.InformationSaddle
