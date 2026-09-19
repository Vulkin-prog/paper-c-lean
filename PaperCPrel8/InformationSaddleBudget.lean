import PaperCPrel8.InformationSaddle

/-! # Actual optimized information budgets and admissible prime cutoffs -/
namespace PaperC.Prel8.InformationSaddleBudget
open Set
open PaperC.V282.SaddleParameters
open PaperC.Prel8.InformationBudget PaperC.Prel8.InformationSaddle
noncomputable section

/-- The literal crossing, with the hard cutoff as a harmless fallback outside its domain. -/
def informationCutoff (H I : ℝ) : ℝ :=
  if h : max (saddleThreshold 1) (saddleThreshold 2) ≤ H ∧ 0 ≤ I ∧ I ≤ saddleCutoff 1 H then
    Classical.choose (existsUnique_crossing h.1 h.2.1 h.2.2)
  else saddleCutoff 1 H

def informationBudget (H I : ℝ) : ℝ := (informationCutoff H I-I)/2

theorem cutoff_spec {H I : ℝ} (hH : max (saddleThreshold 1) (saddleThreshold 2) ≤ H)
    (hI : 0 ≤ I) (hIV : I ≤ saddleCutoff 1 H) :
    informationCutoff H I ∈ Icc (saddleCutoff 1 H) (saddleCutoff 2 H) ∧
      2*saddleCost (H/informationCutoff H I)=informationCutoff H I+I := by
  rw [informationCutoff,dite_eq_left ⟨hH,hI,hIV⟩]
  exact (Classical.choose_spec (existsUnique_crossing hH hI hIV)).1

theorem cutoff_pos {H I : ℝ} (hH : max (saddleThreshold 1) (saddleThreshold 2) ≤ H)
    (hI : 0 ≤ I) (hIV : I ≤ saddleCutoff 1 H) : 0 < informationCutoff H I :=
  (saddleCutoff_pos (by norm_num : (0:ℝ)<1) ((le_max_left _ _).trans hH)).trans_le (cutoff_spec hH hI hIV).1.1

theorem cutoff_zero {H : ℝ} (hH : max (saddleThreshold 1) (saddleThreshold 2) ≤ H) :
    informationCutoff H 0=saddleCutoff 2 H := by
  have hp := saddleCutoff_pos (by norm_num : (0:ℝ)<1) ((le_max_left _ _).trans hH)
  have he := saddleCutoff_equation (by norm_num : (0:ℝ)<2) ((le_max_right _ _).trans hH)
  have hs := cutoff_spec hH (le_refl 0) hp.le
  apply crossing_unique (deletion_antitone hH) hs.1 ⟨cutoff_one_le_two hH,le_refl _⟩ hs.2
  linarith

theorem cutoff_full_information {H : ℝ} (hH : max (saddleThreshold 1) (saddleThreshold 2) ≤ H) :
    informationCutoff H (saddleCutoff 1 H)=saddleCutoff 1 H := by
  have hp := saddleCutoff_pos (by norm_num : (0:ℝ)<1) ((le_max_left _ _).trans hH)
  have he := saddleCutoff_equation (by norm_num : (0:ℝ)<1) ((le_max_left _ _).trans hH)
  have hs := cutoff_spec hH hp.le (le_refl _)
  apply crossing_unique (deletion_antitone hH) hs.1 ⟨le_refl _,cutoff_one_le_two hH⟩ hs.2
  linarith

/-- This is an attained maximum for the actual deletion exponent. -/
theorem budget_maximum {H I w : ℝ} (hH : max (saddleThreshold 1) (saddleThreshold 2) ≤ H)
    (hI : 0 ≤ I) (hIV : I ≤ saddleCutoff 1 H)
    (hw : w ∈ Icc (saddleCutoff 1 H) (saddleCutoff 2 H)) :
    budget (fun v => saddleCost (H/v)) I w ≤ informationBudget H I := by
  have hs := cutoff_spec hH hI hIV
  simpa only [budget_at_crossing (fun v => saddleCost (H/v)) I (informationCutoff H I) hs.2,informationBudget] using
    crossing_maximizes (deletion_antitone hH) hs.1 hw hs.2

/-- A lower admissible cutoff is preserved, rather than assuming smaller-field measurability. -/
theorem constrained_maximum {H I floor w : ℝ} (hH : max (saddleThreshold 1) (saddleThreshold 2) ≤ H)
    (hI : 0 ≤ I) (hIV : I ≤ saddleCutoff 1 H)
    (hf : floor ∈ Icc (saddleCutoff 1 H) (saddleCutoff 2 H))
    (hw : w ∈ Icc (saddleCutoff 1 H) (saddleCutoff 2 H)) (hfw : floor ≤ w) :
    budget (fun v => saddleCost (H/v)) I w ≤
      budget (fun v => saddleCost (H/v)) I (max floor (informationCutoff H I)) :=
  admissible_cutoff_maximizes (deletion_antitone hH) (cutoff_spec hH hI hIV).1 hf hw hfw
    (cutoff_spec hH hI hIV).2

/-- Both exponential margins follow at the constructed crossing. -/
theorem actual_error_margins {H I ell c : ℝ} (hH : max (saddleThreshold 1) (saddleThreshold 2) ≤ H)
    (hI : 0 ≤ I) (hIV : I ≤ saddleCutoff 1 H)
    (hell : ell ≤ informationBudget H I-c*(H/informationCutoff H I)) :
    I+ell-saddleCost (H/informationCutoff H I) ≤ -c*(H/informationCutoff H I) ∧
    I+2*ell-informationCutoff H I ≤ -2*c*(H/informationCutoff H I) :=
  two_error_margins (cutoff_spec hH hI hIV).2 hell

/-- The optimized log cutoff decreases as the information cost grows. -/
theorem cutoff_strict_antitone {H I J : ℝ} (hH : max (saddleThreshold 1) (saddleThreshold 2) ≤ H)
    (hI : 0 ≤ I) (hIJ : I < J) (hJV : J ≤ saddleCutoff 1 H) :
    informationCutoff H J < informationCutoff H I := by
  have hi := cutoff_spec hH hI (hIJ.le.trans hJV)
  have hj := cutoff_spec hH (hI.trans hIJ.le) hJV
  by_contra hn
  have hd := deletion_antitone hH hi.1 hj.1 (le_of_not_gt hn)
  linarith [hi.2,hj.2]

/-- Positive information loses strictly less than I from the enlarged-cutoff budget. -/
theorem budget_strict_improvement {H I : ℝ} (hH : max (saddleThreshold 1) (saddleThreshold 2) ≤ H)
    (hI : 0 < I) (hIV : I ≤ saddleCutoff 1 H) :
    saddleCutoff 2 H/2-I < informationBudget H I := by
  have hi := cutoff_spec hH hI.le hIV
  have hlt := cutoff_strict_antitone hH (le_refl 0) hI hIV
  rw [cutoff_zero hH] at hlt
  have hp := cutoff_pos hH hI.le hIV
  have hHp := (saddleThreshold_pos (by norm_num : (0:ℝ)<1)).trans_le ((le_max_left _ _).trans hH)
  have hdom := saddleCutoff_domain (by norm_num : (0:ℝ)<2) ((le_max_right _ _).trans hH)
  have hd := div_lt_div_of_pos_left hHp hp hlt
  have hc := strictMonoOn_saddleCost hdom (hdom.trans hd.le) hd
  have he := saddleCutoff_equation (by norm_num : (0:ℝ)<2) ((le_max_right _ _).trans hH)
  unfold informationBudget
  linarith [hi.2]

end
end PaperC.Prel8.InformationSaddleBudget
