import PaperCV282.BulkMicroscopicRecord
import PaperCV282.BulkPopulation

/-! # The established bulk comparison along arbitrary prefix subsequences -/
namespace PaperC.V282.RarePrefixSubsequence

open Filter Topology MeasureTheory BulkMarkedRates BulkMarkedComparison BulkMarkedConvergence
open BulkStartFieldComparison BulkMicroscopicRecord AllStartSoftPoisson PrimeEulerPNT ProcessAGGInput

noncomputable section
open scoped NNReal

/-- A uniform saddle bound can be sampled at arbitrary diverging prefix sizes. -/
theorem relative_distance_along_subsequence
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop) (D : ℕ → ℝ)
    (hD : ∀ n, 0 ≤ D n) (epsilon eta : ℝ) (hepsilon : epsilon < 1/3)
    (hbound : ∀ᶠ n in atTop, D n ≤ 67*bulkRelativeRate (sizes n) (lengths n) epsilon eta) :
    Tendsto (fun n => D n/(fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun n => div_nonneg (hD n) (by positivity)) ?_
    ((relative_error_tendsto_zero epsilon eta hepsilon).comp hsizes)
  filter_upwards [hbound, hsizes.eventually (eventually_ge_atTop 1)] with n hb hn
  have hp : (0 : ℝ) < (fullRate (sizes n) (lengths n) : ℝ) := by
    change 0 < (sizes n : ℝ)/2^(lengths n)
    positivity
  apply (div_le_iff₀ hp).mpr
  unfold bulkRelativeRate at hb
  dsimp only [Function.comp_def]
  nlinarith [hb]

theorem start_relative_along_subsequence
    (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop)
    (beta delta : ℝ) (hbeta : 0 < beta) (hdelta : 0 < delta)
    (hupper : ∀ᶠ n in atTop, (lengths n : ℝ) ≤ beta*Real.log (sizes n))
    (hrare : Tendsto (fun n => (fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => bulkStartConditionalDistance (sizes n) (lengths n) delta /
      (fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0) := by
  obtain ⟨Mzero,h⟩ := bulk_start_rate_eventually hAGG hPNT (1/2) (beta+1) delta (1/6) 1
    (by norm_num) (by linarith) hdelta (by norm_num) (by norm_num)
  apply relative_distance_along_subsequence sizes lengths hsizes _
    (fun _ => CountablePrimeEventTransfer.meanAtomDistance_nonneg _ _ _ _) (1/6) 1 (by norm_num)
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hsizes)
  filter_upwards [hupper, hrare.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1)),
    hlog.eventually (eventually_ge_atTop (1 : ℝ)), hsizes.eventually (eventually_ge_atTop (max 1 Mzero))]
    with n hu hr hl hn
  have hb := rare_window_band (by omega) hl hbeta hu hr.le
  exact h (sizes n) (by omega) (lengths n) hb.1 hb.2 hr.le

theorem signed_relative_along_subsequence
    (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop)
    (beta delta : ℝ) (hbeta : 0 < beta) (hdelta : 0 < delta)
    (hupper : ∀ᶠ n in atTop, (lengths n : ℝ) ≤ beta*Real.log (sizes n))
    (hrare : Tendsto (fun n => (fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => bulkConditionalDistance (sizes n) (lengths n) delta /
      (fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0) := by
  obtain ⟨Mzero,h⟩ := theorem_seven_seven hAGG hPNT (1/2) (beta+1) delta (1/6) 1
    (by norm_num) (by linarith) hdelta (by norm_num) (by norm_num)
  apply relative_distance_along_subsequence sizes lengths hsizes _
    (fun _ => spatialConditionalDistance_nonneg _ _ _ _) (1/6) 1 (by norm_num)
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hsizes)
  filter_upwards [hupper, hrare.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1)),
    hlog.eventually (eventually_ge_atTop (1 : ℝ)), hsizes.eventually (eventually_ge_atTop (max 1 Mzero))]
    with n hu hr hl hn
  have hb := rare_window_band (by omega) hl hbeta hu hr.le
  exact h (sizes n) (by omega) (lengths n) hb.1 hb.2 hr.le

/-- The entire true microscopic record remains asymptotically independent on every subsequence. -/
theorem microscopic_joint_relative_along_subsequence
    (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop)
    (beta delta : ℝ) (hbeta : 0 < beta) (hdelta : 0 < delta)
    (hupper : ∀ᶠ n in atTop, (lengths n : ℝ) ≤ beta*Real.log (sizes n))
    (hrare : Tendsto (fun n => (fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => microscopicJointDistance (sizes n) (lengths n) delta /
      (fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ => div_nonneg (microscopicJointDistance_nonneg _ _ _) (by positivity)) ?_
    (start_relative_along_subsequence hAGG hPNT sizes lengths hsizes beta delta hbeta hdelta hupper hrare)
  obtain ⟨Mzero,hzero⟩ := microscopic_cylinder_le_hardCutoff_eventually (beta+1) (by linarith)
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hsizes)
  filter_upwards [hupper,hlog.eventually (eventually_ge_atTop (1 : ℝ)),
    hsizes.eventually (eventually_ge_atTop Mzero)] with n hu hl hn
  dsimp only [Function.comp_def] at hl
  have hc := hzero (sizes n) hn (lengths n) (by nlinarith)
  exact div_le_div_of_nonneg_right (microscopic_joint_le_start_conditional delta hc) (by positivity)

end
end PaperC.V282.RarePrefixSubsequence
