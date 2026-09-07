import PaperCV282.BulkStartFieldComparison
import PaperCV282.SaddleRateConvergence

/-! # Relative convergence in the printed rare bulk regime -/
namespace PaperC.V282.BulkMarkedConvergence

open Filter Topology BulkMarkedRates BulkMarkedComparison BulkStartFieldComparison
open AllStartSoftPoisson HardPoissonRates PrimeEulerPNT ProcessAGGInput
open SaddleRateConvergence SaddlePoissonScales SaddleParameters SaddleScales

noncomputable section

/-- The rare intensity itself supplies the lower logarithmic band. -/
theorem rare_window_band {M L : ℕ} (hM : 0<M) (hlog : 1≤Real.log M)
    {beta : ℝ} (_hbeta : 0<beta) (hL : (L : ℝ)≤beta*Real.log M)
    (hrate : (fullRate M L : ℝ)≤1) :
    (1/2 : ℝ)*Real.log M≤(L+1 : ℝ) ∧ (L+1 : ℝ)≤(beta+1)*Real.log M := by
  have hp : (0 : ℝ)<M := by exact_mod_cast hM
  have hm : (M : ℝ)≤(2 : ℝ)^L := (div_le_one (by positivity)).mp hrate
  have hh := Real.log_le_log hp hm
  rw [Real.log_pow] at hh
  have htwo : Real.log 2≤1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)]
  have hl0 : (0 : ℝ)≤L := by positivity
  constructor <;> nlinarith

/-- All asymptotic errors are numerical consequences of the actual saddle. -/
theorem relative_error_tendsto_zero (epsilon eta : ℝ) (hepsilon : epsilon<1/3) :
    Tendsto (fun M : ℕ => 67*(Real.exp (-saddleCutoff 1 (Real.log M)+eta*saddleNu 1 (Real.log M))+
      (M : ℝ)^(-(1/(3 : ℝ))+epsilon))) atTop (𝓝 0) := by
  have he := saddle_exponential_nat_tendsto_zero 1 1 eta (by norm_num) (by norm_num)
  simpa only [neg_mul,one_mul,add_zero,mul_zero] using
    (he.add (polynomial_error_nat_tendsto_zero epsilon hepsilon)).const_mul 67

/-- A true distance with the established relative bound is o(lambda), even as lambda tends to zero. -/
theorem relative_distance_tendsto_zero (L : ℕ→ℕ) (D : ℕ→ℝ)
    (hD : ∀M,0≤D M) (epsilon eta : ℝ) (hepsilon : epsilon<1/3)
    (hbound : ∀ᶠ M in atTop, D M≤67*bulkRelativeRate M (L M) epsilon eta) :
    Tendsto (fun M => D M/(fullRate M (L M) : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun M => div_nonneg (hD M) (by positivity)) ?_
    (relative_error_tendsto_zero epsilon eta hepsilon)
  filter_upwards [hbound,eventually_ge_atTop (1 : ℕ)] with M hb hM
  have hp : (0 : ℝ)<(fullRate M (L M) : ℝ) := by
    change 0<(M : ℝ)/2^(L M)
    positivity
  apply (div_le_iff₀ hp).mpr
  unfold bulkRelativeRate at hb
  nlinarith

/-- Uniform full marked comparison in exactly the rare regime of Theorem 7.7. -/
theorem signed_relative_convergence (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (L : ℕ→ℕ) (beta delta : ℝ) (hbeta : 0<beta) (hdelta : 0<delta)
    (hupper : ∀ᶠ M in atTop,(L M : ℝ)≤beta*Real.log M)
    (hrare : Tendsto (fun M => (fullRate M (L M) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun M => bulkConditionalDistance M (L M) delta/(fullRate M (L M) : ℝ)) atTop (𝓝 0) := by
  obtain ⟨Mzero,h⟩ := theorem_seven_seven hAGG hPNT (1/2) (beta+1) delta (1/6) 1
    (by norm_num) (by linarith) hdelta (by norm_num) (by norm_num)
  apply relative_distance_tendsto_zero L _ (fun M => spatialConditionalDistance_nonneg _ _ _ _)
    (1/6) 1 (by norm_num)
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hupper,hrare.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1)),
    hlog.eventually (eventually_ge_atTop (1 : ℝ)),eventually_ge_atTop (max 1 Mzero)]
    with M hu hr hl hM
  have hb := rare_window_band (by omega) hl hbeta hu hr.le
  exact h M (by omega) (L M) hb.1 hb.2 hr.le

/-- Equation (7.16): the actual unmarked start field has relative conditional mean error o(lambda). -/
theorem equation_seven_sixteen (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (L : ℕ→ℕ) (beta delta : ℝ) (hbeta : 0<beta) (hdelta : 0<delta)
    (hupper : ∀ᶠ M in atTop,(L M : ℝ)≤beta*Real.log M)
    (hrare : Tendsto (fun M => (fullRate M (L M) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun M => bulkStartConditionalDistance M (L M) delta/(fullRate M (L M) : ℝ)) atTop (𝓝 0) := by
  obtain ⟨Mzero,h⟩ := bulk_start_rate_eventually hAGG hPNT (1/2) (beta+1) delta (1/6) 1
    (by norm_num) (by linarith) hdelta (by norm_num) (by norm_num)
  apply relative_distance_tendsto_zero L _ (fun M => CountablePrimeEventTransfer.meanAtomDistance_nonneg _ _ _ _)
    (1/6) 1 (by norm_num)
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hupper,hrare.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1)),
    hlog.eventually (eventually_ge_atTop (1 : ℝ)),eventually_ge_atTop (max 1 Mzero)]
    with M hu hr hl hM
  have hb := rare_window_band (by omega) hl hbeta hu hr.le
  exact h M (by omega) (L M) hb.1 hb.2 hr.le

end
end PaperC.V282.BulkMarkedConvergence
