import PaperCPrel8.PrimeWindowIntensity
import PaperCPrel8.LogarithmicSaddleBudget

/-! # All fixed saddle margins hold along the literal G.9 windows -/
namespace PaperC.Prel8.PrimeWindowBudget
open Filter Topology PrimeWindowScales PrimeWindowErrors PrimeWindowIntensity
open MicroscopicPaperBudget V282.SaddleParameters V282.SaddleScales
noncomputable section

def betaMin : ℝ := 1/(2*Real.log 2)
def betaMax : ℝ := 2/Real.log 2

theorem band_constants : 0<betaMin ∧ betaMin<betaMax := by
  have h : 0<Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · unfold betaMin
    positivity
  · unfold betaMin betaMax
    apply (div_lt_div_iff₀ (by positivity : 0<2*Real.log 2) h).mpr
    nlinarith

theorem log_window_atTop : Tendsto (fun q ↦ Real.log (window q)) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp window_tendsto)

theorem length_band : ∀ᶠ q : ℕ in atTop,
    betaMin*Real.log (window q)≤(q-1+1:ℕ) ∧
      ((q-1+1:ℕ):ℝ)≤betaMax*Real.log (window q) := by
  have hb : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hlo := log_ratio.eventually (lt_mem_nhds (show Real.log 2/2<Real.log 2 by linarith))
  have hhi := log_ratio.eventually (gt_mem_nhds (show Real.log 2<2*Real.log 2 by linarith))
  filter_upwards [hlo,hhi,eventually_ge_atTop 1] with q hlo hhi hq
  have hqr : (0:ℝ)<q := by positivity
  have hl := (lt_div_iff₀ hqr).mp hlo
  have hh := (div_lt_iff₀ hqr).mp hhi
  have he : q-1+1=q := by omega
  rw [he]
  constructor
  · unfold betaMin
    rw [div_mul_eq_mul_div,one_mul]
    apply (div_le_iff₀ (by positivity : 0<2*Real.log 2)).mpr
    convert hh.le using 1 <;> ring
  · unfold betaMax
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hb).mpr
    convert (show (q:ℝ)*Real.log 2≤2*Real.log (window q) by linarith) using 1 <;> ring

/-- Both the scalar and the stronger labelled budgets hold for every fixed margin. -/
theorem labelled_budget (c : ℝ) : ∀ᶠ q : ℕ in atTop,
    1≤siteRate (window q) (q-1) ∧
    Real.log (siteRate (window q) (q-1))+Real.log (1+siteRate (window q) (q-1))≤
      saddleCutoff 1 (Real.log (window q))-c*saddleNu 1 (Real.log (window q)) := by
  have hK : 0<betaMax := band_constants.1.trans band_constants.2
  have hbase := log_window_atTop.eventually
    (LogarithmicSaddleBudget.logarithmic_budget (Real.log 2+2*Real.log betaMax) 2 c)
  have hr := site_rate_atTop.eventually (eventually_ge_atTop (1:ℝ))
  filter_upwards [length_band,hbase,hr,eventually_ge_atTop 1] with q hband hb hr hq
  have hqr : (0:ℝ)<q := by positivity
  have hH : 0<Real.log (window q) := by
    have ht := hband.2
    have he : q-1+1=q := by omega
    rw [he] at ht
    nlinarith
  have hqbound : (q:ℝ)≤betaMax*Real.log (window q) := by
    simpa only [Nat.sub_add_cancel hq] using hband.2
  have hlogq := Real.log_le_log hqr hqbound
  rw [Real.log_mul hK.ne' hH.ne'] at hlogq
  have hs := site_rate_le hq
  have hlogs := Real.log_le_log (by linarith : 0<siteRate (window q) (q-1)) hs
  have h1s := Real.log_le_log (by linarith : 0<1+siteRate (window q) (q-1))
    (show 1+siteRate (window q) (q-1)≤2*(q:ℝ) by
      have : (1:ℝ)≤q := by exact_mod_cast hq
      linarith)
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hqr.ne'] at h1s
  exact ⟨hr,by linarith⟩

theorem scalar_regime (c : ℝ) : ∀ᶠ q : ℕ in atTop,
    betaMin*Real.log (window q)≤(q-1+1:ℕ) ∧
    ((q-1+1:ℕ):ℝ)≤betaMax*Real.log (window q) ∧
    0≤(0:ℝ) ∧ 1≤siteRate (window q) (q-1) ∧
    0+Real.log (siteRate (window q) (q-1))≤
      saddleCutoff 1 (Real.log (window q))-c*saddleNu 1 (Real.log (window q)) := by
  filter_upwards [length_band,labelled_budget c] with q hband hb
  have hlog : 0≤Real.log (1+siteRate (window q) (q-1)) := Real.log_nonneg (by linarith)
  exact ⟨hband.1,hband.2,le_refl _,hb.1,by linarith [hb.2]⟩

end
end PaperC.Prel8.PrimeWindowBudget
