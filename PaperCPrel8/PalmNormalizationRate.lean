import PaperCPrel8.ArithmeticPalmNormalization
import PaperCPrel8.RegularTargetCompletion

/-! # Vanishing normalized-void penalty at the literal paper budget -/
namespace PaperC.Prel8.PalmNormalizationRate
open Finset Filter Topology
open ArithmeticPalmNormalization MicroscopicPaperBudget MicroscopicDiscardRates RegularCloudCutoff
open V282.SaddleScales V282.SaddleParameters V282.AggregateCutoffRemainder
noncomputable section

theorem baseRate_le_half {L : ℕ} (hL : 1≤L) : baseRate L≤1/2 := by
  unfold baseRate
  apply one_div_le_one_div_of_le (by norm_num)
  simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hL

/-- The normalization penalty is at most 5 Lambda p, uniformly over retained masks. -/
theorem penalty_le {L n : ℕ} (sites : Finset ℕ) (hL : 1≤L) (hg : sites.card≤n)
    (hr : 1≤(n:ℝ)*baseRate L) :
    penalty sites L ⌈2*((n:ℝ)*baseRate L)⌉₊≤5*((n:ℝ)*baseRate L)*baseRate L := by
  have hp := baseRate_bounds hL
  have hp2 := baseRate_le_half hL
  have hgR : (sites.card:ℝ)≤n := by exact_mod_cast hg
  have hK := ceil_twice_le _ hr
  have hkp := mul_le_mul_of_nonneg_right hK.2 hp.1.le
  have hgterm : (sites.card:ℝ)*(baseRate L)^2/(1-baseRate L)≤2*(sites.card:ℝ)*(baseRate L)^2 := by
    apply (div_le_iff₀ (sub_pos.mpr hp.2)).mpr
    have hh := mul_nonneg (show 0≤(sites.card:ℝ)*(baseRate L)^2 by positivity)
      (show 0≤1-2*baseRate L by linarith)
    nlinarith
  have hgprod := mul_le_mul_of_nonneg_right hgR (sq_nonneg (baseRate L))
  unfold penalty
  nlinarith

/-- Exact numerical domination at the source geometry and information budget. -/
theorem penalty_saddle_bound {M L : ℕ} (sites : Finset ℕ) (hM : 0<M) (hL : 1≤L)
    (hshort : 2*L≤M) (hg : sites.card≤M-L) (hr : 1≤siteRate M L)
    {V : ℝ} (hrV : siteRate M L≤Real.exp V) :
    penalty sites L ⌈2*siteRate M L⌉₊≤10*Real.exp (2*V)/(M:ℝ) := by
  have hrate : siteRate M L=((M-L:ℕ):ℝ)*baseRate L := by unfold siteRate baseRate; ring
  have hp := (baseRate_bounds hL).1
  have hm : 0<(M:ℝ) := by exact_mod_cast hM
  have hn : (M:ℝ)≤2*((M-L:ℕ):ℝ) := by exact_mod_cast (show M≤2*(M-L) by omega)
  have hmp : (M:ℝ)*baseRate L≤2*siteRate M L := by rw [hrate]; nlinarith
  have h0 : 0≤siteRate M L := by linarith
  have hnum := penalty_le sites hL hg (by rwa [← hrate])
  rw [← hrate] at hnum
  have he : (Real.exp V)^2=Real.exp (2*V) := by rw [sq,← Real.exp_add]; congr 1; ring
  have hs : (siteRate M L)^2≤Real.exp (2*V) := by rw [← he]; nlinarith [Real.exp_pos V]
  apply hnum.trans
  apply (le_div_iff₀ hm).mpr
  have hh := mul_le_mul_of_nonneg_left hmp (show 0≤5*siteRate M L by positivity)
  nlinarith

/-- One M threshold works for every admissible length, event and retained mask. -/
theorem penalty_eventually (beta c : ℝ) (hbeta : 0<beta) (hc : 0<c) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ, ∀ I : ℝ, ∀ sites : Finset ℕ,
      1≤L → (L+1:ℝ)≤beta*Real.log M → 0≤I → sites.card≤M-L → 1≤siteRate M L →
      I+Real.log (siteRate M L)≤saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M) →
      penalty sites L ⌈2*siteRate M L⌉₊≤(M:ℝ)^(-(1/(2:ℝ))) := by
  obtain ⟨Ml,hl⟩ := logarithmic_length_quarter beta hbeta
  obtain ⟨Mp,hp⟩ := eventually_atTop.mp
    (constant_exp_saddle_le_power_eventually 10 2 (1/2) (by norm_num) (by norm_num))
  obtain ⟨Mn,hn⟩ := nu_le_saddle_eventually
  refine ⟨max 1 (max Ml (max Mp Mn)),?_⟩
  intro M hM L I sites hL hhi hI hg hr hb
  have hm : 0<(M:ℝ) := by exact_mod_cast (show 0<M by omega)
  have hn0 := (hn M (by omega)).1
  have hrV : siteRate M L≤Real.exp (saddleCutoff 1 (Real.log M)) := by
    rw [← Real.exp_log (by linarith : 0<siteRate M L)]
    apply Real.exp_le_exp.mpr
    nlinarith
  apply (penalty_saddle_bound sites (by omega) hL
    (by have := hl M (by omega) L hhi; omega) hg hr hrV).trans
  calc
    _ ≤ (M:ℝ)^(1/(2:ℝ))/M := div_le_div_of_nonneg_right (hp M (by omega)) hm.le
    _ = (M:ℝ)^(1/(2:ℝ))/(M:ℝ)^(1:ℝ) := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_sub hm]; norm_num

end
end PaperC.Prel8.PalmNormalizationRate
