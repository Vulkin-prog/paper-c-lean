import PaperCV282.PostQuadraticPrimeBounds
import Mathlib.Algebra.Order.Floor.Semifield

/-! # PNT under fixed rescaling, with the exact integer floors

This module derives the fixed-scale prime-count ratios from the already
declared PNT remainder. It introduces no separate PNT assumption.
-/

namespace PaperC.V282.MediumPrimeScaling

open Filter PrimeEulerPNT PrimeEulerAbel ExponentialIntegral
open PostQuadraticPrimeBounds
open scoped Topology

noncomputable section

/-- The normalized PNT remainder vanishes on the real variable as well. -/
theorem real_normalized_remainder_tendsto_zero (hPNT : PrimeNumberTheoremRemainder) :
    Tendsto (fun t : ℝ => primeCountingRemainder t * Real.log t / t) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro epsilon hepsilon
  obtain ⟨A,_hA,hrem⟩ := hPNT (epsilon / 2) (by positivity)
  refine ⟨max A 2,fun t ht => ?_⟩
  have htp : 0 < t := by have := (le_max_right A 2).trans ht; linarith
  have htlog : 0 < Real.log t := Real.log_pos (by have := (le_max_right A 2).trans ht; linarith)
  have hb := hrem t ((le_max_left A 2).trans ht)
  have hbound : |primeCountingRemainder t * Real.log t / t| ≤ epsilon / 2 := by
    rw [abs_div,abs_mul,abs_of_pos htp,abs_of_pos htlog]
    calc
      _ ≤ (epsilon / 2 * t / Real.log t) * Real.log t / t :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hb htlog.le) htp.le
      _ = _ := by field_simp
  simpa only [Real.dist_eq,sub_zero] using hbound.trans_lt (by linarith)

/-- The inclusive real prime count has its standard PNT normalization. -/
theorem primeCountingReal_normalized_tendsto_one (hPNT : PrimeNumberTheoremRemainder) :
    Tendsto (fun t : ℝ => primeCountingReal t * Real.log t / t) atTop (𝓝 1) := by
  have hEi := exponentialIntegral_normalized_tendsto_one.comp Real.tendsto_log_atTop
  have hE : Tendsto (fun t : ℝ => logIntegral t * Real.log t / t) atTop (𝓝 1) := by
    apply hEi.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    simp only [Function.comp_apply,logIntegral,Real.exp_log (by positivity : 0 < t)]
  have hs := (real_normalized_remainder_tendsto_zero hPNT).add hE
  convert hs using 1
  · ext t
    simp only [primeCountingRemainder]
    ring
  · norm_num

/-- Dividing the argument by a positive constant does not change its logarithmic scale. -/
theorem log_div_scale_ratio {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => Real.log t / Real.log (t / c)) atTop (𝓝 1) := by
  have hinv : Tendsto (fun t : ℝ => 1 / Real.log t) atTop (𝓝 0) := by
    simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hsmall : Tendsto (fun t : ℝ => Real.log c / Real.log t) atTop (𝓝 0) := by
    simpa only [mul_one_div,mul_zero] using hinv.const_mul (Real.log c)
  have hden : Tendsto (fun t : ℝ => 1 - Real.log c / Real.log t) atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hsmall
  have hr : Tendsto (fun t : ℝ => 1 / (1 - Real.log c / Real.log t)) atTop (𝓝 1) := by
    simpa only [div_one,Pi.div_def] using tendsto_const_nhds.div hden (by norm_num : (1 : ℝ) ≠ 0)
  apply hr.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ),eventually_gt_atTop c] with t ht htc
  have htlog : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hscale : Real.log (t / c) ≠ 0 := (Real.log_pos ((one_lt_div hc).mpr htc)).ne'
  rw [Real.log_div (by positivity) hc.ne'] at hscale ⊢
  field_simp

/-- Exact real fixed-scale ratio, available for every positive scale. -/
theorem primeCountingReal_div_ratio (hPNT : PrimeNumberTheoremRemainder)
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => primeCountingReal (t / c) / primeCountingReal t)
      atTop (𝓝 (1 / c)) := by
  have hs := (primeCountingReal_normalized_tendsto_one hPNT).comp
    (tendsto_id.atTop_div_const hc)
  have hb := primeCountingReal_normalized_tendsto_one hPNT
  have hr := ((hs.div hb (by norm_num : (1 : ℝ) ≠ 0)).mul (log_div_scale_ratio hc)).div_const c
  apply (show Tendsto
      (fun t : ℝ => ((primeCountingReal (t / c) * Real.log (t / c) / (t / c)) /
        (primeCountingReal t * Real.log t / t)) * (Real.log t / Real.log (t / c)) / c)
      atTop (𝓝 (1 / c)) by simpa only [Function.comp_def,id_eq,Pi.div_apply,div_one,mul_one] using hr).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ),eventually_gt_atTop c] with t ht htc
  have htp : t ≠ 0 := (show 0 < t by linarith).ne'
  have htlog : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hslog : Real.log (t / c) ≠ 0 := (Real.log_pos ((one_lt_div hc).mpr htc)).ne'
  field_simp

/-- The source's integer division uses exactly the floor convention of primeCountingReal. -/
theorem prime_count_div_ratio (hPNT : PrimeNumberTheoremRemainder) {j : ℕ} (hj : 0 < j) :
    Tendsto (fun B : ℕ => (PrimesUpTo.count (B / j) : ℝ) / PrimesUpTo.count B)
      atTop (𝓝 (1 / (j : ℝ))) := by
  have h := (primeCountingReal_div_ratio hPNT (by exact_mod_cast hj : (0 : ℝ) < j)).comp
    tendsto_natCast_atTop_atTop
  simpa only [Function.comp_def,primeCountingReal,Nat.floor_div_eq_div,Nat.floor_natCast,
    prime_count_eq_nat] using h

end
end PaperC.V282.MediumPrimeScaling
