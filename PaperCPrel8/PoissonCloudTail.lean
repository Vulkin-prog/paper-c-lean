import PaperCV282.ScalarSteinInput
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Exact exponential tail for a Poisson-size cloud -/
namespace PaperC.Prel8.PoissonCloudTail
open V282.ScalarSteinInput Filter Topology
open scoped NNReal
noncomputable section

/-- The exponential generating sum is proved for the actual Poisson masses. -/
theorem hasSum_powers (rate : ℝ≥0) (z : ℝ) :
    HasSum (fun k : ℕ ↦ poissonMass rate k*z^k) (Real.exp ((rate:ℝ)*(z-1))) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp ((rate:ℝ)*z)).mul_left (Real.exp (-(rate:ℝ)))
  convert h using 1
  · funext k
    rw [poissonMass_formula,mul_pow]
    ring
  · rw [← Real.exp_eq_exp_ℝ,← Real.exp_add]
    congr 1
    ring

def tail (rate : ℝ≥0) (K : ℕ) : ℝ := ∑' k : ℕ, if K<k then poissonMass rate k else 0

/-- The genuine upper-tail series is summable. -/
theorem tail_summable (rate : ℝ≥0) (K : ℕ) :
    Summable (fun k : ℕ ↦ if K<k then poissonMass rate k else 0) := by
  apply (hasSum_poissonMass rate).summable.of_nonneg_of_le
  · intro k; split_ifs <;> first | exact poissonMass_nonneg rate k | exact le_rfl
  · intro k; split_ifs <;> first | exact le_rfl | exact poissonMass_nonneg rate k

/-- Markov at base two, with no estimate assumed for the target tail. -/
theorem tail_le (rate : ℝ≥0) (K : ℕ) : tail rate K ≤ Real.exp (rate:ℝ)/(2:ℝ)^K := by
  have hs := (hasSum_powers rate 2).summable.div_const ((2:ℝ)^K)
  have h := (tail_summable rate K).tsum_le_tsum (g := fun k ↦ poissonMass rate k*(2:ℝ)^k/(2:ℝ)^K) (fun k ↦ by
    by_cases hk : K<k
    · rw [ite_eq_left hk]
      apply (le_div_iff₀ (by positivity : (0:ℝ)<2^K)).mpr
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hk.le) (poissonMass_nonneg rate k)
    · rw [ite_eq_right hk]
      exact div_nonneg (mul_nonneg (poissonMass_nonneg rate k) (by positivity)) (by positivity)) hs
  simpa only [tail,tsum_div_const,(hasSum_powers rate 2).tsum_eq,show (2:ℝ)-1=1 by norm_num,mul_one] using h

/-- The displayed e^{-(2 log 2-1) Lambda} bound at every K>=2 Lambda. -/
theorem doubled_tail_le (rate : ℝ≥0) (K : ℕ) (hK : 2*(rate:ℝ)≤K) :
    tail rate K ≤ Real.exp (-((2*Real.log 2-1)*(rate:ℝ))) := by
  apply (tail_le rate K).trans
  rw [← Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2),← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  have hl : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_left hK hl]

/-- The ceiling used in Appendix G incurs no extra constant. -/
theorem ceil_doubled_tail_le (rate : ℝ≥0) :
    tail rate ⌈2*(rate:ℝ)⌉₊ ≤ Real.exp (-((2*Real.log 2-1)*(rate:ℝ))) :=
  doubled_tail_le rate _ (Nat.le_ceil _)

/-- This tail vanishes precisely in the growing-intensity regime used in Appendix F/G. -/
theorem doubled_rate_tendsto {rate : ℕ → ℝ≥0}
    (hr : Tendsto (fun M ↦ (rate M:ℝ)) atTop atTop) :
    Tendsto (fun M ↦ Real.exp (-((2*Real.log 2-1)*(rate M:ℝ)))) atTop (𝓝 0) := by
  have hc : -(2*Real.log 2-1)<0 := by nlinarith [Real.log_two_gt_d9]
  simpa only [Function.comp_def,neg_mul] using Real.tendsto_exp_atBot.comp (hr.const_mul_atTop_of_neg hc)

end
end PaperC.Prel8.PoissonCloudTail
