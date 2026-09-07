import PaperCV282.SignedGeometricWeights
import Mathlib.Analysis.SpecificLimits.Basic

/-! # The literal infinite geometric root sum in companion (C.4) -/
namespace PaperC.V282.ClosureGeometricWeights

open ExactMarkedModel SignedGeometricWeights Affine
open scoped BigOperators

noncomputable section

theorem sqrt_exactMarkRate_zero (e : ℕ) :
    Real.sqrt (exactMarkRate 0 e : ℝ) = (1 / Real.sqrt 2) ^ (e + 1) := by
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rw [← pow_mul, mul_comm (e + 1) 2, pow_mul, div_pow, hs]
  simp [exactMarkRate_coe, one_div, inv_pow]

/-- The actual unsigned mark weights have the exact root sum printed in (C.4). -/
theorem hasSum_sqrt_exactMarkRate :
    HasSum (fun e : ℕ => Real.sqrt (exactMarkRate 0 e : ℝ)) (1 + Real.sqrt 2) := by
  have hs0 : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs1 : 1 < Real.sqrt (2 : ℝ) := by nlinarith
  have hr : (1 : ℝ) / Real.sqrt 2 < 1 := (div_lt_one hs0).mpr hs1
  have h := (hasSum_geometric_of_lt_one (by positivity : (0 : ℝ) ≤ 1 / Real.sqrt 2) hr).mul_right
    ((1 : ℝ) / Real.sqrt 2)
  have heq : (1 - (1 : ℝ) / Real.sqrt 2)⁻¹ * (1 / Real.sqrt 2) = 1 + Real.sqrt 2 := by
    have hd : 1 - (1 : ℝ) / Real.sqrt 2 ≠ 0 := ne_of_gt (sub_pos.mpr hr)
    field_simp
    field_simp [ne_of_gt (sub_pos.mpr hs1)]
    nlinarith
  rw [heq] at h
  simpa only [sqrt_exactMarkRate_zero, pow_succ] using h

theorem equation_c_four :
    (∑' e : ℕ, Real.sqrt (1 / (2 : ℝ) ^ (e + 1))) = 1 + Real.sqrt 2 := by
  simpa only [exactMarkRate_coe, zero_add] using hasSum_sqrt_exactMarkRate.tsum_eq

/-- Retaining both signs changes the root sum to the corresponding exact constant. -/
theorem hasSum_sqrt_signedMarkRate :
    HasSum (fun e : ℕ => ∑ _s : F₂, Real.sqrt (signedMarkRate 0 e : ℝ)) (2 + Real.sqrt 2) := by
  have hs0 : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs1 : 1 < Real.sqrt (2 : ℝ) := by nlinarith
  have hr : (1 : ℝ) / Real.sqrt 2 < 1 := (div_lt_one hs0).mpr hs1
  have h := hasSum_geometric_of_lt_one (by positivity : (0 : ℝ) ≤ 1 / Real.sqrt 2) hr
  have heq : (1 - (1 : ℝ) / Real.sqrt 2)⁻¹ = 2 + Real.sqrt 2 := by
    have hd : 1 - (1 : ℝ) / Real.sqrt 2 ≠ 0 := ne_of_gt (sub_pos.mpr hr)
    field_simp
    field_simp [ne_of_gt (sub_pos.mpr hs1)]
    nlinarith
  rw [heq] at h
  convert h using 1
  funext e
  have hroot := sqrt_signedGeometricWeight e
  simp only [signedGeometricWeight] at hroot
  simp only [signedMarkRate_coe, zero_add, hroot, Finset.sum_const, nsmul_eq_mul]
  norm_num
  ring

end
end PaperC.V282.ClosureGeometricWeights
