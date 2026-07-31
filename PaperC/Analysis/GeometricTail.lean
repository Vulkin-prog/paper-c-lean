import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The geometric tail used in the Runge estimate

This file isolates the elementary infinite-series estimate behind equation
(3.3) of Paper C.  The analytic coefficient estimate is deliberately kept
separate; here we only prove the exact shifted geometric sum and its bound
when the ratio is at most `1/2`.
-/

namespace PaperC
namespace GeometricTail

open scoped BigOperators Topology

/-- Exact sum of a shifted nonnegative geometric series. -/
theorem tsum_pow_natAdd_eq
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (k : ℕ) :
    (∑' n : ℕ, x ^ (n + k)) = x ^ k * (1 - x)⁻¹ := by
  calc
    (∑' n : ℕ, x ^ (n + k)) =
        ∑' n : ℕ, x ^ k * x ^ n := by
      apply tsum_congr
      intro n
      simp [pow_add, mul_comm]
    _ = x ^ k * ∑' n : ℕ, x ^ n := by
      rw [tsum_mul_left]
    _ = x ^ k * (1 - x)⁻¹ := by
      rw [tsum_geometric_of_lt_one hx0 hx1]

/-- A geometric tail with ratio at most one half is at most twice its first term. -/
theorem tsum_pow_natAdd_le_two_mul
    {x : ℝ} (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) (k : ℕ) :
    (∑' n : ℕ, x ^ (n + k)) ≤ 2 * x ^ k := by
  have hx1 : x < 1 := hxhalf.trans_lt (by norm_num)
  rw [tsum_pow_natAdd_eq hx0 hx1]
  have hhalf : (1 / 2 : ℝ) ≤ 1 - x := by
    linarith
  have hinverse : (1 - x)⁻¹ ≤ (2 : ℝ) := by
    have h :=
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hhalf
    norm_num at h ⊢
    exact h
  calc
    x ^ k * (1 - x)⁻¹ ≤ x ^ k * 2 :=
      mul_le_mul_of_nonneg_left hinverse (pow_nonneg hx0 k)
    _ = 2 * x ^ k := by ring

/-- A convenient division criterion for producing a ratio at most one half. -/
theorem div_le_half
    {A U : ℝ} (hU0 : 0 < U) (hAU : 2 * A ≤ U) :
    A / U ≤ 1 / 2 := by
  rw [div_le_iff₀ hU0]
  nlinarith

/--
The numerical specialization appearing in (3.3): if `U ≥ 4R`, then the
geometric tail with ratio `2R/U` is bounded by twice its first term.
-/
theorem runge_ratio_tail
    {R U : ℕ} (hR : 1 ≤ R) (hU : 4 * R ≤ U) (k : ℕ) :
    (∑' n : ℕ,
        (((2 * R : ℕ) : ℝ) / (U : ℝ)) ^ (n + k)) ≤
      2 * (((2 * R : ℕ) : ℝ) / (U : ℝ)) ^ k := by
  have hRpos : 0 < R := hR
  have hUnat : 0 < U :=
    (Nat.mul_pos (by norm_num) hRpos).trans_le hU
  have hUpos : (0 : ℝ) < U := by
    exact_mod_cast hUnat
  have hratio0 :
      0 ≤ (((2 * R : ℕ) : ℝ) / (U : ℝ)) := by
    positivity
  have hratioHalf :
      (((2 * R : ℕ) : ℝ) / (U : ℝ)) ≤ 1 / 2 := by
    apply div_le_half hUpos
    have hUreal : (((4 * R : ℕ) : ℝ)) ≤ (U : ℝ) := by
      exact_mod_cast hU
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hUreal ⊢
    nlinarith
  exact tsum_pow_natAdd_le_two_mul hratio0 hratioHalf k

end GeometricTail
end PaperC
