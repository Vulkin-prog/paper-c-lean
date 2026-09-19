import PaperCV282.DefectiveRankinCount
import PaperCPrel8.RoughKernelPowerSums

/-! # Finite Rankin counts for the actual rough kernel

The canonical square/small-support/rough-kernel injection gives the bound
without a zeta factor. This strengthens the first finite estimate of G.1.
-/
namespace PaperC.Prel8.RoughKernelRankin

open scoped BigOperators
open DefectCounting TerminalKernelCount V11.RankinTilt V282.DefectiveRankinCount

/-- The square-fibre estimate also holds when the denominator exceeds X. -/
theorem square_fibre_le (X d : ℕ) {σ : ℝ} (hd : 1 ≤ d) (hσ : σ ≤ 1 / 2) :
    (Nat.sqrt (X / d) : ℝ) ≤ (X : ℝ) ^ (1 - σ) * (d : ℝ) ^ (-1 + σ) := by
  by_cases h : d ≤ X
  · exact cast_sqrt_div_le_rankin hd h hσ
  · rw [Nat.div_eq_of_lt (by omega), Nat.sqrt_zero, Nat.cast_zero]
    positivity

/-- Separate the small support and numerical kernel at any admissible tilt. -/
theorem square_fibre_split (B X r : ℕ) (small : Finset ℕ) {σ : ℝ}
    (hsmall : small ⊆ smallPrimesUpTo B) (hr : 1 ≤ r) (hσ : σ ≤ 1 / 2) :
    (Nat.sqrt (X / (small.prod id * r)) : ℝ) ≤
      (X : ℝ) ^ (1 - σ) * (∏ p ∈ small, (p : ℝ) ^ (-1 + σ)) *
        (r : ℝ) ^ (-1 + σ) := by
  have hd : 1 ≤ small.prod id * r := by
    have := one_le_prod_of_subset_smallPrimesUpTo hsmall
    nlinarith
  have h := square_fibre_le X (small.prod id * r) hd hσ
  rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _),
    cast_prod_rpow_eq_prod] at h
  simpa only [mul_assoc] using h

/-- Literal count of integers whose large odd kernel is at most T. -/
theorem count_le_weight_sum (Y T X : ℕ) {σ : ℝ} (hσ : σ ≤ 1 / 2) :
    ((boundedLargeKernelValues Y T X).card : ℝ) ≤
      (X : ℝ) ^ (1 - σ) * rankinEulerProduct Y σ *
        ∑ r ∈ Finset.Icc 1 T, (r : ℝ) ^ (-1 + σ) := by
  have hcount := card_boundedLargeKernelValues_le_sqrt_sum Y T X
  have hc : ((boundedLargeKernelValues Y T X).card : ℝ) ≤
      ∑ small ∈ (smallPrimesUpTo Y).powerset,
        ∑ r ∈ Finset.Icc 1 T, (Nat.sqrt (X / (small.prod id * r)) : ℝ) := by
    exact_mod_cast hcount
  calc
    _ ≤ ∑ small ∈ (smallPrimesUpTo Y).powerset,
        ∑ r ∈ Finset.Icc 1 T,
          (X : ℝ) ^ (1 - σ) * (∏ p ∈ small, (p : ℝ) ^ (-1 + σ)) *
            (r : ℝ) ^ (-1 + σ) := by
      apply hc.trans
      apply Finset.sum_le_sum
      intro small hsmall
      apply Finset.sum_le_sum
      intro r hr
      exact square_fibre_split Y X r small (Finset.mem_powerset.mp hsmall)
        (Finset.mem_Icc.mp hr).1 hσ
    _ = _ := by
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul, ← Finset.mul_sum, ← Finset.prod_one_add]
      rfl

/-- The finite small-kernel Rankin bound, stronger than G.1 by the zeta factor. -/
theorem count_le (Y T X : ℕ) {σ : ℝ} (hσ0 : 0 < σ) (hσ : σ ≤ 1 / 2) :
    ((boundedLargeKernelValues Y T X).card : ℝ) ≤
      (X : ℝ) ^ (1 - σ) * rankinEulerProduct Y σ *
        (1 + (T : ℝ) ^ σ / σ) := by
  apply (count_le_weight_sum Y T X hσ).trans
  apply mul_le_mul_of_nonneg_left (RoughKernelPowerSums.sum_Icc_rankin_le T hσ0 (by linarith))
  apply mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg X) _)
  unfold rankinEulerProduct
  exact Finset.prod_nonneg (fun p _ ↦ by positivity)

/-- Normalization by the actual population size gives X to the negative tilt. -/
theorem normalized_count_le (Y T X : ℕ) (hX : 0 < X)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ : σ ≤ 1 / 2) :
    ((boundedLargeKernelValues Y T X).card : ℝ) / X ≤
      (X : ℝ) ^ (-σ) * rankinEulerProduct Y σ * (1 + (T : ℝ) ^ σ / σ) := by
  have hx : (0 : ℝ) < X := by exact_mod_cast hX
  have h := div_le_div_of_nonneg_right (count_le Y T X hσ0 hσ) hx.le
  have hp : (X : ℝ) ^ (1 - σ) = (X : ℝ) ^ (-σ) * X := by
    rw [show 1 - σ = -σ + 1 by ring, Real.rpow_add hx, Real.rpow_one]
  rw [hp] at h
  convert h using 1; field_simp

end PaperC.Prel8.RoughKernelRankin
