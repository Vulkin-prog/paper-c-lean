import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Interval
import Lean.Elab.Tactic.Omega

/-!
# An elementary reciprocal-square-root sum

This file records a deliberately elementary estimate used in the smooth-prime
part of Paper C.  It needs no information about the distribution of primes:
we simply enlarge a set of primes to all integers in the same interval.
-/

namespace PaperC

/-- The negative half power is the reciprocal of the square root. -/
lemma rpow_neg_one_half_eq_inv_sqrt (x : ℝ) (hx : 0 ≤ x) :
    x ^ (-(1 / 2 : ℝ)) = (Real.sqrt x)⁻¹ := by
  rw [Real.rpow_neg hx, ← Real.sqrt_eq_rpow]

/-- Taking square roots preserves the elementary inequality `n - 1 ≤ n`. -/
lemma sqrt_nat_sub_one_le (n : ℕ) :
    Real.sqrt ((n - 1 : ℕ) : ℝ) ≤ Real.sqrt n :=
  Real.sqrt_le_sqrt (Nat.cast_le.mpr (Nat.sub_le n 1))

/-- Consecutive natural numbers have square-root squares differing by one. -/
lemma sqrt_nat_sq_sub_sq_eq_one (n : ℕ) (hn : 1 ≤ n) :
    (Real.sqrt n) ^ 2 - (Real.sqrt ((n - 1 : ℕ) : ℝ)) ^ 2 = 1 := by
  rw [Real.sq_sqrt (Nat.cast_nonneg n),
    Real.sq_sqrt (Nat.cast_nonneg (n - 1)), Nat.cast_sub hn, Nat.cast_one]
  ring

/--
One reciprocal-square-root term is bounded by twice the corresponding
increment of the square-root function.
-/
lemma inv_sqrt_nat_le_two_mul_sqrt_sub (n : ℕ) (hn : 1 ≤ n) :
    (Real.sqrt n)⁻¹ ≤
      2 * (Real.sqrt n - Real.sqrt ((n - 1 : ℕ) : ℝ)) := by
  have hsqrt : 0 < Real.sqrt n :=
    Real.sqrt_pos.2 (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn))
  rw [inv_le_iff_one_le_mul₀' hsqrt]
  have hroot := sqrt_nat_sub_one_le n
  have hdiff_nonneg : 0 ≤ Real.sqrt n - Real.sqrt ((n - 1 : ℕ) : ℝ) :=
    sub_nonneg.mpr hroot
  have hsum : Real.sqrt n + Real.sqrt ((n - 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt n := by
    calc
      Real.sqrt n + Real.sqrt ((n - 1 : ℕ) : ℝ) ≤ Real.sqrt n + Real.sqrt n :=
        add_le_add_left hroot _
      _ = 2 * Real.sqrt n := (two_mul _).symm
  calc
    1 = (Real.sqrt n) ^ 2 - (Real.sqrt ((n - 1 : ℕ) : ℝ)) ^ 2 :=
      (sqrt_nat_sq_sub_sq_eq_one n hn).symm
    _ = (Real.sqrt n + Real.sqrt ((n - 1 : ℕ) : ℝ)) *
          (Real.sqrt n - Real.sqrt ((n - 1 : ℕ) : ℝ)) := sq_sub_sq _ _
    _ ≤ (Real.sqrt n - Real.sqrt ((n - 1 : ℕ) : ℝ)) * (2 * Real.sqrt n) :=
      (mul_le_mul_of_nonneg_right hsum hdiff_nonneg).trans_eq (mul_comm _ _)
    _ = Real.sqrt n * (2 * (Real.sqrt n - Real.sqrt ((n - 1 : ℕ) : ℝ))) := by
      ac_rfl

/--
The elementary bound

`∑_{1 ≤ n ≤ H} n⁻¹/² ≤ 2 √H`.

The proof is a finite telescoping argument, using
`n⁻¹/² ≤ 2 (√n - √(n-1))`.
-/
theorem sum_Icc_rpow_neg_one_half_le (H : ℕ) :
    (∑ n ∈ Finset.Icc 1 H, (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤
      2 * Real.sqrt H := by
  induction H with
  | zero => simp
  | succ H ih =>
      have hset :
          Finset.Icc 1 (H + 1) = insert (H + 1) (Finset.Icc 1 H) := by
        ext n
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnotmem : H + 1 ∉ Finset.Icc 1 H := by
        simp
      rw [hset, Finset.sum_insert hnotmem]
      rw [rpow_neg_one_half_eq_inv_sqrt _ (Nat.cast_nonneg _)]
      have hterm := inv_sqrt_nat_le_two_mul_sqrt_sub (H + 1) (by omega)
      simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel,
        add_sub_cancel_right] at hterm ⊢
      calc
        (Real.sqrt ((H : ℝ) + 1))⁻¹ +
              ∑ n ∈ Finset.Icc 1 H, (n : ℝ) ^ (-(1 / 2 : ℝ))
            ≤ (Real.sqrt ((H : ℝ) + 1))⁻¹ + 2 * Real.sqrt H :=
              add_le_add_left ih _
        _ ≤ 2 * (Real.sqrt ((H : ℝ) + 1) - Real.sqrt H) + 2 * Real.sqrt H :=
          add_le_add_right hterm _
        _ = 2 * Real.sqrt ((H : ℝ) + 1) := by ring

/-- The same estimate written with reciprocal square roots. -/
theorem sum_Icc_inv_sqrt_le (H : ℕ) :
    (∑ n ∈ Finset.Icc 1 H, (Real.sqrt n)⁻¹) ≤ 2 * Real.sqrt H := by
  simpa only [rpow_neg_one_half_eq_inv_sqrt _ (Nat.cast_nonneg _)] using
    sum_Icc_rpow_neg_one_half_le H

end PaperC
