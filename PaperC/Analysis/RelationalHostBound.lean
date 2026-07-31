import PaperC.Combinatorics.RelationalHosts
import PaperC.Arithmetic.LargeKernelWeightedCounting
import PaperC.Analysis.SmoothEulerProduct

/-!
# Explicit bound for two-block relational hosts

This module closes the quantitative part of Lemma 4.2.  It first transports
the exact rational certificate count to `ℝ`, then applies the canonical
large-kernel decomposition and the two elementary Euler-product estimates.
-/

namespace PaperC
namespace RelationalHostBound

open scoped BigOperators

open DefectCounting LargeOddKernel

/--
The rational kernel weight used by the finite host count is exactly the real
kernel weight used by the Euler-product estimate after scalar extension.
-/
theorem cast_largeKernelWeightQ (B n : ℕ) :
    ((RelationalHosts.largeKernelWeightQ B n : ℚ) : ℝ) =
      LargeKernelWeightedCounting.largeKernelWeight B n := by
  unfold RelationalHosts.largeKernelWeightQ
    LargeKernelWeightedCounting.largeKernelWeight
  rw [Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast, Nat.cast_pow]

/--
Real-valued form of the exact finite certificate estimate from the
relational-host construction.
-/
theorem card_relationalHosts_cast_le_kernelSum
    {N L : ℕ} (hN : 2 ≤ N) (hL : L ≤ N) :
    ((RelationalHosts.relationalHosts N L).card : ℝ) ≤
      8 * (L + 1 : ℝ) * (N : ℝ) *
        ∑ n ∈ Finset.Icc 1 (3 * N),
          LargeKernelWeightedCounting.largeKernelWeight (L + 1) n := by
  have hq :=
    RelationalHosts.card_relationalHosts_cast_le_kernelSumQ hN hL
  have hsumCast :
      ((∑ n ∈ Finset.Icc 1 (3 * N),
          RelationalHosts.largeKernelWeightQ (L + 1) n : ℚ) : ℝ) =
        ∑ n ∈ Finset.Icc 1 (3 * N),
          LargeKernelWeightedCounting.largeKernelWeight
            (L + 1) n := by
    simp only [Rat.cast_sum, cast_largeKernelWeightQ]
  calc
    ((RelationalHosts.relationalHosts N L).card : ℝ) =
        ((((RelationalHosts.relationalHosts N L).card : ℚ) : ℝ)) := by
      simp
    _ ≤
        ((8 * (L + 1 : ℚ) * (N : ℚ) *
          ∑ n ∈ Finset.Icc 1 (3 * N),
            RelationalHosts.largeKernelWeightQ (L + 1) n : ℚ) : ℝ) :=
      (Rat.cast_le (K := ℝ)).2 hq
    _ =
        8 * (L + 1 : ℝ) * (N : ℝ) *
          ∑ n ∈ Finset.Icc 1 (3 * N),
            LargeKernelWeightedCounting.largeKernelWeight
              (L + 1) n := by
      simp only [Rat.cast_mul, Rat.cast_add, Rat.cast_ofNat,
        Rat.cast_natCast,
        hsumCast]
      norm_num

/--
The large-kernel weighted sum is bounded by the elementary exponential
majorant appearing in Lemma 4.2.
-/
theorem sum_largeKernelWeight_le_sqrt_mul_exp
    (B X : ℕ) (hB : 1 ≤ B) :
    (∑ n ∈ Finset.Icc 1 X,
        LargeKernelWeightedCounting.largeKernelWeight B n) ≤
      Real.sqrt X * Real.exp (4 * Real.sqrt B) := by
  let smallProduct : ℝ :=
    ∏ p ∈ DefectCounting.smallPrimesUpTo B,
      (1 + (Real.sqrt p)⁻¹)
  let largeProduct : ℝ :=
    ∏ p ∈ LargeKernelWeightedCounting.largePrimesBetween B X,
      (1 + (B : ℝ) * (p : ℝ) ^ (-(3 / 2 : ℝ)))
  have hEuler :=
    LargeKernelWeightedCounting.sum_largeKernelWeight_le_eulerProducts B X
  have hsmall :
      smallProduct ≤ Real.exp (2 * Real.sqrt B) := by
    simpa [smallProduct] using
      prod_smallPrimesUpTo_one_add_inv_sqrt_le B
  have hlarge :
      largeProduct ≤ Real.exp (2 * Real.sqrt B) := by
    simpa [largeProduct] using
      LargeEulerProduct.prod_one_add_mul_rpow_neg_three_halves_le_exp_two_sqrt
        B X (LargeKernelWeightedCounting.largePrimesBetween B X) hB
        (LargeKernelWeightedCounting.largePrimesBetween_subset_Ioc B X)
  have hlargeNonneg : 0 ≤ largeProduct := by
    unfold largeProduct
    positivity
  have hsqrtNonneg : 0 ≤ Real.sqrt X := Real.sqrt_nonneg X
  have hexpNonneg : 0 ≤ Real.exp (2 * Real.sqrt B) :=
    (Real.exp_pos _).le
  have hproducts :
      Real.sqrt X * smallProduct * largeProduct ≤
        Real.sqrt X * Real.exp (2 * Real.sqrt B) *
          Real.exp (2 * Real.sqrt B) := by
    calc
      Real.sqrt X * smallProduct * largeProduct ≤
          Real.sqrt X * Real.exp (2 * Real.sqrt B) *
            largeProduct := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsmall hsqrtNonneg)
          hlargeNonneg
      _ ≤ Real.sqrt X * Real.exp (2 * Real.sqrt B) *
            Real.exp (2 * Real.sqrt B) := by
        exact mul_le_mul_of_nonneg_left hlarge
          (mul_nonneg hsqrtNonneg hexpNonneg)
  have hexp :
      Real.exp (2 * Real.sqrt B) * Real.exp (2 * Real.sqrt B) =
        Real.exp (4 * Real.sqrt B) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    (∑ n ∈ Finset.Icc 1 X,
        LargeKernelWeightedCounting.largeKernelWeight B n) ≤
        Real.sqrt X * smallProduct * largeProduct := by
      simpa [smallProduct, largeProduct] using hEuler
    _ ≤ Real.sqrt X * Real.exp (2 * Real.sqrt B) *
          Real.exp (2 * Real.sqrt B) :=
      hproducts
    _ = Real.sqrt X * Real.exp (4 * Real.sqrt B) := by
      rw [mul_assoc, hexp]

/--
Explicit closed form of Lemma 4.2:

`H₂(N,L) ≤ 8 (L+1) N √(3N) exp(4 √(L+1))`.
-/
theorem card_relationalHosts_cast_le_exp_bound
    {N L : ℕ} (hN : 2 ≤ N) (hL : L ≤ N) :
    ((RelationalHosts.relationalHosts N L).card : ℝ) ≤
      8 * (L + 1 : ℝ) * (N : ℝ) * Real.sqrt (3 * N) *
        Real.exp (4 * Real.sqrt (L + 1)) := by
  have hfinite :=
    card_relationalHosts_cast_le_kernelSum hN hL
  have hsum :=
    sum_largeKernelWeight_le_sqrt_mul_exp
      (L + 1) (3 * N) (by omega)
  have hsum' :
      (∑ n ∈ Finset.Icc 1 (3 * N),
          LargeKernelWeightedCounting.largeKernelWeight (L + 1) n) ≤
        Real.sqrt (3 * (N : ℝ)) *
          Real.exp (4 * Real.sqrt (L + 1 : ℝ)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
      using hsum
  have hprefactor :
      0 ≤ 8 * (L + 1 : ℝ) * (N : ℝ) := by positivity
  calc
    ((RelationalHosts.relationalHosts N L).card : ℝ) ≤
        8 * (L + 1 : ℝ) * (N : ℝ) *
          ∑ n ∈ Finset.Icc 1 (3 * N),
            LargeKernelWeightedCounting.largeKernelWeight (L + 1) n :=
      hfinite
    _ ≤ 8 * (L + 1 : ℝ) * (N : ℝ) *
          (Real.sqrt (3 * (N : ℝ)) *
            Real.exp (4 * Real.sqrt (L + 1 : ℝ))) :=
      mul_le_mul_of_nonneg_left hsum' hprefactor
    _ = 8 * (L + 1 : ℝ) * (N : ℝ) * Real.sqrt (3 * N) *
          Real.exp (4 * Real.sqrt (L + 1)) := by
      ring

end RelationalHostBound
end PaperC
