import PaperCV11.TruncatedDefectCount

/-!
# Paper C v1.1: finite Rankin tilt

This is the finite analytic step following the exact truncation. On an
admissible support with squarefree product `s ≤ X`, the square-root fibre is
bounded by `X^(1-σ) s^(-1+σ)` for `σ ≤ 1/2`. Summing and enlarging back to
the full powerset gives the exact finite Euler product used in Proposition 3.3.

The later prime-harmonic estimate, and hence the asymptotic endpoint of
Proposition 3.3, are intentionally not asserted here.
-/

namespace PaperC
namespace V11
namespace RankinTilt

open scoped BigOperators

open DefectCounting
open TerminalKernelCount
open TruncatedDefectCount

/-- A product of a support of small primes is positive. -/
theorem one_le_prod_of_subset_smallPrimesUpTo
    {primeCutoff : ℕ} {small : Finset ℕ}
    (hsmall : small ⊆ smallPrimesUpTo primeCutoff) :
    1 ≤ small.prod id := by
  apply Nat.one_le_iff_ne_zero.mpr
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  exact (mem_smallPrimesUpTo.mp (hsmall hp)).1.ne_zero

/-- The real-variable Rankin comparison used termwise in the finite sum. -/
theorem sqrt_div_le_rankin
    {X s σ : ℝ}
    (hs : 1 ≤ s) (hsX : s ≤ X)
    (hσ : σ ≤ 1 / 2) :
    Real.sqrt (X / s) ≤
      X ^ (1 - σ) * s ^ (-1 + σ) := by
  have hX : 1 ≤ X := hs.trans hsX
  have hspos : 0 < s := zero_lt_one.trans_le hs
  have hs0 : 0 ≤ s := zero_le_one.trans hs
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  have hquot : 1 ≤ X / s := by
    apply (le_div_iff₀ hspos).2
    simpa using hsX
  calc
    Real.sqrt (X / s) = (X / s) ^ (1 / 2 : ℝ) :=
      Real.sqrt_eq_rpow _
    _ ≤ (X / s) ^ (1 - σ) :=
      Real.rpow_le_rpow_of_exponent_le hquot
      (show (1 / 2 : ℝ) ≤ 1 - σ by linarith)
    _ = X ^ (1 - σ) * s ^ (-1 + σ) := by
      rw [Real.div_rpow hX0 hs0, div_eq_mul_inv,
        ← Real.rpow_neg hs0]
      congr 2
      ring

/-- Natural square-root fibres satisfy the Rankin comparison after casting. -/
theorem cast_sqrt_div_le_rankin
    {X s : ℕ} {σ : ℝ}
    (hs : 1 ≤ s) (hsX : s ≤ X)
    (hσ : σ ≤ 1 / 2) :
    (Nat.sqrt (X / s) : ℝ) ≤
      (X : ℝ) ^ (1 - σ) * (s : ℝ) ^ (-1 + σ) := by
  calc
    (Nat.sqrt (X / s) : ℝ) ≤ Real.sqrt (X / s : ℕ) :=
      Real.nat_sqrt_le_real_sqrt
    _ ≤ Real.sqrt ((X : ℝ) / (s : ℝ)) :=
      Real.sqrt_le_sqrt Nat.cast_div_le
    _ ≤ (X : ℝ) ^ (1 - σ) * (s : ℝ) ^ (-1 + σ) := by
      apply sqrt_div_le_rankin
      · exact_mod_cast hs
      · exact_mod_cast hsX
      · exact hσ

/-- A real power distributes over a finite product of natural numbers. -/
theorem cast_prod_rpow_eq_prod
    (small : Finset ℕ) (σ : ℝ) :
    (↑(small.prod id) : ℝ) ^ (-1 + σ) =
      ∏ p ∈ small, (p : ℝ) ^ (-1 + σ) := by
  rw [Nat.cast_prod]
  simp only [id_eq]
  exact (Real.finsetProd_rpow small (fun p : ℕ ↦ (p : ℝ))
    (fun p _ ↦ Nat.cast_nonneg p) (-1 + σ)).symm

/-- Rankin's comparison specialized to one admissible small-prime support. -/
theorem cast_sqrt_div_prod_le_rankin
    {primeCutoff X : ℕ} {small : Finset ℕ} {σ : ℝ}
    (hsmall : small ∈ admissibleSmallSupports primeCutoff X)
    (hσ : σ ≤ 1 / 2) :
    (Nat.sqrt (X / small.prod id) : ℝ) ≤
      (X : ℝ) ^ (1 - σ) *
        ∏ p ∈ small, (p : ℝ) ^ (-1 + σ) := by
  have hdata := mem_admissibleSmallSupports.mp hsmall
  calc
    (Nat.sqrt (X / small.prod id) : ℝ) ≤
        (X : ℝ) ^ (1 - σ) *
          (↑(small.prod id) : ℝ) ^ (-1 + σ) :=
      cast_sqrt_div_le_rankin
        (one_le_prod_of_subset_smallPrimesUpTo hdata.1)
        hdata.2 hσ
    _ = (X : ℝ) ^ (1 - σ) *
          ∏ p ∈ small, (p : ℝ) ^ (-1 + σ) := by
      rw [cast_prod_rpow_eq_prod]

/--
Finite Rankin bound in the Euler-product form needed by the prime-harmonic
envelope of Proposition 3.3.
-/
theorem card_kernel_one_cast_le_rankin_eulerProduct
    (primeCutoff X : ℕ) {σ : ℝ}
    (hσ : σ ≤ 1 / 2) :
    ((boundedLargeKernelValues primeCutoff 1 X).card : ℝ) ≤
      (X : ℝ) ^ (1 - σ) *
        ∏ p ∈ smallPrimesUpTo primeCutoff,
          (1 + (p : ℝ) ^ (-1 + σ)) := by
  have hcard :=
    card_kernel_one_le_truncated_sqrt_sum primeCutoff X
  calc
    ((boundedLargeKernelValues primeCutoff 1 X).card : ℝ) ≤
        ((∑ small ∈ admissibleSmallSupports primeCutoff X,
          Nat.sqrt (X / small.prod id) : ℕ) : ℝ) := by
      exact_mod_cast hcard
    _ = ∑ small ∈ admissibleSmallSupports primeCutoff X,
          (Nat.sqrt (X / small.prod id) : ℝ) := by
      norm_cast
    _ ≤ ∑ small ∈ admissibleSmallSupports primeCutoff X,
          (X : ℝ) ^ (1 - σ) *
            ∏ p ∈ small, (p : ℝ) ^ (-1 + σ) := by
      apply Finset.sum_le_sum
      intro small hsmall
      exact cast_sqrt_div_prod_le_rankin hsmall hσ
    _ = (X : ℝ) ^ (1 - σ) *
          ∑ small ∈ admissibleSmallSupports primeCutoff X,
            ∏ p ∈ small, (p : ℝ) ^ (-1 + σ) := by
      rw [Finset.mul_sum]
    _ ≤ (X : ℝ) ^ (1 - σ) *
          ∑ small ∈ (smallPrimesUpTo primeCutoff).powerset,
            ∏ p ∈ small, (p : ℝ) ^ (-1 + σ) := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro small hsmall
          exact Finset.mem_powerset.mpr
            (mem_admissibleSmallSupports.mp hsmall).1
        · intro small _ _
          positivity
      · exact Real.rpow_nonneg (Nat.cast_nonneg X) _
    _ = (X : ℝ) ^ (1 - σ) *
          ∏ p ∈ smallPrimesUpTo primeCutoff,
            (1 + (p : ℝ) ^ (-1 + σ)) := by
      rw [← Finset.prod_one_add]

end RankinTilt
end V11
end PaperC
