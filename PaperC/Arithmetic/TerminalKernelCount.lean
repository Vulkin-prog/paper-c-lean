import PaperC.Arithmetic.LargeKernelWeightedCounting
import PaperC.Analysis.ReciprocalSqrtSum
import PaperC.Analysis.SmoothEulerProduct
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Counting integers with a bounded large odd kernel

Step 2 of Theorem 10.1 introduces

`A_{B,T}(X) = {n : 1 ≤ n ≤ X, 𝒦_B(n) ≤ T}`.

This module proves the finite arithmetic estimate behind equation (10.3).
Every positive `n` has the canonical and unique decomposition

`n = z² * a * r`,

where `a` is the product of a subset of the primes at most `B` and
`r = 𝒦_B(n)`.  Restricting `r ≤ T`, enlarging the possible kernels to all
positive integers up to `T`, and summing the square-root fibres gives

`#A_{B,T}(X) ≤
  2 √X √T ∏_{p≤B} (1 + 1/√p)`.

No asymptotic notation or external theorem is used here.
-/

namespace PaperC
namespace TerminalKernelCount

open scoped BigOperators

open DefectCounting
open DefectivePredicate
open LargeOddKernel
open WeightedDefectCounting

/-- Positive integers up to `X` whose large odd kernel is at most `T`. -/
noncomputable def boundedLargeKernelValues
    (B T X : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter fun n ↦ largeOddKernel B n ≤ T

@[simp]
theorem mem_boundedLargeKernelValues
    {B T X n : ℕ} :
    n ∈ boundedLargeKernelValues B T X ↔
      1 ≤ n ∧ n ≤ X ∧ largeOddKernel B n ≤ T := by
  simp [boundedLargeKernelValues, and_assoc]

/--
A terminal kernel triple records the small odd support, the numerical large
kernel, and the positive square parameter.
-/
abbrev TerminalKernelTriple :=
  Σ _small : Finset ℕ, Σ _kernel : ℕ, ℕ

/-- Canonical terminal triple attached to a positive integer. -/
noncomputable def canonicalTerminalKernelTriple
    (B n : ℕ) : TerminalKernelTriple :=
  ⟨smallOddPrimeSupport B n,
    ⟨largeOddKernel B n, canonicalSquarePart n⟩⟩

/--
Candidate triples after the harmless overcount in which the large kernel is
allowed to be any integer in `[1,T]`.
-/
noncomputable def terminalKernelTriples
    (B T X : ℕ) : Finset TerminalKernelTriple :=
  (smallPrimesUpTo B).powerset.sigma fun small ↦
    (Finset.Icc 1 T).sigma fun r ↦
      Finset.Icc 1
        (Nat.sqrt (X / (small.prod id * r)))

/-- The canonical triple determines a positive integer uniquely. -/
theorem canonicalTerminalKernelTriple_injective_of_ne_zero
    {B m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (h :
      canonicalTerminalKernelTriple B m =
        canonicalTerminalKernelTriple B n) :
    m = n := by
  have hsmall :
      smallOddPrimeSupport B m =
        smallOddPrimeSupport B n :=
    congrArg (fun t : TerminalKernelTriple ↦ t.1) h
  have hkernel :
      largeOddKernel B m =
        largeOddKernel B n :=
    congrArg (fun t : TerminalKernelTriple ↦ t.2.1) h
  have hsquare :
      canonicalSquarePart m =
        canonicalSquarePart n :=
    congrArg (fun t : TerminalKernelTriple ↦ t.2.2) h
  calc
    m = canonicalSquarePart m ^ 2 *
          smallOddPart B m * largeOddKernel B m :=
      canonical_largeOddKernel_decomposition hm
    _ = canonicalSquarePart n ^ 2 *
          smallOddPart B n * largeOddKernel B n := by
      simp only [smallOddPart]
      rw [hsquare, hsmall, hkernel]
    _ = n :=
      (canonical_largeOddKernel_decomposition hn).symm

/-- Every bounded positive integer supplies one of the candidate triples. -/
theorem canonicalTerminalKernelTriple_mem
    {B T X n : ℕ}
    (hn : n ∈ boundedLargeKernelValues B T X) :
    canonicalTerminalKernelTriple B n ∈
      terminalKernelTriples B T X := by
  have hnData := mem_boundedLargeKernelValues.mp hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt hnData.1
  rw [terminalKernelTriples, Finset.mem_sigma]
  refine ⟨Finset.mem_powerset.mpr ?_, ?_⟩
  · intro p hp
    exact mem_smallPrimesUpTo.mpr
      (prime_and_small_of_mem_smallOddPrimeSupport hp)
  · rw [Finset.mem_sigma]
    refine ⟨Finset.mem_Icc.mpr
      ⟨one_le_largeOddKernel B n, hnData.2.2⟩, ?_⟩
    change canonicalSquarePart n ∈
      Finset.Icc 1
        (Nat.sqrt
          (X /
            ((smallOddPrimeSupport B n).prod id *
              largeOddKernel B n)))
    rw [Finset.mem_Icc]
    refine ⟨Nat.one_le_iff_ne_zero.mpr
      (canonicalSquarePart_ne_zero hn0), ?_⟩
    apply Nat.le_sqrt'.mpr
    apply (Nat.le_div_iff_mul_le ?_).mpr
    · calc
        canonicalSquarePart n ^ 2 *
            ((smallOddPrimeSupport B n).prod id *
              largeOddKernel B n) =
            canonicalSquarePart n ^ 2 *
              smallOddPart B n * largeOddKernel B n := by
              simp [smallOddPart, Nat.mul_assoc]
        _ = n :=
          (canonical_largeOddKernel_decomposition hn0).symm
        _ ≤ X := hnData.2.1
    · exact Nat.mul_pos
        (Nat.pos_of_ne_zero (smallOddPart_ne_zero B n))
        (Nat.pos_of_ne_zero (largeOddKernel_ne_zero B n))

/-- The canonical image of the bounded value set. -/
noncomputable def canonicalTerminalKernelTriples
    (B T X : ℕ) : Finset TerminalKernelTriple :=
  (boundedLargeKernelValues B T X).image
    (canonicalTerminalKernelTriple B)

/-- Canonical triples form a subset of the overcounting candidate space. -/
theorem canonicalTerminalKernelTriples_subset
    (B T X : ℕ) :
    canonicalTerminalKernelTriples B T X ⊆
      terminalKernelTriples B T X := by
  intro t ht
  obtain ⟨n, hn, rfl⟩ :=
    Finset.mem_image.mp ht
  exact canonicalTerminalKernelTriple_mem hn

/-- Reindexing by the canonical triple preserves cardinality exactly. -/
theorem card_canonicalTerminalKernelTriples
    (B T X : ℕ) :
    (canonicalTerminalKernelTriples B T X).card =
      (boundedLargeKernelValues B T X).card := by
  rw [canonicalTerminalKernelTriples,
    Finset.card_image_iff.mpr]
  intro m hm n hn hmn
  exact canonicalTerminalKernelTriple_injective_of_ne_zero
    (Nat.ne_of_gt (mem_boundedLargeKernelValues.mp hm).1)
    (Nat.ne_of_gt (mem_boundedLargeKernelValues.mp hn).1)
    hmn

/--
First finite bound: expand the candidate sigma-finset into its exact
square-root fibre count.
-/
theorem card_boundedLargeKernelValues_le_sqrt_sum
    (B T X : ℕ) :
    (boundedLargeKernelValues B T X).card ≤
      ∑ small ∈ (smallPrimesUpTo B).powerset,
        ∑ r ∈ Finset.Icc 1 T,
          Nat.sqrt (X / (small.prod id * r)) := by
  calc
    (boundedLargeKernelValues B T X).card =
        (canonicalTerminalKernelTriples B T X).card :=
      (card_canonicalTerminalKernelTriples B T X).symm
    _ ≤ (terminalKernelTriples B T X).card :=
      Finset.card_le_card
        (canonicalTerminalKernelTriples_subset B T X)
    _ = ∑ small ∈ (smallPrimesUpTo B).powerset,
          ∑ r ∈ Finset.Icc 1 T,
            Nat.sqrt (X / (small.prod id * r)) := by
      rw [terminalKernelTriples, Finset.card_sigma]
      apply Finset.sum_congr rfl
      intro small hsmall
      rw [Finset.card_sigma]
      apply Finset.sum_congr rfl
      intro r hr
      simp [Nat.card_Icc]

/-- Generic reciprocal-square-root estimate for an arbitrary denominator. -/
theorem cast_sqrt_div_le
    (X d : ℕ) :
    (Nat.sqrt (X / d) : ℝ) ≤
      Real.sqrt X * (Real.sqrt d)⁻¹ := by
  by_cases hd : d = 0
  · subst d
    simp
  · calc
      (Nat.sqrt (X / d) : ℝ) ≤
          Real.sqrt (X / d : ℕ) :=
        Real.nat_sqrt_le_real_sqrt
      _ ≤ Real.sqrt ((X : ℝ) / (d : ℝ)) :=
        Real.sqrt_le_sqrt Nat.cast_div_le
      _ = Real.sqrt X / Real.sqrt d := by
        rw [Real.sqrt_div (Nat.cast_nonneg X)]
      _ = Real.sqrt X * (Real.sqrt d)⁻¹ := by
        rw [div_eq_mul_inv]

/-- Split the denominator into the small support and the numerical kernel. -/
theorem cast_sqrt_div_small_mul_kernel_le
    (X r : ℕ) (small : Finset ℕ) :
    (Nat.sqrt (X / (small.prod id * r)) : ℝ) ≤
      Real.sqrt X *
        (∏ p ∈ small, (Real.sqrt p)⁻¹) *
        (Real.sqrt r)⁻¹ := by
  have h :=
    cast_sqrt_div_le X (small.prod id * r)
  calc
    (Nat.sqrt (X / (small.prod id * r)) : ℝ) ≤
        Real.sqrt X *
          (Real.sqrt (small.prod id * r))⁻¹ :=
      by simpa only [Nat.cast_mul] using h
    _ = Real.sqrt X *
        (∏ p ∈ small, (Real.sqrt p)⁻¹) *
        (Real.sqrt r)⁻¹ := by
      rw [Real.sqrt_mul (Nat.cast_nonneg (small.prod id))]
      rw [sqrt_natCast_prod]
      simp only [id_eq, mul_inv_rev, Finset.prod_inv_distrib]
      ring

/-- Cast the finite fibre count and bound it by separated support weights. -/
theorem card_boundedLargeKernelValues_cast_le_weight_sums
    (B T X : ℕ) :
    ((boundedLargeKernelValues B T X).card : ℝ) ≤
      ∑ small ∈ (smallPrimesUpTo B).powerset,
        ∑ r ∈ Finset.Icc 1 T,
          Real.sqrt X *
            (∏ p ∈ small, (Real.sqrt p)⁻¹) *
            (Real.sqrt r)⁻¹ := by
  have hfinite :=
    card_boundedLargeKernelValues_le_sqrt_sum B T X
  calc
    ((boundedLargeKernelValues B T X).card : ℝ) ≤
        ((∑ small ∈ (smallPrimesUpTo B).powerset,
          ∑ r ∈ Finset.Icc 1 T,
            Nat.sqrt (X / (small.prod id * r)) : ℕ) : ℝ) := by
      exact_mod_cast hfinite
    _ = ∑ small ∈ (smallPrimesUpTo B).powerset,
          ∑ r ∈ Finset.Icc 1 T,
            (Nat.sqrt (X / (small.prod id * r)) : ℝ) := by
      norm_cast
    _ ≤ ∑ small ∈ (smallPrimesUpTo B).powerset,
          ∑ r ∈ Finset.Icc 1 T,
            Real.sqrt X *
              (∏ p ∈ small, (Real.sqrt p)⁻¹) *
              (Real.sqrt r)⁻¹ := by
      apply Finset.sum_le_sum
      intro small hsmall
      apply Finset.sum_le_sum
      intro r hr
      exact cast_sqrt_div_small_mul_kernel_le X r small

/--
Finite form of equation (10.3):

`#A_{B,T}(X) ≤ 2 √X √T ∏_{p≤B}(1+p⁻¹/²)`.
-/
theorem card_boundedLargeKernelValues_cast_le
    (B T X : ℕ) :
    ((boundedLargeKernelValues B T X).card : ℝ) ≤
      2 * Real.sqrt X * Real.sqrt T *
        ∏ p ∈ smallPrimesUpTo B,
          (1 + (Real.sqrt p)⁻¹) := by
  have hweighted :=
    card_boundedLargeKernelValues_cast_le_weight_sums B T X
  have hr :
      (∑ r ∈ Finset.Icc 1 T, (Real.sqrt r)⁻¹) ≤
        2 * Real.sqrt T :=
    sum_Icc_inv_sqrt_le T
  have heuler :
      (∑ small ∈ (smallPrimesUpTo B).powerset,
          ∏ p ∈ small, (Real.sqrt p)⁻¹) =
        ∏ p ∈ smallPrimesUpTo B,
          (1 + (Real.sqrt p)⁻¹) := by
    simpa only using
      (Finset.prod_one_add
        (s := smallPrimesUpTo B)
        (f := fun p : ℕ ↦ (Real.sqrt p)⁻¹)).symm
  calc
    ((boundedLargeKernelValues B T X).card : ℝ) ≤
        ∑ small ∈ (smallPrimesUpTo B).powerset,
          ∑ r ∈ Finset.Icc 1 T,
            Real.sqrt X *
              (∏ p ∈ small, (Real.sqrt p)⁻¹) *
              (Real.sqrt r)⁻¹ :=
      hweighted
    _ = Real.sqrt X *
        (∑ small ∈ (smallPrimesUpTo B).powerset,
          ∏ p ∈ small, (Real.sqrt p)⁻¹) *
        (∑ r ∈ Finset.Icc 1 T, (Real.sqrt r)⁻¹) := by
      calc
        (∑ small ∈ (smallPrimesUpTo B).powerset,
            ∑ r ∈ Finset.Icc 1 T,
              Real.sqrt X *
                (∏ p ∈ small, (Real.sqrt p)⁻¹) *
                (Real.sqrt r)⁻¹) =
            ∑ small ∈ (smallPrimesUpTo B).powerset,
              (Real.sqrt X *
                (∏ p ∈ small, (Real.sqrt p)⁻¹)) *
                (∑ r ∈ Finset.Icc 1 T, (Real.sqrt r)⁻¹) := by
          apply Finset.sum_congr rfl
          intro small hsmall
          rw [Finset.mul_sum]
        _ =
            (∑ small ∈ (smallPrimesUpTo B).powerset,
              Real.sqrt X *
                (∏ p ∈ small, (Real.sqrt p)⁻¹)) *
              (∑ r ∈ Finset.Icc 1 T, (Real.sqrt r)⁻¹) := by
          rw [Finset.sum_mul]
        _ = Real.sqrt X *
            (∑ small ∈ (smallPrimesUpTo B).powerset,
              ∏ p ∈ small, (Real.sqrt p)⁻¹) *
            (∑ r ∈ Finset.Icc 1 T, (Real.sqrt r)⁻¹) := by
          rw [← Finset.mul_sum]
    _ ≤ Real.sqrt X *
        (∑ small ∈ (smallPrimesUpTo B).powerset,
          ∏ p ∈ small, (Real.sqrt p)⁻¹) *
        (2 * Real.sqrt T) := by
      apply mul_le_mul_of_nonneg_left hr
      positivity
    _ = 2 * Real.sqrt X * Real.sqrt T *
        ∏ p ∈ smallPrimesUpTo B,
          (1 + (Real.sqrt p)⁻¹) := by
      rw [heuler]
      ring

/--
Explicit exponential envelope obtained from the elementary smooth-prime
Euler product.  This is the finite expression whose critical-window
specialization is `X^{1/2} T^{1/2} X^{o(1)}`.
-/
theorem card_boundedLargeKernelValues_cast_le_exp
    (B T X : ℕ) :
    ((boundedLargeKernelValues B T X).card : ℝ) ≤
      2 * Real.sqrt X * Real.sqrt T *
        Real.exp (2 * Real.sqrt B) := by
  have hfinite :=
    card_boundedLargeKernelValues_cast_le B T X
  have heuler :=
    prod_smallPrimesUpTo_one_add_inv_sqrt_le B
  refine hfinite.trans ?_
  apply mul_le_mul_of_nonneg_left heuler
  positivity

end TerminalKernelCount
end PaperC
