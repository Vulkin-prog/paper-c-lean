import PaperC.Arithmetic.LargeOddKernel
import PaperC.Arithmetic.WeightedDefectCounting
import PaperC.Analysis.LargeEulerProduct
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Weighted counting by the large odd kernel

This module formalizes the finite arithmetic sum in Lemma 4.2.  A positive
integer `n ≤ X` is sent to its canonical triple

`(small odd support, large odd support, square part)`.

The two supports range over powersets of finite prime sets, while the square
part ranges up to `√(X / (u r))`.  This gives the finite Euler-product
majorant for the weight `B^ω(r) / r`.
-/

namespace PaperC
namespace LargeKernelWeightedCounting

open scoped BigOperators

open DefectCounting DefectivePredicate LargeOddKernel

/-- The primes in the finite interval `(B, X]`. -/
def largePrimesBetween (B X : ℕ) : Finset ℕ :=
  (smallPrimesUpTo X).filter fun p ↦ B < p

@[simp]
theorem mem_largePrimesBetween {B X p : ℕ} :
    p ∈ largePrimesBetween B X ↔
      p.Prime ∧ B < p ∧ p ≤ X := by
  simp only [largePrimesBetween, Finset.mem_filter, mem_smallPrimesUpTo]
  aesop

/-- Forgetting primality, the large-prime finset lies in `(B,X]`. -/
theorem largePrimesBetween_subset_Ioc (B X : ℕ) :
    largePrimesBetween B X ⊆ Finset.Ioc B X := by
  intro p hp
  have hpData := mem_largePrimesBetween.mp hp
  exact Finset.mem_Ioc.mpr ⟨hpData.2.1, hpData.2.2⟩

/-- The real weight `B^ω(𝒦_B(n)) / 𝒦_B(n)` in support-cardinality form. -/
noncomputable def largeKernelWeight (B n : ℕ) : ℝ :=
  (B : ℝ) ^ (largeOddPrimeSupport B n).card /
    (largeOddKernel B n : ℝ)

theorem largeKernelWeight_nonneg (B n : ℕ) :
    0 ≤ largeKernelWeight B n := by
  unfold largeKernelWeight
  positivity

/-- The same weight written with Mathlib's distinct-prime-factor function `ω`. -/
theorem largeKernelWeight_eq_cardDistinctFactors (B n : ℕ) :
    largeKernelWeight B n =
      (B : ℝ) ^
          (ArithmeticFunction.cardDistinctFactors (largeOddKernel B n)) /
        (largeOddKernel B n : ℝ) := by
  rw [largeKernelWeight,
    cardDistinctFactors_largeOddKernel]

/--
A support triple consists of the small support, the large support, and the
positive square parameter, in that order.
-/
abbrev KernelTriple :=
  Σ _small : Finset ℕ, Σ _large : Finset ℕ, ℕ

/-- The weight attached to a support triple; it is independent of the square part. -/
noncomputable def kernelTripleWeight (B : ℕ) (t : KernelTriple) : ℝ :=
  (B : ℝ) ^ t.2.1.card / (t.2.1.prod id : ℕ)

theorem kernelTripleWeight_nonneg (B : ℕ) (t : KernelTriple) :
    0 ≤ kernelTripleWeight B t := by
  unfold kernelTripleWeight
  positivity

/-- The canonical support triple attached to `n`. -/
noncomputable def canonicalKernelTriple (B n : ℕ) : KernelTriple :=
  ⟨smallOddPrimeSupport B n,
    ⟨largeOddPrimeSupport B n, canonicalSquarePart n⟩⟩

/-- On the canonical triple, the triple weight is the large-kernel weight. -/
theorem kernelTripleWeight_canonical (B n : ℕ) :
    kernelTripleWeight B (canonicalKernelTriple B n) =
      largeKernelWeight B n := by
  rfl

/--
All candidate triples for positive integers at most `X`.  The square
parameter has the sharp support-dependent range.
-/
noncomputable def kernelTriplesUpTo (B X : ℕ) : Finset KernelTriple :=
  (smallPrimesUpTo B).powerset.sigma fun small ↦
    (largePrimesBetween B X).powerset.sigma fun large ↦
      Finset.Icc 1
        (Nat.sqrt (X / (small.prod id * large.prod id)))

/-- The canonical triple determines every nonzero integer uniquely. -/
theorem canonicalKernelTriple_injective_of_ne_zero
    {B m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (h : canonicalKernelTriple B m = canonicalKernelTriple B n) :
    m = n := by
  have hsmall :
      smallOddPrimeSupport B m = smallOddPrimeSupport B n :=
    congrArg (fun t : KernelTriple ↦ t.1) h
  have hlarge :
      largeOddPrimeSupport B m = largeOddPrimeSupport B n :=
    congrArg (fun t : KernelTriple ↦ t.2.1) h
  have hsquare :
      canonicalSquarePart m = canonicalSquarePart n :=
    congrArg (fun t : KernelTriple ↦ t.2.2) h
  calc
    m = canonicalSquarePart m ^ 2 *
        smallOddPart B m * largeOddKernel B m :=
      canonical_largeOddKernel_decomposition hm
    _ = canonicalSquarePart n ^ 2 *
        smallOddPart B n * largeOddKernel B n := by
      simp only [smallOddPart, largeOddKernel]
      rw [hsquare, hsmall, hlarge]
    _ = n :=
      (canonical_largeOddKernel_decomposition hn).symm

/-- Every canonical triple for `1 ≤ n ≤ X` belongs to the candidate finset. -/
theorem canonicalKernelTriple_mem_kernelTriplesUpTo
    {B X n : ℕ} (hn : n ∈ Finset.Icc 1 X) :
    canonicalKernelTriple B n ∈ kernelTriplesUpTo B X := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hn).1
  have hnX : n ≤ X := (Finset.mem_Icc.mp hn).2
  rw [kernelTriplesUpTo, Finset.mem_sigma]
  refine ⟨Finset.mem_powerset.mpr ?_, ?_⟩
  · intro p hp
    have hpData := prime_and_small_of_mem_smallOddPrimeSupport hp
    exact mem_smallPrimesUpTo.mpr hpData
  · rw [Finset.mem_sigma]
    refine ⟨Finset.mem_powerset.mpr ?_, ?_⟩
    · intro p hp
      have hpData := prime_and_large_of_mem_largeOddPrimeSupport hp
      have hpFactor :
          p ∈ n.primeFactors :=
        largeOddPrimeSupport_subset_primeFactors B n hp
      exact mem_largePrimesBetween.mpr
        ⟨hpData.1, hpData.2,
          (Nat.le_of_mem_primeFactors hpFactor).trans hnX⟩
    · change canonicalSquarePart n ∈
        Finset.Icc 1
          (Nat.sqrt
            (X /
              ((smallOddPrimeSupport B n).prod id *
                (largeOddPrimeSupport B n).prod id)))
      rw [Finset.mem_Icc]
      refine ⟨Nat.one_le_iff_ne_zero.mpr
        (canonicalSquarePart_ne_zero hn0), ?_⟩
      apply Nat.le_sqrt'.mpr
      apply (Nat.le_div_iff_mul_le ?_).mpr
      · calc
          canonicalSquarePart n ^ 2 *
              ((smallOddPrimeSupport B n).prod id *
                (largeOddPrimeSupport B n).prod id) =
              canonicalSquarePart n ^ 2 *
                smallOddPart B n * largeOddKernel B n := by
                simp [smallOddPart, largeOddKernel, Nat.mul_assoc]
          _ = n :=
            (canonical_largeOddKernel_decomposition
              (B := B) hn0).symm
          _ ≤ X := hnX
      · exact Nat.mul_pos
          (Nat.pos_of_ne_zero (smallOddPart_ne_zero B n))
          (Nat.pos_of_ne_zero (largeOddKernel_ne_zero B n))

/-! ## Reindexing the weighted integer sum by canonical triples -/

/-- The finite image of the canonical triples of positive integers at most `X`. -/
noncomputable def canonicalKernelTriplesUpTo (B X : ℕ) :
    Finset KernelTriple :=
  (Finset.Icc 1 X).image (canonicalKernelTriple B)

/-- Every canonical triple lies in the corresponding candidate space. -/
theorem canonicalKernelTriplesUpTo_subset_kernelTriplesUpTo (B X : ℕ) :
    canonicalKernelTriplesUpTo B X ⊆ kernelTriplesUpTo B X := by
  intro t ht
  rw [canonicalKernelTriplesUpTo, Finset.mem_image] at ht
  obtain ⟨n, hn, rfl⟩ := ht
  exact canonicalKernelTriple_mem_kernelTriplesUpTo hn

/-- Reindexing by canonical triples is exact because the map is injective on positive integers. -/
theorem sum_largeKernelWeight_eq_sum_canonicalKernelTriplesUpTo
    (B X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, largeKernelWeight B n) =
      ∑ t ∈ canonicalKernelTriplesUpTo B X, kernelTripleWeight B t := by
  calc
    (∑ n ∈ Finset.Icc 1 X, largeKernelWeight B n) =
        ∑ n ∈ Finset.Icc 1 X,
          kernelTripleWeight B (canonicalKernelTriple B n) := by
      apply Finset.sum_congr rfl
      intro n _hn
      exact (kernelTripleWeight_canonical B n).symm
    _ = ∑ t ∈ canonicalKernelTriplesUpTo B X,
          kernelTripleWeight B t := by
      rw [canonicalKernelTriplesUpTo, Finset.sum_image]
      intro m hm n hn hmn
      apply canonicalKernelTriple_injective_of_ne_zero
      · exact Nat.ne_of_gt (Finset.mem_Icc.mp hm).1
      · exact Nat.ne_of_gt (Finset.mem_Icc.mp hn).1
      · exact hmn

/-- The weighted integer sum is bounded by the sum over every candidate triple. -/
theorem sum_largeKernelWeight_le_sum_kernelTriplesUpTo
    (B X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, largeKernelWeight B n) ≤
      ∑ t ∈ kernelTriplesUpTo B X, kernelTripleWeight B t := by
  rw [sum_largeKernelWeight_eq_sum_canonicalKernelTriplesUpTo]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (canonicalKernelTriplesUpTo_subset_kernelTriplesUpTo B X)
    (fun t _ht _hcanon ↦ kernelTripleWeight_nonneg B t)

/-- Expanding the candidate sigma-finset gives the two support sums explicitly. -/
theorem sum_kernelTriplesUpTo_eq_support_sums (B X : ℕ) :
    (∑ t ∈ kernelTriplesUpTo B X, kernelTripleWeight B t) =
      ∑ small ∈ (smallPrimesUpTo B).powerset,
        ∑ large ∈ (largePrimesBetween B X).powerset,
          (Nat.sqrt
            (X / (small.prod id * large.prod id)) : ℝ) *
            ((B : ℝ) ^ large.card / (large.prod id : ℕ)) := by
  rw [kernelTriplesUpTo, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro small hsmall
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro large hlarge
  simp [kernelTripleWeight, Nat.card_Icc]

/-! ## Support weights and the two Euler factors -/

/-- The reciprocal-square-root weight of a small support. -/
noncomputable def smallSupportWeight (small : Finset ℕ) : ℝ :=
  ∏ p ∈ small, (Real.sqrt p)⁻¹

/-- The denominator form of the large-support weight. -/
noncomputable def largeSupportDenominatorWeight
    (B : ℕ) (large : Finset ℕ) : ℝ :=
  ∏ p ∈ large, (B : ℝ) / ((p : ℝ) * Real.sqrt p)

/-- The negative-three-halves form of the large-support weight. -/
noncomputable def largeSupportWeight
    (B : ℕ) (large : Finset ℕ) : ℝ :=
  ∏ p ∈ large, (B : ℝ) * (p : ℝ) ^ (-(3 / 2 : ℝ))

/-- A small-prime support and a large-prime support are disjoint. -/
theorem disjoint_of_subset_smallPrimesUpTo_of_subset_largePrimesBetween
    {B X : ℕ} {small large : Finset ℕ}
    (hsmall : small ⊆ smallPrimesUpTo B)
    (hlarge : large ⊆ largePrimesBetween B X) :
    Disjoint small large := by
  rw [Finset.disjoint_left]
  intro p hpSmall hpLarge
  have hpB : p ≤ B :=
    (mem_smallPrimesUpTo.mp (hsmall hpSmall)).2
  have hBp : B < p :=
    (mem_largePrimesBetween.mp (hlarge hpLarge)).2.1
  omega

/--
The square-root count for a pair of disjoint supports splits into its small
and large reciprocal-square-root factors.
-/
theorem cast_sqrt_div_small_mul_large_le
    (X : ℕ) {small large : Finset ℕ}
    (hdisj : Disjoint small large) :
    (Nat.sqrt (X / (small.prod id * large.prod id)) : ℝ) ≤
      Real.sqrt X * smallSupportWeight small *
        (∏ p ∈ large, (Real.sqrt p)⁻¹) := by
  have h :=
    WeightedDefectCounting.cast_sqrt_div_prod_le (small ∪ large) X
  have hprod :
      (small ∪ large).prod id =
        small.prod id * large.prod id :=
    Finset.prod_union hdisj
  have hweight :
      (∏ p ∈ small ∪ large, (Real.sqrt p)⁻¹) =
        (∏ p ∈ small, (Real.sqrt p)⁻¹) *
          ∏ p ∈ large, (Real.sqrt p)⁻¹ :=
    Finset.prod_union hdisj
  rw [hprod, hweight] at h
  simpa only [smallSupportWeight, mul_assoc] using h

/--
The remaining large-support factors combine exactly into
`B^#large / (r √r)`.
-/
theorem invSqrtWeight_mul_kernelWeight_eq_denominatorWeight
    (B : ℕ) (large : Finset ℕ) :
    (∏ p ∈ large, (Real.sqrt p)⁻¹) *
        ((B : ℝ) ^ large.card / (large.prod id : ℕ)) =
      largeSupportDenominatorWeight B large := by
  simp only [largeSupportDenominatorWeight, Finset.prod_div_distrib,
    Finset.prod_const, Finset.prod_mul_distrib,
    Finset.prod_inv_distrib, div_eq_mul_inv, mul_inv_rev]
  rw [Nat.cast_prod]
  simp only [id_eq]
  ring

/-- On primes in `(B,X]`, denominator and negative-power notation agree. -/
theorem largeSupportDenominatorWeight_eq_largeSupportWeight
    {B X : ℕ} {large : Finset ℕ}
    (hlarge : large ⊆ largePrimesBetween B X) :
    largeSupportDenominatorWeight B large =
      largeSupportWeight B large := by
  rw [largeSupportDenominatorWeight, largeSupportWeight]
  apply Finset.prod_congr rfl
  intro p hp
  have hpLarge := mem_largePrimesBetween.mp (hlarge hp)
  have hpOne : 1 ≤ p := hpLarge.1.one_lt.le
  rw [div_eq_mul_inv,
    ← LargeEulerProduct.rpow_neg_three_halves_eq_inv_mul_sqrt hpOne]

/-! ## The finite Euler-product bound -/

/--
One fixed pair of supports contributes at most its separated small/large
Euler weight.
-/
theorem support_pair_contribution_le
    {B X : ℕ} {small large : Finset ℕ}
    (hsmall : small ⊆ smallPrimesUpTo B)
    (hlarge : large ⊆ largePrimesBetween B X) :
    (Nat.sqrt (X / (small.prod id * large.prod id)) : ℝ) *
        ((B : ℝ) ^ large.card / (large.prod id : ℕ)) ≤
      Real.sqrt X * smallSupportWeight small *
        largeSupportWeight B large := by
  have hdisj :=
    disjoint_of_subset_smallPrimesUpTo_of_subset_largePrimesBetween
      hsmall hlarge
  have hsqrt :=
    cast_sqrt_div_small_mul_large_le X hdisj
  have hkernelNonneg :
      0 ≤ (B : ℝ) ^ large.card / (large.prod id : ℕ) := by
    positivity
  calc
    (Nat.sqrt (X / (small.prod id * large.prod id)) : ℝ) *
          ((B : ℝ) ^ large.card / (large.prod id : ℕ))
        ≤ (Real.sqrt X * smallSupportWeight small *
            (∏ p ∈ large, (Real.sqrt p)⁻¹)) *
          ((B : ℝ) ^ large.card / (large.prod id : ℕ)) :=
      mul_le_mul_of_nonneg_right hsqrt hkernelNonneg
    _ = Real.sqrt X * smallSupportWeight small *
        ((∏ p ∈ large, (Real.sqrt p)⁻¹) *
          ((B : ℝ) ^ large.card / (large.prod id : ℕ))) := by
      ring
    _ = Real.sqrt X * smallSupportWeight small *
        largeSupportDenominatorWeight B large := by
      rw [invSqrtWeight_mul_kernelWeight_eq_denominatorWeight]
    _ = Real.sqrt X * smallSupportWeight small *
        largeSupportWeight B large := by
      rw [largeSupportDenominatorWeight_eq_largeSupportWeight hlarge]

/-- Summing the preceding fibrewise estimate over both powersets. -/
theorem sum_kernelTriplesUpTo_le_support_weight_sums (B X : ℕ) :
    (∑ t ∈ kernelTriplesUpTo B X, kernelTripleWeight B t) ≤
      ∑ small ∈ (smallPrimesUpTo B).powerset,
        ∑ large ∈ (largePrimesBetween B X).powerset,
          Real.sqrt X * smallSupportWeight small *
            largeSupportWeight B large := by
  rw [sum_kernelTriplesUpTo_eq_support_sums]
  apply Finset.sum_le_sum
  intro small hsmall
  apply Finset.sum_le_sum
  intro large hlarge
  exact support_pair_contribution_le
    (Finset.mem_powerset.mp hsmall)
    (Finset.mem_powerset.mp hlarge)

/-- The double support sum factors exactly into the two finite Euler products. -/
theorem support_weight_sums_eq_eulerProducts (B X : ℕ) :
    (∑ small ∈ (smallPrimesUpTo B).powerset,
        ∑ large ∈ (largePrimesBetween B X).powerset,
          Real.sqrt X * smallSupportWeight small *
            largeSupportWeight B large) =
      Real.sqrt X *
        (∏ p ∈ smallPrimesUpTo B,
          (1 + (Real.sqrt p)⁻¹)) *
        ∏ p ∈ largePrimesBetween B X,
          (1 + (B : ℝ) * (p : ℝ) ^ (-(3 / 2 : ℝ))) := by
  have hsmallEuler :
      (∑ small ∈ (smallPrimesUpTo B).powerset,
          smallSupportWeight small) =
        ∏ p ∈ smallPrimesUpTo B,
          (1 + (Real.sqrt p)⁻¹) := by
    simpa only [smallSupportWeight] using
      (Finset.prod_one_add
        (s := smallPrimesUpTo B)
        (f := fun p : ℕ ↦ (Real.sqrt p)⁻¹)).symm
  have hlargeEuler :
      (∑ large ∈ (largePrimesBetween B X).powerset,
          largeSupportWeight B large) =
        ∏ p ∈ largePrimesBetween B X,
          (1 + (B : ℝ) * (p : ℝ) ^ (-(3 / 2 : ℝ))) := by
    simpa only [largeSupportWeight] using
      (Finset.prod_one_add
        (s := largePrimesBetween B X)
        (f := fun p : ℕ ↦
          (B : ℝ) * (p : ℝ) ^ (-(3 / 2 : ℝ)))).symm
  calc
    (∑ small ∈ (smallPrimesUpTo B).powerset,
        ∑ large ∈ (largePrimesBetween B X).powerset,
          Real.sqrt X * smallSupportWeight small *
            largeSupportWeight B large) =
        ∑ small ∈ (smallPrimesUpTo B).powerset,
          (Real.sqrt X * smallSupportWeight small) *
            (∑ large ∈ (largePrimesBetween B X).powerset,
              largeSupportWeight B large) := by
      apply Finset.sum_congr rfl
      intro small hsmall
      rw [Finset.mul_sum]
    _ = (∑ small ∈ (smallPrimesUpTo B).powerset,
          Real.sqrt X * smallSupportWeight small) *
        (∑ large ∈ (largePrimesBetween B X).powerset,
          largeSupportWeight B large) := by
      rw [Finset.sum_mul]
    _ = (Real.sqrt X *
          ∑ small ∈ (smallPrimesUpTo B).powerset,
            smallSupportWeight small) *
        (∑ large ∈ (largePrimesBetween B X).powerset,
          largeSupportWeight B large) := by
      apply congrArg (fun z : ℝ ↦
        z * (∑ large ∈ (largePrimesBetween B X).powerset,
          largeSupportWeight B large))
      rw [Finset.mul_sum]
    _ = Real.sqrt X *
        (∏ p ∈ smallPrimesUpTo B,
          (1 + (Real.sqrt p)⁻¹)) *
        ∏ p ∈ largePrimesBetween B X,
          (1 + (B : ℝ) * (p : ℝ) ^ (-(3 / 2 : ℝ))) := by
      rw [hsmallEuler, hlargeEuler]

/--
Finite weighted form of Lemma 4.2.

The left side is the exact sum over `1 ≤ n ≤ X`; the right side is the
small-prime Euler factor times the large-kernel Euler factor.
-/
theorem sum_largeKernelWeight_le_eulerProducts (B X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, largeKernelWeight B n) ≤
      Real.sqrt X *
        (∏ p ∈ smallPrimesUpTo B,
          (1 + (Real.sqrt p)⁻¹)) *
        ∏ p ∈ largePrimesBetween B X,
          (1 + (B : ℝ) * (p : ℝ) ^ (-(3 / 2 : ℝ))) := by
  calc
    (∑ n ∈ Finset.Icc 1 X, largeKernelWeight B n) ≤
        ∑ t ∈ kernelTriplesUpTo B X, kernelTripleWeight B t :=
      sum_largeKernelWeight_le_sum_kernelTriplesUpTo B X
    _ ≤ ∑ small ∈ (smallPrimesUpTo B).powerset,
        ∑ large ∈ (largePrimesBetween B X).powerset,
          Real.sqrt X * smallSupportWeight small *
            largeSupportWeight B large :=
      sum_kernelTriplesUpTo_le_support_weight_sums B X
    _ = Real.sqrt X *
        (∏ p ∈ smallPrimesUpTo B,
          (1 + (Real.sqrt p)⁻¹)) *
        ∏ p ∈ largePrimesBetween B X,
          (1 + (B : ℝ) * (p : ℝ) ^ (-(3 / 2 : ℝ))) :=
      support_weight_sums_eq_eulerProducts B X

end LargeKernelWeightedCounting
end PaperC
