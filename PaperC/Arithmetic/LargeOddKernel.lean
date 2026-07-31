import PaperC.Arithmetic.DefectivePredicate
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.ArithmeticFunction

/-!
# The large odd kernel

For a cutoff `B` and an integer `n`, the large odd kernel is the product of
the primes `p > B` which occur to odd order in `n`.  This is the canonical
integer denoted `𝒦_B(n)` in Lemma 4.2 of Paper C.

Besides the defining support characterization, this file records the
properties used by the counting argument: the kernel is a nonzero squarefree
divisor of `n`, its prime factors recover its defining support, and the
canonical odd-support decomposition of `n` splits into coprime small and
large parts.
-/

namespace PaperC
namespace LargeOddKernel

open scoped BigOperators

open DefectivePredicate

/-- The odd-valuation primes of `n` lying strictly above `B`. -/
noncomputable def largeOddPrimeSupport (B n : ℕ) : Finset ℕ :=
  (oddPrimeSupport n).filter fun p ↦ B < p

/-- The odd-valuation primes of `n` lying at or below `B`. -/
noncomputable def smallOddPrimeSupport (B n : ℕ) : Finset ℕ :=
  (oddPrimeSupport n).filter fun p ↦ p ≤ B

/-- The product of the odd-valuation primes of `n` lying strictly above `B`. -/
noncomputable def largeOddKernel (B n : ℕ) : ℕ :=
  (largeOddPrimeSupport B n).prod id

/-- The complementary squarefree part supported on primes at most `B`. -/
noncomputable def smallOddPart (B n : ℕ) : ℕ :=
  (smallOddPrimeSupport B n).prod id

@[simp]
theorem mem_largeOddPrimeSupport {B n p : ℕ} :
    p ∈ largeOddPrimeSupport B n ↔
      p ∈ oddPrimeSupport n ∧ B < p := by
  simp [largeOddPrimeSupport]

@[simp]
theorem mem_smallOddPrimeSupport {B n p : ℕ} :
    p ∈ smallOddPrimeSupport B n ↔
      p ∈ oddPrimeSupport n ∧ p ≤ B := by
  simp [smallOddPrimeSupport]

/-- The canonical odd support is exactly the support of the parity vector. -/
theorem mem_oddPrimeSupport_iff_parityVec_ne_zero {n p : ℕ} :
    p ∈ oddPrimeSupport n ↔ parityVec n p ≠ 0 := by
  simp only [oddPrimeSupport, oddFactorization, parityVec,
    Finsupp.mem_support_iff, Finsupp.mapRange_apply, ne_eq,
    ZMod.natCast_zmod_eq_zero_iff_dvd]
  constructor
  · intro h hp
    exact h (Nat.mod_eq_zero_of_dvd hp)
  · intro h hp
    exact h (Nat.dvd_of_mod_eq_zero hp)

/-- Membership in the large support, expressed directly through `parityVec`. -/
theorem mem_largeOddPrimeSupport_iff {B n p : ℕ} :
    p ∈ largeOddPrimeSupport B n ↔
      B < p ∧ parityVec n p ≠ 0 := by
  rw [mem_largeOddPrimeSupport, mem_oddPrimeSupport_iff_parityVec_ne_zero]
  exact and_comm

/-- Membership in the small support, expressed directly through `parityVec`. -/
theorem mem_smallOddPrimeSupport_iff {B n p : ℕ} :
    p ∈ smallOddPrimeSupport B n ↔
      p ≤ B ∧ parityVec n p ≠ 0 := by
  rw [mem_smallOddPrimeSupport, mem_oddPrimeSupport_iff_parityVec_ne_zero]
  exact and_comm

/-- Every coordinate in the odd support is a genuine prime. -/
theorem prime_of_mem_oddPrimeSupport {n p : ℕ}
    (hp : p ∈ oddPrimeSupport n) :
    p.Prime := by
  apply Nat.prime_of_mem_primeFactors
  exact Finsupp.support_mapRange hp

/-- Every prime in the large support lies above the cutoff. -/
theorem prime_and_large_of_mem_largeOddPrimeSupport {B n p : ℕ}
    (hp : p ∈ largeOddPrimeSupport B n) :
    p.Prime ∧ B < p := by
  exact ⟨prime_of_mem_oddPrimeSupport (mem_largeOddPrimeSupport.mp hp).1,
    (mem_largeOddPrimeSupport.mp hp).2⟩

/-- Every prime in the small support lies below the inclusive cutoff. -/
theorem prime_and_small_of_mem_smallOddPrimeSupport {B n p : ℕ}
    (hp : p ∈ smallOddPrimeSupport B n) :
    p.Prime ∧ p ≤ B := by
  exact ⟨prime_of_mem_oddPrimeSupport (mem_smallOddPrimeSupport.mp hp).1,
    (mem_smallOddPrimeSupport.mp hp).2⟩

/--
For a prime above the cutoff, a nonzero parity coordinate is equivalent to
membership in the large odd support.
-/
theorem parityVec_ne_zero_iff_mem_largeOddPrimeSupport
    {B n p : ℕ} (_hp : p.Prime) (hpB : B < p) :
    parityVec n p ≠ 0 ↔ p ∈ largeOddPrimeSupport B n := by
  rw [mem_largeOddPrimeSupport_iff]
  simp [hpB]

/-! ## Arithmetic properties of the support and its product -/

/-- Complete valuation characterization of the large support. -/
theorem mem_largeOddPrimeSupport_iff_prime_large_odd {B n p : ℕ} :
    p ∈ largeOddPrimeSupport B n ↔
      p.Prime ∧ B < p ∧ Odd (n.factorization p) := by
  constructor
  · intro hp
    exact ⟨(prime_and_large_of_mem_largeOddPrimeSupport hp).1,
      (prime_and_large_of_mem_largeOddPrimeSupport hp).2,
      ZMod.ne_zero_iff_odd.mp (by
        simpa only [parityVec_apply] using
          (mem_largeOddPrimeSupport_iff.mp hp).2)⟩
  · rintro ⟨_hpPrime, hpB, hpOdd⟩
    rw [mem_largeOddPrimeSupport_iff, parityVec_apply]
    exact ⟨hpB, ZMod.ne_zero_iff_odd.mpr hpOdd⟩

/-- Complete valuation characterization of the small support. -/
theorem mem_smallOddPrimeSupport_iff_prime_small_odd {B n p : ℕ} :
    p ∈ smallOddPrimeSupport B n ↔
      p.Prime ∧ p ≤ B ∧ Odd (n.factorization p) := by
  constructor
  · intro hp
    exact ⟨(prime_and_small_of_mem_smallOddPrimeSupport hp).1,
      (prime_and_small_of_mem_smallOddPrimeSupport hp).2,
      ZMod.ne_zero_iff_odd.mp (by
        simpa only [parityVec_apply] using
          (mem_smallOddPrimeSupport_iff.mp hp).2)⟩
  · rintro ⟨_hpPrime, hpB, hpOdd⟩
    rw [mem_smallOddPrimeSupport_iff, parityVec_apply]
    exact ⟨hpB, ZMod.ne_zero_iff_odd.mpr hpOdd⟩

/-- The large support is a finite subset of the prime factors of `n`. -/
theorem largeOddPrimeSupport_subset_primeFactors (B n : ℕ) :
    largeOddPrimeSupport B n ⊆ n.primeFactors := by
  intro p hp
  exact Finsupp.support_mapRange (mem_largeOddPrimeSupport.mp hp).1

/-- The small support is a finite subset of the prime factors of `n`. -/
theorem smallOddPrimeSupport_subset_primeFactors (B n : ℕ) :
    smallOddPrimeSupport B n ⊆ n.primeFactors := by
  intro p hp
  exact Finsupp.support_mapRange (mem_smallOddPrimeSupport.mp hp).1

/-- The large odd kernel never vanishes, including for `n = 0`. -/
theorem largeOddKernel_ne_zero (B n : ℕ) :
    largeOddKernel B n ≠ 0 := by
  rw [largeOddKernel, Finset.prod_ne_zero_iff]
  intro p hp
  exact (prime_and_large_of_mem_largeOddPrimeSupport hp).1.ne_zero

/-- The complementary small odd part never vanishes. -/
theorem smallOddPart_ne_zero (B n : ℕ) :
    smallOddPart B n ≠ 0 := by
  rw [smallOddPart, Finset.prod_ne_zero_iff]
  intro p hp
  exact (prime_and_small_of_mem_smallOddPrimeSupport hp).1.ne_zero

/--
The product of a finite set of primes remembers the set.  This is the
injectivity statement used implicitly whenever an odd kernel is identified
through its prime support.
-/
theorem primeFinset_product_injective
    {s t : Finset ℕ}
    (hs : ∀ p ∈ s, p.Prime)
    (ht : ∀ p ∈ t, p.Prime)
    (hprod : s.prod id = t.prod id) :
    s = t := by
  calc
    s = (s.prod id).primeFactors := (Nat.primeFactors_prod hs).symm
    _ = (t.prod id).primeFactors := congrArg Nat.primeFactors hprod
    _ = t := Nat.primeFactors_prod ht

/-- The defining support is recovered exactly from the kernel. -/
theorem primeFactors_largeOddKernel (B n : ℕ) :
    (largeOddKernel B n).primeFactors = largeOddPrimeSupport B n := by
  rw [largeOddKernel]
  exact Nat.primeFactors_prod fun p hp ↦
    (prime_and_large_of_mem_largeOddPrimeSupport hp).1

/-- The small odd support is recovered exactly from its product. -/
theorem primeFactors_smallOddPart (B n : ℕ) :
    (smallOddPart B n).primeFactors = smallOddPrimeSupport B n := by
  rw [smallOddPart]
  exact Nat.primeFactors_prod fun p hp ↦
    (prime_and_small_of_mem_smallOddPrimeSupport hp).1

/-- A finite product of distinct natural primes is squarefree. -/
private theorem squarefree_prod_primes
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (s.prod id) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert p s hp ih =>
      have hpPrime : p.Prime := hs p (Finset.mem_insert_self p s)
      have hsPrime : ∀ q ∈ s, q.Prime := by
        intro q hq
        exact hs q (Finset.mem_insert_of_mem hq)
      rw [Finset.prod_insert hp]
      apply (Nat.squarefree_mul ?_).mpr
      · exact ⟨hpPrime.squarefree, ih hsPrime⟩
      · apply Nat.Coprime.prod_right
        intro q hq
        apply (Nat.coprime_primes hpPrime (hsPrime q hq)).mpr
        intro hpq
        apply hp
        rwa [hpq]

/-- The large odd kernel is squarefree. -/
theorem largeOddKernel_squarefree (B n : ℕ) :
    Squarefree (largeOddKernel B n) := by
  rw [largeOddKernel]
  exact squarefree_prod_primes _ fun p hp ↦
    (prime_and_large_of_mem_largeOddPrimeSupport hp).1

/-- The complementary small odd part is squarefree. -/
theorem smallOddPart_squarefree (B n : ℕ) :
    Squarefree (smallOddPart B n) := by
  rw [smallOddPart]
  exact squarefree_prod_primes _ fun p hp ↦
    (prime_and_small_of_mem_smallOddPrimeSupport hp).1

/-- The large odd kernel divides the original integer. -/
theorem largeOddKernel_dvd (B n : ℕ) :
    largeOddKernel B n ∣ n := by
  rw [largeOddKernel]
  apply Finset.prod_primes_dvd n
  · intro p hp
    exact (prime_and_large_of_mem_largeOddPrimeSupport hp).1.prime
  · intro p hp
    exact Nat.dvd_of_mem_primeFactors
      (largeOddPrimeSupport_subset_primeFactors B n hp)

/-- The complementary small odd part also divides the original integer. -/
theorem smallOddPart_dvd (B n : ℕ) :
    smallOddPart B n ∣ n := by
  rw [smallOddPart]
  apply Finset.prod_primes_dvd n
  · intro p hp
    exact (prime_and_small_of_mem_smallOddPrimeSupport hp).1.prime
  · intro p hp
    exact Nat.dvd_of_mem_primeFactors
      (smallOddPrimeSupport_subset_primeFactors B n hp)

/-- Positivity of the large odd kernel in inequality form. -/
theorem one_le_largeOddKernel (B n : ℕ) :
    1 ≤ largeOddKernel B n :=
  Nat.one_le_iff_ne_zero.mpr (largeOddKernel_ne_zero B n)

/-- A positive integer bounds its large odd kernel. -/
theorem largeOddKernel_le {B n : ℕ} (hn : 0 < n) :
    largeOddKernel B n ≤ n :=
  Nat.le_of_dvd hn (largeOddKernel_dvd B n)

/-- The exact interval needed in the counting argument. -/
theorem largeOddKernel_mem_Icc {B n : ℕ} (hn : 0 < n) :
    largeOddKernel B n ∈ Finset.Icc 1 n := by
  exact Finset.mem_Icc.mpr ⟨one_le_largeOddKernel B n, largeOddKernel_le hn⟩

/-- The distinct-prime-factor count of the kernel is its support cardinality. -/
theorem cardDistinctFactors_largeOddKernel (B n : ℕ) :
    ArithmeticFunction.cardDistinctFactors (largeOddKernel B n) =
      (largeOddPrimeSupport B n).card := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset]
  change (largeOddKernel B n).primeFactors.card =
    (largeOddPrimeSupport B n).card
  rw [primeFactors_largeOddKernel]

/-! ## The small/large partition and canonical decomposition -/

/-- The small and large odd supports are disjoint. -/
theorem disjoint_smallOddPrimeSupport_largeOddPrimeSupport (B n : ℕ) :
    Disjoint (smallOddPrimeSupport B n) (largeOddPrimeSupport B n) := by
  rw [Finset.disjoint_left]
  intro p hpSmall hpLarge
  exact (Nat.not_lt_of_ge
    (prime_and_small_of_mem_smallOddPrimeSupport hpSmall).2)
    (prime_and_large_of_mem_largeOddPrimeSupport hpLarge).2

/-- Splitting at `B` exhausts the full odd-prime support. -/
theorem smallOddPrimeSupport_union_largeOddPrimeSupport (B n : ℕ) :
    smallOddPrimeSupport B n ∪ largeOddPrimeSupport B n =
      oddPrimeSupport n := by
  ext p
  simp only [Finset.mem_union, mem_smallOddPrimeSupport,
    mem_largeOddPrimeSupport]
  constructor
  · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
  · intro hp
    exact (le_or_lt p B).elim
      (fun hpB ↦ Or.inl ⟨hp, hpB⟩)
      (fun hpB ↦ Or.inr ⟨hp, hpB⟩)

/-- The products of the two pieces multiply back to the full odd part. -/
theorem smallOddPart_mul_largeOddKernel (B n : ℕ) :
    smallOddPart B n * largeOddKernel B n =
      (oddPrimeSupport n).prod id := by
  rw [smallOddPart, largeOddKernel,
    ← Finset.prod_union
      (disjoint_smallOddPrimeSupport_largeOddPrimeSupport B n),
    smallOddPrimeSupport_union_largeOddPrimeSupport]

/-- The small and large odd parts have disjoint prime support. -/
theorem smallOddPart_coprime_largeOddKernel (B n : ℕ) :
    (smallOddPart B n).Coprime (largeOddKernel B n) := by
  rw [smallOddPart, largeOddKernel]
  apply Nat.Coprime.prod_left
  intro p hpSmall
  apply Nat.Coprime.prod_right
  intro q hqLarge
  have hpData := prime_and_small_of_mem_smallOddPrimeSupport hpSmall
  have hqData := prime_and_large_of_mem_largeOddPrimeSupport hqLarge
  apply (Nat.coprime_primes hpData.1 hqData.1).mpr
  exact Nat.ne_of_lt (hpData.2.trans_lt hqData.2)

/--
The canonical decomposition used in Lemma 4.2:

`n = a² u r`,

where `a` is the canonical square part, `u` is squarefree and supported on
primes at most `B`, and `r = largeOddKernel B n` is squarefree and supported
on primes strictly above `B`.
-/
theorem canonical_largeOddKernel_decomposition
    {B n : ℕ} (hn : n ≠ 0) :
    n = canonicalSquarePart n ^ 2 *
        smallOddPart B n * largeOddKernel B n := by
  calc
    n = (oddPrimeSupport n).prod id * canonicalSquarePart n ^ 2 :=
      canonical_odd_mul_sq_decomposition hn
    _ = (smallOddPart B n * largeOddKernel B n) *
        canonicalSquarePart n ^ 2 := by
      rw [smallOddPart_mul_largeOddKernel]
    _ = canonicalSquarePart n ^ 2 *
        smallOddPart B n * largeOddKernel B n := by
      ac_rfl

/-- The canonical square part is nonzero whenever `n` is nonzero. -/
theorem canonicalSquarePart_ne_zero
    {n : ℕ} (hn : n ≠ 0) :
    canonicalSquarePart n ≠ 0 := by
  intro ha
  apply hn
  rw [canonical_largeOddKernel_decomposition (B := 0) hn, ha]
  simp

/-- A prime divides the large kernel exactly when it belongs to its support. -/
theorem prime_dvd_largeOddKernel_iff
    {B n p : ℕ} (hp : p.Prime) :
    p ∣ largeOddKernel B n ↔ p ∈ largeOddPrimeSupport B n := by
  rw [← primeFactors_largeOddKernel B n,
    Nat.mem_primeFactors_of_ne_zero (largeOddKernel_ne_zero B n)]
  simp [hp]

/--
The prime divisors of the kernel are exactly the primes above `B` occurring
to odd order in `n`.
-/
theorem prime_dvd_largeOddKernel_iff_large_odd
    {B n p : ℕ} (hp : p.Prime) :
    p ∣ largeOddKernel B n ↔
      B < p ∧ Odd (n.factorization p) := by
  rw [prime_dvd_largeOddKernel_iff hp,
    mem_largeOddPrimeSupport_iff_prime_large_odd]
  simp [hp]

/-- A prime divides the small odd part exactly when it belongs to its support. -/
theorem prime_dvd_smallOddPart_iff
    {B n p : ℕ} (hp : p.Prime) :
    p ∣ smallOddPart B n ↔ p ∈ smallOddPrimeSupport B n := by
  rw [← primeFactors_smallOddPart B n,
    Nat.mem_primeFactors_of_ne_zero (smallOddPart_ne_zero B n)]
  simp [hp]

/--
The prime divisors of the small odd part are exactly the odd-valuation primes
at or below `B`.
-/
theorem prime_dvd_smallOddPart_iff_small_odd
    {B n p : ℕ} (hp : p.Prime) :
    p ∣ smallOddPart B n ↔
      p ≤ B ∧ Odd (n.factorization p) := by
  rw [prime_dvd_smallOddPart_iff hp,
    mem_smallOddPrimeSupport_iff_prime_small_odd]
  simp [hp]

/-- Explicit factorization of the large kernel: every retained exponent is one. -/
theorem factorization_largeOddKernel (B n p : ℕ) :
    (largeOddKernel B n).factorization p =
      if p ∈ largeOddPrimeSupport B n then 1 else 0 := by
  by_cases hp : p ∈ largeOddPrimeSupport B n
  · rw [if_pos hp]
    exact Nat.factorization_eq_one_of_squarefree
      (largeOddKernel_squarefree B n)
      (prime_and_large_of_mem_largeOddPrimeSupport hp).1
      ((prime_dvd_largeOddKernel_iff
        (prime_and_large_of_mem_largeOddPrimeSupport hp).1).mpr hp)
  · rw [if_neg hp]
    apply Finsupp.not_mem_support_iff.mp
    rw [Nat.support_factorization, primeFactors_largeOddKernel]
    exact hp

/-- Explicit factorization of the small odd part. -/
theorem factorization_smallOddPart (B n p : ℕ) :
    (smallOddPart B n).factorization p =
      if p ∈ smallOddPrimeSupport B n then 1 else 0 := by
  by_cases hp : p ∈ smallOddPrimeSupport B n
  · rw [if_pos hp]
    exact Nat.factorization_eq_one_of_squarefree
      (smallOddPart_squarefree B n)
      (prime_and_small_of_mem_smallOddPrimeSupport hp).1
      ((prime_dvd_smallOddPart_iff
        (prime_and_small_of_mem_smallOddPrimeSupport hp).1).mpr hp)
  · rw [if_neg hp]
    apply Finsupp.not_mem_support_iff.mp
    rw [Nat.support_factorization, primeFactors_smallOddPart]
    exact hp

/-- The kernel is one exactly when its defining support is empty. -/
theorem largeOddKernel_eq_one_iff_support_eq_empty (B n : ℕ) :
    largeOddKernel B n = 1 ↔ largeOddPrimeSupport B n = ∅ := by
  constructor
  · intro hk
    have hs := primeFactors_largeOddKernel B n
    rw [hk] at hs
    simpa using hs.symm
  · intro hs
    simp [largeOddKernel, hs]

/--
The intrinsic defect predicate is equivalently the assertion that the large
odd kernel is one.
-/
theorem largeOddKernel_eq_one_iff_hDefective (B n : ℕ) :
    largeOddKernel B n = 1 ↔ HDefective B n := by
  rw [largeOddKernel_eq_one_iff_support_eq_empty]
  constructor
  · intro hs p hpPrime hpB
    by_contra hpParity
    have hpMem :=
      (parityVec_ne_zero_iff_mem_largeOddPrimeSupport hpPrime hpB).mp hpParity
    rw [hs] at hpMem
    exact Finset.not_mem_empty p hpMem
  · intro h
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro p hpMem
    have hpData := prime_and_large_of_mem_largeOddPrimeSupport hpMem
    exact (mem_largeOddPrimeSupport_iff.mp hpMem).2
      (h p hpData.1 hpData.2)

end LargeOddKernel
end PaperC
