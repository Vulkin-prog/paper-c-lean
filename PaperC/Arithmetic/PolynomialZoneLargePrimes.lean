import PaperC.Arithmetic.LaishramShoreyInput
import PaperC.Arithmetic.LargeOddKernel
import PaperC.Probability.BadStartMass
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.NormNum

/-!
# Large primes in the polynomial zone

This file formalizes the finite arithmetic part of the proof of Paper C,
Lemma 15.2.  It contains no bridge: the only published input is the
Laishram--Shorey proposition imported from
`PaperC.Arithmetic.LaishramShoreyInput`.

For a window `n, …, n+k-1`, we:

* extract the prime divisors above a cutoff `B`;
* prove that, when `k ≤ B`, every such prime divides a unique vertex;
* discard primes whose square divides their vertex;
* map every remaining prime to a non-`B`-defective vertex; and
* bound the multiplicity of that map by two under the manuscript's
  cubic size bound.
-/

namespace PaperC
namespace PolynomialZoneLargePrimes

open scoped BigOperators

open DefectivePredicate
open LaishramShoreyInput

noncomputable section

/-- Prime divisors of `Δ(n,k)` strictly larger than `B`. -/
def largePrimeFactors (B n k : ℕ) : Finset ℕ :=
  (consecutiveProduct n k).primeFactors.filter fun p ↦ B < p

/--
Large prime divisors whose square divides at least one member of the window.
These are a safe superset of the primes having even positive valuation in
the consecutive product.
-/
def squarefulLargePrimeFactors (B n k : ℕ) : Finset ℕ :=
  (largePrimeFactors B n k).filter fun p ↦
    ∃ i < k, p ^ 2 ∣ n + i

/--
The large prime divisors left after deleting the squareful ones.
Each of these occurs to exponent exactly one at its unique window vertex.
-/
def simpleLargePrimeFactors (B n k : ℕ) : Finset ℕ :=
  (largePrimeFactors B n k).filter fun p ↦
    ¬∃ i < k, p ^ 2 ∣ n + i

/-- Indices of the vertices which are not `B`-defective. -/
def nondefectiveWindowIndices (B n k : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range k).filter fun i ↦ ¬HDefective B (n + i)

/-- Simple large primes attached to a fixed window index. -/
def simpleLargePrimesAt (B n k i : ℕ) : Finset ℕ :=
  (simpleLargePrimeFactors B n k).filter fun p ↦ p ∣ n + i

/--
The chosen vertex at which a squareful large prime has square divisibility.
The value outside `squarefulLargePrimeFactors` is deliberately irrelevant.
-/
noncomputable def squarefulIndex (B n k p : ℕ) : ℕ :=
  if h : ∃ i < k, p ^ 2 ∣ n + i then Classical.choose h else 0

/-- The cofactor `a` in the manuscript identity `n+i = a p²`. -/
noncomputable def squarefulQuotient (B n k p : ℕ) : ℕ :=
  (n + squarefulIndex B n k p) / p ^ 2

@[simp]
theorem mem_largePrimeFactors {B n k p : ℕ} :
    p ∈ largePrimeFactors B n k ↔
      p ∈ (consecutiveProduct n k).primeFactors ∧ B < p := by
  simp [largePrimeFactors]

@[simp]
theorem mem_squarefulLargePrimeFactors {B n k p : ℕ} :
    p ∈ squarefulLargePrimeFactors B n k ↔
      p ∈ largePrimeFactors B n k ∧
        ∃ i < k, p ^ 2 ∣ n + i := by
  simp [squarefulLargePrimeFactors]

@[simp]
theorem mem_simpleLargePrimeFactors {B n k p : ℕ} :
    p ∈ simpleLargePrimeFactors B n k ↔
      p ∈ largePrimeFactors B n k ∧
        ¬∃ i < k, p ^ 2 ∣ n + i := by
  simp [simpleLargePrimeFactors]

@[simp]
theorem mem_nondefectiveWindowIndices {B n k i : ℕ} :
    i ∈ nondefectiveWindowIndices B n k ↔
      i < k ∧ ¬HDefective B (n + i) := by
  simp [nondefectiveWindowIndices]

@[simp]
theorem mem_simpleLargePrimesAt {B n k i p : ℕ} :
    p ∈ simpleLargePrimesAt B n k i ↔
      p ∈ simpleLargePrimeFactors B n k ∧ p ∣ n + i := by
  simp [simpleLargePrimesAt]

theorem squarefulIndex_spec
    {B n k p : ℕ} (hp : p ∈ squarefulLargePrimeFactors B n k) :
    squarefulIndex B n k p < k ∧
      p ^ 2 ∣ n + squarefulIndex B n k p := by
  have hex := (mem_squarefulLargePrimeFactors.mp hp).2
  simpa [squarefulIndex, hex] using Classical.choose_spec hex

theorem squareful_value_eq
    {B n k p : ℕ} (hp : p ∈ squarefulLargePrimeFactors B n k) :
    n + squarefulIndex B n k p =
      p ^ 2 * squarefulQuotient B n k p := by
  unfold squarefulQuotient
  exact (Nat.mul_div_cancel'
    (squarefulIndex_spec hp).2).symm

/-- Every large factor is prime and lies above the cutoff. -/
theorem prime_and_large_of_mem_largePrimeFactors
    {B n k p : ℕ} (hp : p ∈ largePrimeFactors B n k) :
    p.Prime ∧ B < p := by
  exact ⟨Nat.prime_of_mem_primeFactors (mem_largePrimeFactors.mp hp).1,
    (mem_largePrimeFactors.mp hp).2⟩

/-! ## Extracting the primes above `B` -/

/--
At most `π(B)` prime factors of an integer can lie at or below `B`.
Consequently removing them loses at most `π(B)` elements.
-/
theorem primeFactors_card_sub_primeCount_le_largePrimeFactors_card
    (B n k : ℕ) :
    (consecutiveProduct n k).primeFactors.card -
        PrimesUpTo.count B ≤
      (largePrimeFactors B n k).card := by
  classical
  let small :=
    (consecutiveProduct n k).primeFactors.filter fun p ↦ p ≤ B
  have hsmall :
      small ⊆ DefectCounting.smallPrimesUpTo B := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    exact DefectCounting.mem_smallPrimesUpTo.mpr
      ⟨Nat.prime_of_mem_primeFactors hpData.1, hpData.2⟩
  have hpartition :
      (consecutiveProduct n k).primeFactors =
        small ∪ largePrimeFactors B n k := by
    ext p
    by_cases hpB : p ≤ B
    · simp [small, largePrimeFactors, hpB,
        Nat.not_lt_of_ge hpB]
    · have hBp : B < p := Nat.lt_of_not_ge hpB
      simp [small, largePrimeFactors, hpB, hBp]
  have hcard :
      (consecutiveProduct n k).primeFactors.card ≤
        PrimesUpTo.count B + (largePrimeFactors B n k).card := by
    rw [hpartition]
    calc
      (small ∪ largePrimeFactors B n k).card ≤
          small.card + (largePrimeFactors B n k).card :=
        Finset.card_union_le _ _
      _ ≤ (DefectCounting.smallPrimesUpTo B).card +
          (largePrimeFactors B n k).card :=
        Nat.add_le_add_right (Finset.card_le_card hsmall) _
      _ = PrimesUpTo.count B +
          (largePrimeFactors B n k).card := by
        rw [← PrimeCountBridge.count_eq_card_smallPrimesUpTo]
  omega

/-- The exact finite lower bound on large primes obtained from Laishram--Shorey (2004). -/
theorem laishramShorey_largePrimeFactors
    (hLS : LaishramShoreyStatement)
    {n k : ℕ} (hk : 2 ≤ k) (hnk : k < n) :
    min
          (PrimesUpTo.count k +
            (3 * PrimesUpTo.count k) / 4 - 1)
          (PrimesUpTo.count (2 * k) - 1) -
        PrimesUpTo.count k ≤
      (largePrimeFactors k n k).card := by
  have htotal :=
    manuscript_bound_of_laishramShorey hLS hk hnk
  have hremove :=
    primeFactors_card_sub_primeCount_le_largePrimeFactors_card k n k
  omega

/-! ## Unique divisible vertex -/

/--
A prime larger than the diameter of a consecutive window divides at most one
member of that window.
-/
theorem unique_index_of_large_prime_dvd
    {B n k p i j : ℕ}
    (hkB : k ≤ B) (hpB : B < p)
    (hi : i < k) (hj : j < k)
    (hpi : p ∣ n + i) (hpj : p ∣ n + j) :
    i = j := by
  have hcong_i : n + i ≡ 0 [MOD p] := hpi.modEq_zero_nat
  have hcong_j : n + j ≡ 0 [MOD p] := hpj.modEq_zero_nat
  have hcong_sum : n + i ≡ n + j [MOD p] :=
    hcong_i.trans hcong_j.symm
  have hcong : i ≡ j [MOD p] :=
    (Nat.ModEq.refl n).add_left_cancel hcong_sum
  exact hcong.eq_of_lt_of_lt
    (lt_trans (lt_of_lt_of_le hi hkB) hpB)
    (lt_trans (lt_of_lt_of_le hj hkB) hpB)

/--
Every large prime divisor of the consecutive product divides a unique
window vertex.
-/
theorem existsUnique_index_dvd_of_mem_largePrimeFactors
    {B n k p : ℕ} (hkB : k ≤ B)
    (hp : p ∈ largePrimeFactors B n k) :
    ∃! i : ℕ, i < k ∧ p ∣ n + i := by
  have hpPrime :=
    (prime_and_large_of_mem_largePrimeFactors hp).1
  have hpProd :
      p ∣ consecutiveProduct n k :=
    Nat.dvd_of_mem_primeFactors (mem_largePrimeFactors.mp hp).1
  obtain ⟨i, hi, hpi⟩ :=
    (hpPrime.prime.dvd_finsetProd_iff
      (fun i : ℕ ↦ n + i)).mp hpProd
  have hik : i < k := Finset.mem_range.mp hi
  refine ⟨i, ⟨hik, hpi⟩, ?_⟩
  intro j hj
  exact unique_index_of_large_prime_dvd hkB
    (prime_and_large_of_mem_largePrimeFactors hp).2
    hj.1 hik hj.2 hpi

/-! ## Simple primes give nondefective vertices -/

/--
If a simple large prime divides a window vertex, its valuation at that
vertex is exactly one.
-/
theorem factorization_eq_one_of_mem_simpleLargePrimeFactors_of_dvd
    {B n k p i : ℕ}
    (hn : 0 < n)
    (hp : p ∈ simpleLargePrimeFactors B n k)
    (hi : i < k) (hpi : p ∣ n + i) :
    (n + i).factorization p = 1 := by
  have hpPrime :=
    (prime_and_large_of_mem_largePrimeFactors
      (mem_simpleLargePrimeFactors.mp hp).1).1
  have hvalue : n + i ≠ 0 := by omega
  have hone :
      1 ≤ (n + i).factorization p :=
    (hpPrime.dvd_iff_one_le_factorization hvalue).mp hpi
  have hnotSquare :
      ¬p ^ 2 ∣ n + i := by
    intro hsquare
    exact (mem_simpleLargePrimeFactors.mp hp).2
      ⟨i, hi, hsquare⟩
  have hnotTwo :
      ¬2 ≤ (n + i).factorization p := by
    intro htwo
    exact hnotSquare
      ((hpPrime.pow_dvd_iff_le_factorization hvalue).mpr htwo)
  omega

/-- A simple large prime makes its unique vertex non-`B`-defective. -/
theorem not_hDefective_of_mem_simpleLargePrimeFactors_of_dvd
    {B n k p i : ℕ}
    (hn : 0 < n)
    (hp : p ∈ simpleLargePrimeFactors B n k)
    (hi : i < k) (hpi : p ∣ n + i) :
    ¬HDefective B (n + i) := by
  have hpLarge :=
    prime_and_large_of_mem_largePrimeFactors
      (mem_simpleLargePrimeFactors.mp hp).1
  have hfactor :=
    factorization_eq_one_of_mem_simpleLargePrimeFactors_of_dvd
      hn hp hi hpi
  intro hdef
  have hzero := hdef p hpLarge.1 hpLarge.2
  simp [parityVec_apply, hfactor] at hzero

/--
Every simple large prime belongs to the fiber of a nondefective vertex.
-/
theorem simpleLargePrimeFactors_subset_nondefective_biUnion
    {B n k : ℕ} (hn : 0 < n) (hkB : k ≤ B) :
    simpleLargePrimeFactors B n k ⊆
      (nondefectiveWindowIndices B n k).biUnion
        (simpleLargePrimesAt B n k) := by
  intro p hp
  obtain ⟨i, hi, hpi⟩ :=
    (existsUnique_index_dvd_of_mem_largePrimeFactors hkB
      (mem_simpleLargePrimeFactors.mp hp).1).exists
  rw [Finset.mem_biUnion]
  refine ⟨i, mem_nondefectiveWindowIndices.mpr
    ⟨hi, not_hDefective_of_mem_simpleLargePrimeFactors_of_dvd
      hn hp hi hpi⟩, ?_⟩
  exact mem_simpleLargePrimesAt.mpr ⟨hp, hpi⟩

/-! ## At most two large primes per vertex -/

/--
A vertex below `B³` has at most two distinct prime divisors above `B`.
This is the last elementary multiplicity estimate in the proof of
Lemma 15.2.
-/
theorem card_simpleLargePrimesAt_le_two
    {B n k i : ℕ}
    (hn : 0 < n)
    (hupper : n + i < B ^ 3) :
    (simpleLargePrimesAt B n k i).card ≤ 2 := by
  by_contra hcard
  have hthree : 2 < (simpleLargePrimesAt B n k i).card :=
    Nat.lt_of_not_ge hcard
  rw [Finset.two_lt_card] at hthree
  obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩ := hthree
  have hpData := mem_simpleLargePrimesAt.mp hp
  have hqData := mem_simpleLargePrimesAt.mp hq
  have hrData := mem_simpleLargePrimesAt.mp hr
  have hpLarge :=
    prime_and_large_of_mem_largePrimeFactors
      (mem_simpleLargePrimeFactors.mp hpData.1).1
  have hqLarge :=
    prime_and_large_of_mem_largePrimeFactors
      (mem_simpleLargePrimeFactors.mp hqData.1).1
  have hrLarge :=
    prime_and_large_of_mem_largePrimeFactors
      (mem_simpleLargePrimeFactors.mp hrData.1).1
  have hprodDvd :
      ({p, q, r} : Finset ℕ).prod id ∣ n + i := by
    apply Finset.prod_primes_dvd (n + i)
    · intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with (rfl | rfl | rfl)
      · exact hpLarge.1.prime
      · exact hqLarge.1.prime
      · exact hrLarge.1.prime
    · intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with (rfl | rfl | rfl)
      · exact hpData.2
      · exact hqData.2
      · exact hrData.2
  have hprodEq :
      ({p, q, r} : Finset ℕ).prod id = p * q * r := by
    simp [hpq, hpr, hqr, mul_assoc]
  have hvaluePos : 0 < n + i := by omega
  have hprodLe : p * q * r ≤ n + i := by
    rw [← hprodEq]
    exact Nat.le_of_dvd hvaluePos hprodDvd
  have hpqLower : B * B < p * q :=
    Nat.mul_lt_mul'' hpLarge.2 hqLarge.2
  have hprodLower : B ^ 3 < p * q * r := by
    have :=
      Nat.mul_lt_mul'' hpqLower hrLarge.2
    simpa [pow_succ, mul_assoc] using this
  omega

/-! ## Removing at most three squareful primes -/

/-- The cofactor `a` in `n+i = p²a` is positive on a positive window. -/
theorem squarefulQuotient_pos
    {B n k p : ℕ}
    (hn : 0 < n)
    (hp : p ∈ squarefulLargePrimeFactors B n k) :
    0 < squarefulQuotient B n k p := by
  have hvalue : 0 < n + squarefulIndex B n k p := by omega
  rw [squareful_value_eq hp] at hvalue
  by_contra hquotient
  have hzero :
      squarefulQuotient B n k p = 0 :=
    Nat.eq_zero_of_not_pos hquotient
  simp [hzero] at hvalue

/--
Under the manuscript's quadratic upper bound, every squareful cofactor
belongs to `{1,2,3}`.
-/
theorem squarefulQuotient_le_three
    {B n k p : ℕ}
    (hupper : ∀ i < k, n + i ≤ 3 * B ^ 2)
    (hp : p ∈ squarefulLargePrimeFactors B n k) :
    squarefulQuotient B n k p ≤ 3 := by
  have hpLarge :=
    prime_and_large_of_mem_largePrimeFactors
      (mem_squarefulLargePrimeFactors.mp hp).1
  have hpPow : B ^ 2 ≤ p ^ 2 :=
    Nat.pow_le_pow_left hpLarge.2.le 2
  have hvalue :
      n + squarefulIndex B n k p ≤ 3 * p ^ 2 :=
    (hupper _ (squarefulIndex_spec hp).1).trans
      (Nat.mul_le_mul_left 3 hpPow)
  rw [squareful_value_eq hp] at hvalue
  have hscaled :
      p ^ 2 * squarefulQuotient B n k p ≤ p ^ 2 * 3 := by
    simpa [mul_comm] using hvalue
  exact Nat.le_of_mul_le_mul_left hscaled
    (pow_pos hpLarge.1.pos 2)

/--
Two distinct squareful primes cannot have the same cofactor: two labels in a
window of diameter `< k` cannot differ by `a(q²-p²)` when `p,q>B≥k`.
-/
theorem squarefulQuotient_injOn
    {B n k : ℕ}
    (hn : 0 < n)
    (hkB : k ≤ B) :
    Set.InjOn (squarefulQuotient B n k)
      (squarefulLargePrimeFactors B n k : Set ℕ) := by
  intro p hp q hq heq
  by_contra hpq
  have hpFin : p ∈ squarefulLargePrimeFactors B n k := hp
  have hqFin : q ∈ squarefulLargePrimeFactors B n k := hq
  have hpLarge :=
    prime_and_large_of_mem_largePrimeFactors
      (mem_squarefulLargePrimeFactors.mp hpFin).1
  have hqLarge :=
    prime_and_large_of_mem_largePrimeFactors
      (mem_squarefulLargePrimeFactors.mp hqFin).1
  have haPos :=
    squarefulQuotient_pos hn hpFin
  have hpValue := squareful_value_eq hpFin
  have hqValue := squareful_value_eq hqFin
  rw [← heq] at hqValue
  rcases lt_or_gt_of_ne hpq with hpqLt | hqpLt
  · have hlabels :
        n + squarefulIndex B n k q <
          n + squarefulIndex B n k p + k := by
      have hpIndex := (squarefulIndex_spec hpFin).1
      have hqIndex := (squarefulIndex_spec hqFin).1
      omega
    rw [hpValue, hqValue] at hlabels
    have hsq :
        p ^ 2 + k ≤ q ^ 2 := by
      nlinarith
    have hkMul :
        k ≤ squarefulQuotient B n k p * k := by
      simpa [one_mul, mul_comm] using
        Nat.mul_le_mul_right k haPos
    have hgrowth :
        p ^ 2 * squarefulQuotient B n k p + k ≤
          q ^ 2 * squarefulQuotient B n k p := by
      calc
        p ^ 2 * squarefulQuotient B n k p + k ≤
            p ^ 2 * squarefulQuotient B n k p +
              squarefulQuotient B n k p * k :=
          Nat.add_le_add_left hkMul _
        _ = squarefulQuotient B n k p * (p ^ 2 + k) := by
          ring
        _ ≤ squarefulQuotient B n k p * q ^ 2 :=
          Nat.mul_le_mul_left _ hsq
        _ = q ^ 2 * squarefulQuotient B n k p := by
          ring
    omega
  · have hlabels :
        n + squarefulIndex B n k p <
          n + squarefulIndex B n k q + k := by
      have hpIndex := (squarefulIndex_spec hpFin).1
      have hqIndex := (squarefulIndex_spec hqFin).1
      omega
    rw [hpValue, hqValue] at hlabels
    have hsq :
        q ^ 2 + k ≤ p ^ 2 := by
      nlinarith
    have hkMul :
        k ≤ squarefulQuotient B n k p * k := by
      simpa [one_mul, mul_comm] using
        Nat.mul_le_mul_right k haPos
    have hgrowth :
        q ^ 2 * squarefulQuotient B n k p + k ≤
          p ^ 2 * squarefulQuotient B n k p := by
      calc
        q ^ 2 * squarefulQuotient B n k p + k ≤
            q ^ 2 * squarefulQuotient B n k p +
              squarefulQuotient B n k p * k :=
          Nat.add_le_add_left hkMul _
        _ = squarefulQuotient B n k p * (q ^ 2 + k) := by
          ring
        _ ≤ squarefulQuotient B n k p * p ^ 2 :=
          Nat.mul_le_mul_left _ hsq
        _ = p ^ 2 * squarefulQuotient B n k p := by
          ring
    omega

/--
The squareful exceptional set has cardinality at most three, exactly as in
the manuscript proof.
-/
theorem card_squarefulLargePrimeFactors_le_three
    {B n k : ℕ}
    (hn : 0 < n)
    (hkB : k ≤ B)
    (hupper : ∀ i < k, n + i ≤ 3 * B ^ 2) :
    (squarefulLargePrimeFactors B n k).card ≤ 3 := by
  let image :=
    (squarefulLargePrimeFactors B n k).image
      (squarefulQuotient B n k)
  have hsubset : image ⊆ Finset.Icc 1 3 := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_Icc.mpr
      ⟨squarefulQuotient_pos hn hp,
        squarefulQuotient_le_three hupper hp⟩
  calc
    (squarefulLargePrimeFactors B n k).card =
        image.card := by
      symm
      exact Finset.card_image_of_injOn
        (squarefulQuotient_injOn hn hkB)
    _ ≤ (Finset.Icc 1 3).card :=
      Finset.card_le_card hsubset
    _ = 3 := by simp

/--
The large-prime set is partitioned into the squareful exceptional primes and
the simple primes.
-/
theorem card_squareful_add_card_simple
    (B n k : ℕ) :
    (squarefulLargePrimeFactors B n k).card +
        (simpleLargePrimeFactors B n k).card =
      (largePrimeFactors B n k).card := by
  classical
  simpa [squarefulLargePrimeFactors, simpleLargePrimeFactors] using
    (Finset.card_filter_add_card_filter_not
      (s := largePrimeFactors B n k)
      (p := fun p ↦ ∃ i < k, p ^ 2 ∣ n + i))

/--
Counting fibers of the prime-to-vertex map gives the factor `1/2` in the
manuscript: the number of simple large primes is at most twice the number of
nondefective vertices.
-/
theorem card_simpleLargePrimeFactors_le_two_mul_nondefective
    {B n k : ℕ}
    (hn : 0 < n)
    (hkB : k ≤ B)
    (hupper : ∀ i < k, n + i < B ^ 3) :
    (simpleLargePrimeFactors B n k).card ≤
      2 * (nondefectiveWindowIndices B n k).card := by
  have hcover :=
    simpleLargePrimeFactors_subset_nondefective_biUnion hn hkB
  calc
    (simpleLargePrimeFactors B n k).card ≤
        ((nondefectiveWindowIndices B n k).biUnion
          (simpleLargePrimesAt B n k)).card :=
      Finset.card_le_card hcover
    _ ≤ (nondefectiveWindowIndices B n k).card * 2 := by
      apply Finset.card_biUnion_le_card_mul
      intro i hi
      exact card_simpleLargePrimesAt_le_two hn
        (hupper i (mem_nondefectiveWindowIndices.mp hi).1)
    _ = 2 * (nondefectiveWindowIndices B n k).card := by
      omega

/--
After deleting at most three squareful primes and accounting for at most two
remaining large primes per vertex, at least `(R-3)/2` vertices are
nondefective, where `R` is the number of large prime factors.
-/
theorem largePrimeFactors_sub_three_div_two_le_nondefective
    {B n k : ℕ}
    (hn : 0 < n)
    (hkB : k ≤ B)
    (hquadratic : ∀ i < k, n + i ≤ 3 * B ^ 2)
    (hcubic : ∀ i < k, n + i < B ^ 3) :
    ((largePrimeFactors B n k).card - 3) / 2 ≤
      (nondefectiveWindowIndices B n k).card := by
  have hsquare :=
    card_squarefulLargePrimeFactors_le_three hn hkB hquadratic
  have hsimple :=
    card_simpleLargePrimeFactors_le_two_mul_nondefective
      hn hkB hcubic
  have hpartition := card_squareful_add_card_simple B n k
  apply Nat.div_le_of_le_mul
  omega

/--
Finite conclusion of the Laishram--Shorey part of Lemma 15.2.  No
asymptotic estimate is hidden here: the exact prime-counting rank from the
published theorem appears on the left.
-/
theorem laishramShorey_nondefectiveWindow_lower_bound
    (hLS : LaishramShoreyStatement)
    {n k : ℕ}
    (hn : 0 < n)
    (hk : 2 ≤ k)
    (hnk : k < n)
    (hquadratic : ∀ i < k, n + i ≤ 3 * k ^ 2)
    (hcubic : ∀ i < k, n + i < k ^ 3) :
    (min
          (PrimesUpTo.count k +
            (3 * PrimesUpTo.count k) / 4 - 1)
          (PrimesUpTo.count (2 * k) - 1) -
        PrimesUpTo.count k - 3) / 2 ≤
      (nondefectiveWindowIndices k n k).card := by
  have hlarge :=
    laishramShorey_largePrimeFactors hLS hk hnk
  have hfinite :=
    largePrimeFactors_sub_three_div_two_le_nondefective
      hn le_rfl hquadratic hcubic
  exact (Nat.div_le_div_right
    (Nat.sub_le_sub_right hlarge 3)).trans hfinite

end

end PolynomialZoneLargePrimes
end PaperC
