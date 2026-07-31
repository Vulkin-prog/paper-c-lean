import PaperC.Arithmetic.ChebyshevPrimeCount
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Explicit reciprocal-prime sums on dyadic intervals

This file derives the two finite estimates needed in Paper C, Lemma 7.2,
from the elementary Chebyshev bound already proved in
`ChebyshevPrimeCount`:

* on `(B, B * 2^K]`, the sum of `1 / p` is at most
  `14 K / log₂ B`;
* on the same interval, the sum of `1 / p²` is at most
  `28 / (B log₂ B)`, uniformly in `K`.

All sums take values in `ℚ`, the coefficient field used by the CRT
certificate summation in Lemma 7.1.  The proofs are finite: the prime
interval is split into disjoint dyadic shells, each shell is controlled by
`log₂ H * π(H) ≤ 7H`, and the reciprocal-square estimate is closed by a
finite geometric sum.
-/

namespace PaperC
namespace DyadicPrimeReciprocalSums

open Finset
open scoped BigOperators

/-- The finite set of primes in the half-open interval `(B, X]`. -/
def primesBetween (B X : ℕ) : Finset ℕ :=
  (DefectCounting.smallPrimesUpTo X).filter fun p ↦ B < p

@[simp]
theorem mem_primesBetween {B X p : ℕ} :
    p ∈ primesBetween B X ↔ p.Prime ∧ B < p ∧ p ≤ X := by
  simp only [primesBetween, Finset.mem_filter,
    DefectCounting.mem_smallPrimesUpTo]
  aesop

@[simp]
theorem primesBetween_self (B : ℕ) :
    primesBetween B B = ∅ := by
  ext p
  simp

/-- The dyadic prime interval `(B, B * 2^K]`. -/
def dyadicPrimes (B K : ℕ) : Finset ℕ :=
  primesBetween B (B * 2 ^ K)

@[simp]
theorem mem_dyadicPrimes {B K p : ℕ} :
    p ∈ dyadicPrimes B K ↔
      p.Prime ∧ B < p ∧ p ≤ B * 2 ^ K := by
  simp [dyadicPrimes]

private theorem two_le_log_two {B : ℕ} (hB : 4 ≤ B) :
    2 ≤ Nat.log 2 B := by
  apply Nat.le_log_of_pow_le (by norm_num)
  norm_num
  exact hB

private theorem primesBetween_subset_smallPrimesUpTo (B X : ℕ) :
    primesBetween B X ⊆ DefectCounting.smallPrimesUpTo X :=
  Finset.filter_subset _ _

private theorem card_primesBetween_le_count (B X : ℕ) :
    (primesBetween B X).card ≤ PrimesUpTo.count X := by
  calc
    (primesBetween B X).card ≤
        (DefectCounting.smallPrimesUpTo X).card :=
      Finset.card_le_card (primesBetween_subset_smallPrimesUpTo B X)
    _ = PrimesUpTo.count X :=
      (PrimeCountBridge.count_eq_card_smallPrimesUpTo X).symm

/--
The Chebyshev cardinality estimate for one shell `(Y, 2Y]`, with the
logarithm frozen at any smaller base scale `B`.
-/
private theorem log_mul_card_shell_le
    {B Y : ℕ} (hB : 4 ≤ B) (hBY : B ≤ Y) :
    Nat.log 2 B * (primesBetween Y (2 * Y)).card ≤ 14 * Y := by
  have hlog :
      Nat.log 2 B ≤ Nat.log 2 (2 * Y) :=
    Nat.log_mono_right (hBY.trans (by omega))
  have hcard :
      (primesBetween Y (2 * Y)).card ≤
        PrimesUpTo.count (2 * Y) :=
    card_primesBetween_le_count Y (2 * Y)
  calc
    Nat.log 2 B * (primesBetween Y (2 * Y)).card
        ≤ Nat.log 2 (2 * Y) * PrimesUpTo.count (2 * Y) :=
      Nat.mul_le_mul hlog hcard
    _ ≤ 7 * (2 * Y) :=
      ChebyshevPrimeCount.log_mul_count_le_seven_mul
        (H := 2 * Y) (by omega)
    _ = 14 * Y := by omega

/-- The reciprocal sum over one dyadic shell. -/
private theorem sum_inv_shell_le
    {B Y : ℕ} (hB : 4 ≤ B) (hBY : B ≤ Y) :
    (∑ p ∈ primesBetween Y (2 * Y), 1 / (p : ℚ)) ≤
      14 / (Nat.log 2 B : ℚ) := by
  have hYpos : (0 : ℚ) < (Y : ℚ) := by
    exact_mod_cast (show 0 < Y by omega)
  have hlogPos : (0 : ℚ) < (Nat.log 2 B : ℚ) := by
    exact_mod_cast (show 0 < Nat.log 2 B by
      have := two_le_log_two hB
      omega)
  have hterm :
      ∀ p ∈ primesBetween Y (2 * Y),
        1 / (p : ℚ) ≤ 1 / (Y : ℚ) := by
    intro p hp
    apply one_div_le_one_div_of_le hYpos
    exact_mod_cast (mem_primesBetween.mp hp).2.1.le
  have hsum :
      (∑ p ∈ primesBetween Y (2 * Y), 1 / (p : ℚ)) ≤
        ((primesBetween Y (2 * Y)).card : ℚ) / (Y : ℚ) := by
    calc
      (∑ p ∈ primesBetween Y (2 * Y), 1 / (p : ℚ))
          ≤ ∑ _p ∈ primesBetween Y (2 * Y), 1 / (Y : ℚ) :=
        Finset.sum_le_sum hterm
      _ = ((primesBetween Y (2 * Y)).card : ℚ) /
          (Y : ℚ) := by
        simp [div_eq_mul_inv]
  have hcardQ :
      (Nat.log 2 B : ℚ) *
          ((primesBetween Y (2 * Y)).card : ℚ) ≤
        14 * (Y : ℚ) := by
    exact_mod_cast log_mul_card_shell_le hB hBY
  calc
    (∑ p ∈ primesBetween Y (2 * Y), 1 / (p : ℚ))
        ≤ ((primesBetween Y (2 * Y)).card : ℚ) / (Y : ℚ) :=
      hsum
    _ ≤ 14 / (Nat.log 2 B : ℚ) := by
      rw [div_le_div_iff₀ hYpos hlogPos]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hcardQ

/-- The reciprocal-square sum over one dyadic shell. -/
private theorem sum_inv_sq_shell_le
    {B Y : ℕ} (hB : 4 ≤ B) (hBY : B ≤ Y) :
    (∑ p ∈ primesBetween Y (2 * Y), 1 / (p : ℚ) ^ 2) ≤
      14 / ((Y : ℚ) * (Nat.log 2 B : ℚ)) := by
  have hYpos : (0 : ℚ) < (Y : ℚ) := by
    exact_mod_cast (show 0 < Y by omega)
  have hlogPos : (0 : ℚ) < (Nat.log 2 B : ℚ) := by
    exact_mod_cast (show 0 < Nat.log 2 B by
      have := two_le_log_two hB
      omega)
  have hterm :
      ∀ p ∈ primesBetween Y (2 * Y),
        1 / (p : ℚ) ^ 2 ≤ 1 / (Y : ℚ) ^ 2 := by
    intro p hp
    apply one_div_le_one_div_of_le (sq_pos_of_pos hYpos)
    have hpY : (Y : ℚ) ≤ (p : ℚ) := by
      exact_mod_cast (mem_primesBetween.mp hp).2.1.le
    nlinarith
  have hsum :
      (∑ p ∈ primesBetween Y (2 * Y), 1 / (p : ℚ) ^ 2) ≤
        ((primesBetween Y (2 * Y)).card : ℚ) /
          (Y : ℚ) ^ 2 := by
    calc
      (∑ p ∈ primesBetween Y (2 * Y), 1 / (p : ℚ) ^ 2)
          ≤ ∑ _p ∈ primesBetween Y (2 * Y),
              1 / (Y : ℚ) ^ 2 :=
        Finset.sum_le_sum hterm
      _ = ((primesBetween Y (2 * Y)).card : ℚ) /
          (Y : ℚ) ^ 2 := by
        simp [div_eq_mul_inv]
  have hcardQ :
      (Nat.log 2 B : ℚ) *
          ((primesBetween Y (2 * Y)).card : ℚ) ≤
        14 * (Y : ℚ) := by
    exact_mod_cast log_mul_card_shell_le hB hBY
  calc
    (∑ p ∈ primesBetween Y (2 * Y), 1 / (p : ℚ) ^ 2)
        ≤ ((primesBetween Y (2 * Y)).card : ℚ) /
          (Y : ℚ) ^ 2 :=
      hsum
    _ ≤ 14 / ((Y : ℚ) * (Nat.log 2 B : ℚ)) := by
      rw [div_le_div_iff₀ (sq_pos_of_pos hYpos)
        (mul_pos hYpos hlogPos)]
      calc
        ((primesBetween Y (2 * Y)).card : ℚ) *
            ((Y : ℚ) * (Nat.log 2 B : ℚ)) =
            (Y : ℚ) *
              ((Nat.log 2 B : ℚ) *
                ((primesBetween Y (2 * Y)).card : ℚ)) := by ring
        _ ≤ (Y : ℚ) * (14 * (Y : ℚ)) :=
          mul_le_mul_of_nonneg_left hcardQ hYpos.le
        _ = 14 * (Y : ℚ) ^ 2 := by ring

private theorem primesBetween_double_eq_union
    {B Y : ℕ} (hBY : B ≤ Y) :
    primesBetween B (2 * Y) =
      primesBetween B Y ∪ primesBetween Y (2 * Y) := by
  ext p
  simp only [mem_primesBetween, Finset.mem_union]
  constructor
  · rintro ⟨hp, hBp, hp2Y⟩
    by_cases hpY : p ≤ Y
    · exact Or.inl ⟨hp, hBp, hpY⟩
    · exact Or.inr ⟨hp, lt_of_not_ge hpY, hp2Y⟩
  · rintro (hp | hp)
    · exact ⟨hp.1, hp.2.1, hp.2.2.trans (by omega)⟩
    · exact ⟨hp.1, hBY.trans_lt hp.2.1, hp.2.2⟩

private theorem disjoint_primesBetween_adjacent (B Y : ℕ) :
    Disjoint (primesBetween B Y) (primesBetween Y (2 * Y)) := by
  rw [Finset.disjoint_left]
  intro p hp₁ hp₂
  have hpY := (mem_primesBetween.mp hp₁).2.2
  have hYp := (mem_primesBetween.mp hp₂).2.1
  omega

private theorem dyadicPrimes_succ_eq_union (B K : ℕ) :
    dyadicPrimes B (K + 1) =
      dyadicPrimes B K ∪
        primesBetween (B * 2 ^ K) (2 * (B * 2 ^ K)) := by
  have hscale : B ≤ B * 2 ^ K :=
    Nat.le_mul_of_pos_right B (by positivity)
  unfold dyadicPrimes
  rw [show B * 2 ^ (K + 1) = 2 * (B * 2 ^ K) by
    rw [pow_succ]
    ring]
  exact primesBetween_double_eq_union hscale

private theorem disjoint_dyadicPrimes_shell (B K : ℕ) :
    Disjoint (dyadicPrimes B K)
      (primesBetween (B * 2 ^ K) (2 * (B * 2 ^ K))) := by
  unfold dyadicPrimes
  exact disjoint_primesBetween_adjacent B (B * 2 ^ K)

/--
Explicit first reciprocal-prime estimate on `(B, B * 2^K]`.
-/
theorem sum_inv_dyadicPrimes_le
    (B K : ℕ) (hB : 4 ≤ B) :
    (∑ p ∈ dyadicPrimes B K, 1 / (p : ℚ)) ≤
      14 * (K : ℚ) / (Nat.log 2 B : ℚ) := by
  induction K with
  | zero =>
      simp [dyadicPrimes]
  | succ K ih =>
      have hscale : B ≤ B * 2 ^ K :=
        Nat.le_mul_of_pos_right B (by positivity)
      rw [show K + 1 = Nat.succ K by omega,
        dyadicPrimes_succ_eq_union,
        Finset.sum_union (disjoint_dyadicPrimes_shell B K)]
      have hshell :=
        sum_inv_shell_le hB hscale
      calc
        (∑ p ∈ dyadicPrimes B K, 1 / (p : ℚ)) +
              ∑ p ∈ primesBetween (B * 2 ^ K)
                (2 * (B * 2 ^ K)), 1 / (p : ℚ)
            ≤ 14 * (K : ℚ) / (Nat.log 2 B : ℚ) +
                14 / (Nat.log 2 B : ℚ) :=
          add_le_add ih hshell
        _ = 14 * (Nat.succ K : ℚ) /
            (Nat.log 2 B : ℚ) := by
          push_cast
          ring

private theorem sum_inv_two_pow_le_two (K : ℕ) :
    (∑ k ∈ Finset.range K, 1 / ((2 ^ k : ℕ) : ℚ)) ≤ 2 := by
  have hgeom :
      (∑ k ∈ Finset.range K, (1 / 2 : ℚ) ^ k) =
        (((1 / 2 : ℚ) ^ K - 1) / ((1 / 2 : ℚ) - 1)) :=
    geom_sum_eq (by norm_num) K
  have hpowNonneg : (0 : ℚ) ≤ (1 / 2 : ℚ) ^ K := by positivity
  calc
    (∑ k ∈ Finset.range K, 1 / ((2 ^ k : ℕ) : ℚ)) =
        ∑ k ∈ Finset.range K, (1 / 2 : ℚ) ^ k := by
      apply Finset.sum_congr rfl
      intro k hk
      push_cast
      rw [one_div_pow]
    _ = (((1 / 2 : ℚ) ^ K - 1) /
        ((1 / 2 : ℚ) - 1)) := hgeom
    _ ≤ 2 := by
      norm_num
      linarith

private theorem sum_inv_sq_dyadicPrimes_le_geometric
    (B K : ℕ) (hB : 4 ≤ B) :
    (∑ p ∈ dyadicPrimes B K, 1 / (p : ℚ) ^ 2) ≤
      (14 / ((B : ℚ) * (Nat.log 2 B : ℚ))) *
        ∑ k ∈ Finset.range K, 1 / ((2 ^ k : ℕ) : ℚ) := by
  induction K with
  | zero =>
      simp [dyadicPrimes]
  | succ K ih =>
      have hscale : B ≤ B * 2 ^ K :=
        Nat.le_mul_of_pos_right B (by positivity)
      have hBpos : (0 : ℚ) < (B : ℚ) := by
        exact_mod_cast (show 0 < B by omega)
      have hlogPos : (0 : ℚ) < (Nat.log 2 B : ℚ) := by
        exact_mod_cast (show 0 < Nat.log 2 B by
          have := two_le_log_two hB
          omega)
      rw [show K + 1 = Nat.succ K by omega,
        dyadicPrimes_succ_eq_union,
        Finset.sum_union (disjoint_dyadicPrimes_shell B K),
        Finset.sum_range_succ]
      have hshell :=
        sum_inv_sq_shell_le hB hscale
      calc
        (∑ p ∈ dyadicPrimes B K, 1 / (p : ℚ) ^ 2) +
              ∑ p ∈ primesBetween (B * 2 ^ K)
                (2 * (B * 2 ^ K)), 1 / (p : ℚ) ^ 2
            ≤ (14 / ((B : ℚ) * (Nat.log 2 B : ℚ))) *
                  ∑ k ∈ Finset.range K,
                    1 / ((2 ^ k : ℕ) : ℚ) +
                14 /
                  (((B * 2 ^ K : ℕ) : ℚ) *
                    (Nat.log 2 B : ℚ)) :=
          add_le_add ih hshell
        _ = (14 / ((B : ℚ) * (Nat.log 2 B : ℚ))) *
            (∑ k ∈ Finset.range K,
                1 / ((2 ^ k : ℕ) : ℚ) +
              1 / ((2 ^ K : ℕ) : ℚ)) := by
          push_cast
          field_simp

/--
Explicit reciprocal-square estimate on `(B, B * 2^K]`, uniform in `K`.
-/
theorem sum_inv_sq_dyadicPrimes_le
    (B K : ℕ) (hB : 4 ≤ B) :
    (∑ p ∈ dyadicPrimes B K, 1 / (p : ℚ) ^ 2) ≤
      28 / ((B : ℚ) * (Nat.log 2 B : ℚ)) := by
  have hBpos : (0 : ℚ) < (B : ℚ) := by
    exact_mod_cast (show 0 < B by omega)
  have hlogPos : (0 : ℚ) < (Nat.log 2 B : ℚ) := by
    exact_mod_cast (show 0 < Nat.log 2 B by
      have := two_le_log_two hB
      omega)
  have hfactorNonneg :
      0 ≤ 14 / ((B : ℚ) * (Nat.log 2 B : ℚ)) := by positivity
  calc
    (∑ p ∈ dyadicPrimes B K, 1 / (p : ℚ) ^ 2) ≤
        (14 / ((B : ℚ) * (Nat.log 2 B : ℚ))) *
          ∑ k ∈ Finset.range K, 1 / ((2 ^ k : ℕ) : ℚ) :=
      sum_inv_sq_dyadicPrimes_le_geometric B K hB
    _ ≤ (14 / ((B : ℚ) * (Nat.log 2 B : ℚ))) * 2 :=
      mul_le_mul_of_nonneg_left (sum_inv_two_pow_le_two K) hfactorNonneg
    _ = 28 / ((B : ℚ) * (Nat.log 2 B : ℚ)) := by ring

/-! ## Subsets and the residual-channel cutoff -/

/--
The first reciprocal estimate is inherited by every subfamily of the
dyadic prime interval.
-/
theorem sum_inv_subset_dyadicPrimes_le
    (B K : ℕ) (P : Finset ℕ) (hB : 4 ≤ B)
    (hP : P ⊆ dyadicPrimes B K) :
    (∑ p ∈ P, 1 / (p : ℚ)) ≤
      14 * (K : ℚ) / (Nat.log 2 B : ℚ) := by
  calc
    (∑ p ∈ P, 1 / (p : ℚ)) ≤
        ∑ p ∈ dyadicPrimes B K, 1 / (p : ℚ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hP
        (fun p _hp _hpP ↦ by positivity)
    _ ≤ 14 * (K : ℚ) / (Nat.log 2 B : ℚ) :=
      sum_inv_dyadicPrimes_le B K hB

/--
The uniform reciprocal-square estimate is inherited by every subfamily of
the dyadic prime interval.
-/
theorem sum_inv_sq_subset_dyadicPrimes_le
    (B K : ℕ) (P : Finset ℕ) (hB : 4 ≤ B)
    (hP : P ⊆ dyadicPrimes B K) :
    (∑ p ∈ P, 1 / (p : ℚ) ^ 2) ≤
      28 / ((B : ℚ) * (Nat.log 2 B : ℚ)) := by
  calc
    (∑ p ∈ P, 1 / (p : ℚ) ^ 2) ≤
        ∑ p ∈ dyadicPrimes B K, 1 / (p : ℚ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hP
        (fun p _hp _hpP ↦ by positivity)
    _ ≤ 28 / ((B : ℚ) * (Nat.log 2 B : ℚ)) :=
      sum_inv_sq_dyadicPrimes_le B K hB

/--
The residual-channel cutoff `4 q B` lies below the dyadic cutoff with
exponent `q + 2`.  The deliberately loose exponent avoids any logarithmic
rounding in the later channel argument.
-/
theorem four_mul_q_mul_B_le_dyadicCutoff (B q : ℕ) :
    4 * q * B ≤ B * 2 ^ (q + 2) := by
  have hq : q ≤ 2 ^ q :=
    (Nat.lt_two_pow_self (n := q)).le
  have hfour : 4 * q ≤ 4 * 2 ^ q :=
    Nat.mul_le_mul_left 4 hq
  have hmul : B * (4 * q) ≤ B * (4 * 2 ^ q) :=
    Nat.mul_le_mul_left B hfour
  simpa [pow_add, mul_comm, mul_left_comm, mul_assoc] using hmul

/--
Every prime in the geometric support `(B, 4qB)` of a residual channel lies
in the dyadic interval with exponent `q + 2`.
-/
theorem mem_dyadicPrimes_add_two_of_prime_lt_four_mul
    {B q p : ℕ} (hp : p.Prime) (hBp : B < p)
    (hpUpper : p < 4 * q * B) :
    p ∈ dyadicPrimes B (q + 2) := by
  rw [mem_dyadicPrimes]
  exact ⟨hp, hBp,
    hpUpper.le.trans (four_mul_q_mul_B_le_dyadicCutoff B q)⟩

/--
A finite family of primes satisfying the residual-channel support
restriction is contained in the dyadic prime interval with exponent
`q + 2`.
-/
theorem subset_dyadicPrimes_add_two_of_prime_lt_four_mul
    {B q : ℕ} (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlower : ∀ p ∈ P, B < p)
    (hupper : ∀ p ∈ P, p < 4 * q * B) :
    P ⊆ dyadicPrimes B (q + 2) := by
  intro p hp
  exact mem_dyadicPrimes_add_two_of_prime_lt_four_mul
    (hprime p hp) (hlower p hp) (hupper p hp)

/--
First reciprocal-prime estimate in the exact support range supplied by the
residual-channel geometry.
-/
theorem sum_inv_primes_lt_four_mul_le
    {B q : ℕ} (P : Finset ℕ) (hB : 4 ≤ B)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlower : ∀ p ∈ P, B < p)
    (hupper : ∀ p ∈ P, p < 4 * q * B) :
    (∑ p ∈ P, 1 / (p : ℚ)) ≤
      14 * ((q + 2 : ℕ) : ℚ) /
        (Nat.log 2 B : ℚ) := by
  exact sum_inv_subset_dyadicPrimes_le B (q + 2) P hB
    (subset_dyadicPrimes_add_two_of_prime_lt_four_mul
      P hprime hlower hupper)

/--
Uniform reciprocal-square estimate in the exact support range supplied by
the residual-channel geometry.
-/
theorem sum_inv_sq_primes_lt_four_mul_le
    {B q : ℕ} (P : Finset ℕ) (hB : 4 ≤ B)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlower : ∀ p ∈ P, B < p)
    (hupper : ∀ p ∈ P, p < 4 * q * B) :
    (∑ p ∈ P, 1 / (p : ℚ) ^ 2) ≤
      28 / ((B : ℚ) * (Nat.log 2 B : ℚ)) := by
  exact sum_inv_sq_subset_dyadicPrimes_le B (q + 2) P hB
    (subset_dyadicPrimes_add_two_of_prime_lt_four_mul
      P hprime hlower hupper)

end DyadicPrimeReciprocalSums
end PaperC
