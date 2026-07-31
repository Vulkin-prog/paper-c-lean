import PaperC.Arithmetic.PrimeCountBridge
import Mathlib.Data.Nat.Log
import Mathlib.NumberTheory.Primorial

/-!
# An elementary Chebyshev-type bound for the small-prime coordinate count

This module proves the finite product estimate needed to replace the trivial
bound `PrimesUpTo.count H ≤ H` by a sublinear one.  Put

`L = Nat.log 2 H`, `q = L / 2`, and `K = 2 ^ q`.

There are at most `K` primes below `K`.  Every remaining prime is at least
`K`, so their product is at least `K` to the power of their number.  On the
other hand this product divides the primorial up to `H`, and Mathlib's
elementary estimate `primorial H ≤ 4 ^ H` applies.  Comparing powers of two
gives

`q * (# primes in [K,H]) ≤ 2H`.

Consequently, as soon as `q > 0`,

`PrimesUpTo.count H ≤ 2 ^ q + (2H) / q`.

No prime number theorem, analytic assumption, or asymptotic black box is used.
-/

namespace PaperC
namespace ChebyshevPrimeCount

open scoped BigOperators

private def primes (H : ℕ) : Finset ℕ :=
  DefectCounting.smallPrimesUpTo H

private def cutoff (H : ℕ) : ℕ :=
  2 ^ (Nat.log 2 H / 2)

private def lowPrimes (H : ℕ) : Finset ℕ :=
  (primes H).filter fun p ↦ p < cutoff H

private def highPrimes (H : ℕ) : Finset ℕ :=
  (primes H).filter fun p ↦ ¬ p < cutoff H

private theorem card_primes (H : ℕ) :
    (primes H).card = PrimesUpTo.count H := by
  exact (PrimeCountBridge.count_eq_card_smallPrimesUpTo H).symm

private theorem card_lowPrimes_le (H : ℕ) :
    (lowPrimes H).card ≤ cutoff H := by
  refine (Finset.card_le_card ?_).trans_eq (Finset.card_range _)
  intro p hp
  exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2

private theorem highPrimes_subset_primes (H : ℕ) :
    highPrimes H ⊆ primes H :=
  Finset.filter_subset _ _

private theorem cutoff_pow_card_highPrimes_le_primorial (H : ℕ) :
    cutoff H ^ (highPrimes H).card ≤ primorial H := by
  calc
    cutoff H ^ (highPrimes H).card
        ≤ ∏ p ∈ highPrimes H, p := by
          apply Finset.pow_card_le_prod
          intro p hp
          exact Nat.le_of_not_gt (Finset.mem_filter.mp hp).2
    _ ≤ ∏ p ∈ primes H, p := by
      apply Finset.prod_le_prod_of_subset_of_one_le'
      · exact highPrimes_subset_primes H
      · intro p hp _
        exact (DefectCounting.mem_smallPrimesUpTo.mp hp).1.one_lt.le
    _ = primorial H := by
      simp [primes, DefectCounting.smallPrimesUpTo, primorial]

/--
The number of primes in the upper part `[2^(log₂ H / 2), H]` satisfies the
key exponent bound obtained from the elementary primorial estimate.
-/
theorem halfLog_mul_card_highPrimes_le (H : ℕ) :
    (Nat.log 2 H / 2) * (highPrimes H).card ≤ 2 * H := by
  have hpow :
      2 ^ ((Nat.log 2 H / 2) * (highPrimes H).card) ≤
        2 ^ (2 * H) := by
    calc
      2 ^ ((Nat.log 2 H / 2) * (highPrimes H).card)
          = cutoff H ^ (highPrimes H).card := by
            simp [cutoff, pow_mul]
      _ ≤ primorial H := cutoff_pow_card_highPrimes_le_primorial H
      _ ≤ 4 ^ H := primorial_le_four_pow H
      _ = 2 ^ (2 * H) := by norm_num [pow_mul]
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hpow

private theorem card_highPrimes_le_div (H : ℕ)
    (hq : 0 < Nat.log 2 H / 2) :
    (highPrimes H).card ≤ (2 * H) / (Nat.log 2 H / 2) := by
  apply (Nat.le_div_iff_mul_le hq).mpr
  simpa [Nat.mul_comm] using halfLog_mul_card_highPrimes_le H

private theorem card_low_add_card_high (H : ℕ) :
    (lowPrimes H).card + (highPrimes H).card = (primes H).card := by
  exact Finset.card_filter_add_card_filter_not
    (s := primes H) (fun p ↦ p < cutoff H)

/--
Explicit elementary prime-counting bound.  It is the usual
`O(H / log H)` Chebyshev estimate, with a harmless square-root scale summand
`2^(⌊log₂ H / 2⌋)` kept visible.

The positivity assumption is equivalent to `Nat.log 2 H ≥ 2`; in particular
it holds for every `H ≥ 4`.
-/
theorem count_le_pow_halfLog_add_div (H : ℕ)
    (hq : 0 < Nat.log 2 H / 2) :
    PrimesUpTo.count H ≤
      2 ^ (Nat.log 2 H / 2) + (2 * H) / (Nat.log 2 H / 2) := by
  rw [← card_primes H, ← card_low_add_card_high H]
  exact Nat.add_le_add (card_lowPrimes_le H) (card_highPrimes_le_div H hq)

/-- The explicit estimate in a form with the easy-to-check threshold `4 ≤ H`. -/
theorem count_le_pow_halfLog_add_div_of_four_le {H : ℕ} (hH : 4 ≤ H) :
    PrimesUpTo.count H ≤
      2 ^ (Nat.log 2 H / 2) + (2 * H) / (Nat.log 2 H / 2) := by
  apply count_le_pow_halfLog_add_div H
  have hlog : 2 ≤ Nat.log 2 H := by
    apply Nat.le_log_of_pow_le (by omega)
    norm_num at hH ⊢
    exact hH
  omega

private theorem two_mul_add_one_le_two_pow_succ :
    ∀ q : ℕ, 2 * q + 1 ≤ 2 ^ (q + 1)
  | 0 => by norm_num
  | 1 => by norm_num
  | q + 2 => by
      have ih := two_mul_add_one_le_two_pow_succ (q + 1)
      calc
        2 * (q + 2) + 1 ≤ 2 * (2 * (q + 1) + 1) := by omega
        _ ≤ 2 * 2 ^ (q + 1 + 1) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (q + 2 + 1) := by
          simp only [pow_add, pow_one]
          ring

private theorem card_highPrimes_le (H : ℕ) :
    (highPrimes H).card ≤ H := by
  calc
    (highPrimes H).card ≤ (Finset.Icc 1 H).card := by
      apply Finset.card_le_card
      intro p hp
      have hp' :=
        DefectCounting.mem_smallPrimesUpTo.mp
          (Finset.mem_filter.mp hp).1
      exact Finset.mem_Icc.mpr ⟨hp'.1.pos, hp'.2⟩
    _ = H := by simp

private theorem log_mul_card_lowPrimes_le {H : ℕ} (hH : 4 ≤ H) :
    Nat.log 2 H * (lowPrimes H).card ≤ 2 * H := by
  let L := Nat.log 2 H
  let q := L / 2
  have hLq_upper : L ≤ 2 * q + 1 := by
    dsimp [q]
    omega
  have hqL : 2 * q ≤ L := by
    dsimp [q]
    omega
  have hLK : L * 2 ^ q ≤ 2 ^ (L + 1) := by
    calc
      L * 2 ^ q ≤ (2 * q + 1) * 2 ^ q :=
        Nat.mul_le_mul_right (2 ^ q) hLq_upper
      _ ≤ 2 ^ (q + 1) * 2 ^ q :=
        Nat.mul_le_mul_right (2 ^ q) (two_mul_add_one_le_two_pow_succ q)
      _ = 2 ^ (2 * q + 1) := by
        rw [← pow_add]
        congr 1
        omega
      _ ≤ 2 ^ (L + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hpow : 2 ^ L ≤ H := by
    apply Nat.pow_log_le_self
    omega
  calc
    Nat.log 2 H * (lowPrimes H).card
        ≤ L * 2 ^ q := by
          dsimp [L, q]
          exact Nat.mul_le_mul_left _ (card_lowPrimes_le H)
    _ ≤ 2 ^ (L + 1) := hLK
    _ = 2 * 2 ^ L := by rw [pow_succ]; omega
    _ ≤ 2 * H := Nat.mul_le_mul_left 2 hpow

private theorem log_mul_card_highPrimes_le (H : ℕ) :
    Nat.log 2 H * (highPrimes H).card ≤ 5 * H := by
  let L := Nat.log 2 H
  let q := L / 2
  let m := (highPrimes H).card
  have hLq : L ≤ 2 * q + 1 := by
    dsimp [q]
    omega
  have hqm : q * m ≤ 2 * H := by
    simpa [q, m, L] using halfLog_mul_card_highPrimes_le H
  have hm : m ≤ H := by
    simpa [m] using card_highPrimes_le H
  calc
    Nat.log 2 H * (highPrimes H).card = L * m := rfl
    _ ≤ (2 * q + 1) * m := Nat.mul_le_mul_right m hLq
    _ = 2 * (q * m) + m := by ring
    _ ≤ 2 * (2 * H) + H :=
      Nat.add_le_add (Nat.mul_le_mul_left 2 hqm) hm
    _ = 5 * H := by omega

/--
Fully simplified Chebyshev-type estimate with a numerical constant:

`⌊log₂ H⌋ · π(H) ≤ 7H` for every `H ≥ 4`.

Here `π(H)` is exactly the coordinate count `PrimesUpTo.count H`.  This is a
direct finite consequence of `primorial_le_four_pow`; no analytic estimate for
primes is assumed.
-/
theorem log_mul_count_le_seven_mul {H : ℕ} (hH : 4 ≤ H) :
    Nat.log 2 H * PrimesUpTo.count H ≤ 7 * H := by
  rw [← card_primes H, ← card_low_add_card_high H, Nat.mul_add]
  calc
    Nat.log 2 H * (lowPrimes H).card +
          Nat.log 2 H * (highPrimes H).card
        ≤ 2 * H + 5 * H :=
      Nat.add_le_add (log_mul_card_lowPrimes_le hH)
        (log_mul_card_highPrimes_le H)
    _ = 7 * H := by omega

/--
Division form of the explicit Chebyshev bound:

`π(H) ≤ 7H / ⌊log₂ H⌋` for `H ≥ 4`.
-/
theorem count_le_seven_mul_div_log {H : ℕ} (hH : 4 ≤ H) :
    PrimesUpTo.count H ≤ (7 * H) / Nat.log 2 H := by
  have hlog : 0 < Nat.log 2 H := by
    have : 2 ≤ Nat.log 2 H := by
      apply Nat.le_log_of_pow_le (by omega)
      norm_num at hH ⊢
      exact hH
    omega
  apply (Nat.le_div_iff_mul_le hlog).mpr
  simpa [Nat.mul_comm] using log_mul_count_le_seven_mul hH

end ChebyshevPrimeCount
end PaperC
