import PaperC.Coding.HammingBound
import Mathlib.Data.Nat.Choose.Bounds

/-!
# A quantitative consequence of the Hamming bound

This file formalizes the elementary numerical step immediately following
equation (3.5) of Paper C.  We deliberately keep the statement finite and
integer-valued.

If `1 ≤ t`, `2 * t ≤ m`, and

`∑ j ≤ t, m.choose j ≤ 2 ^ r`,

then

`m < 2 * t * 2 ^ (r / t + 1)`.

The harmless absolute factor comes from the robust integer lower bound

`(m / (2 * t)) ^ t ≤ m.choose t`.

This is enough for the use in Proposition 3.2: when `r / t` is bounded, the
length `m` is bounded by a constant times `t`.  No asymptotic estimate for the
parameters of the paper is asserted here.
-/

namespace PaperC
namespace HammingDefectBound

open Finset

/--
A division-safe lower bound for a binomial coefficient.  The hypotheses put
us in the range used after (3.5).  The factor `2` avoids any rounding issue in
the integer quotient.
-/
theorem half_ratio_pow_le_choose {m t : ℕ}
    (ht : 1 ≤ t) (hmt : 2 * t ≤ m) :
    (m / (2 * t)) ^ t ≤ m.choose t := by
  let a := m / (2 * t)
  have htpos : 0 < t := by omega
  have hden : 0 < 2 * t := Nat.mul_pos (by omega) htpos
  have haone : 1 ≤ a := by
    rw [Nat.le_div_iff_mul_le hden]
    simpa [a] using hmt
  have hamul : a * (2 * t) ≤ m := by
    simpa [a] using Nat.div_mul_le_self m (2 * t)
  have ht_le_at : t ≤ a * t := by
    simpa using Nat.mul_le_mul_right t haone
  have hat_add : a * t + t ≤ m := by
    calc
      a * t + t ≤ a * t + a * t := Nat.add_le_add_left ht_le_at _
      _ = a * (2 * t) := by rw [two_mul, mul_add]
      _ ≤ m := hamul
  have hat0 : a * t ≤ m - t :=
    Nat.le_sub_of_add_le hat_add
  have hat : a * t ≤ m + 1 - t := by
    exact hat0.trans (Nat.sub_le_sub_right m.le_succ t)
  have hfactorial :
      a ^ t * Nat.factorial t ≤ a ^ t * t ^ t :=
    Nat.mul_le_mul_left _ (Nat.factorial_le_pow t)
  have hpow :
      (a * t) ^ t ≤ (m + 1 - t) ^ t :=
    Nat.pow_le_pow_left hat t
  have hdesc :
      (m + 1 - t) ^ t ≤ m.descFactorial t :=
    m.pow_sub_le_descFactorial t
  have hmul :
      Nat.factorial t * a ^ t ≤ Nat.factorial t * m.choose t := by
    calc
      Nat.factorial t * a ^ t = a ^ t * Nat.factorial t := Nat.mul_comm _ _
      _ ≤ a ^ t * t ^ t := hfactorial
      _ = (a * t) ^ t := by rw [mul_pow]
      _ ≤ (m + 1 - t) ^ t := hpow
      _ ≤ m.descFactorial t := hdesc
      _ = Nat.factorial t * m.choose t :=
        Nat.descFactorial_eq_factorial_mul_choose m t
  exact Nat.le_of_mul_le_mul_left hmul (Nat.factorial_pos t)

/-- The last binomial coefficient is one of the nonnegative summands in the
radius-`t` Hamming volume. -/
theorem choose_le_volume (m t : ℕ) :
    m.choose t ≤
      ∑ j ∈ Finset.range (t + 1), m.choose j := by
  exact Finset.single_le_sum
    (fun j _ ↦ Nat.zero_le (m.choose j))
    (Finset.mem_range.mpr (Nat.lt_succ_self t))

/--
The binomial-volume inequality in (3.5) forces a power bound on the integer
ratio `m / (2*t)`.
-/
theorem half_ratio_pow_le_two_pow {m t r : ℕ}
    (ht : 1 ≤ t) (hmt : 2 * t ≤ m)
    (hvolume :
      (∑ j ∈ Finset.range (t + 1), m.choose j) ≤ 2 ^ r) :
    (m / (2 * t)) ^ t ≤ 2 ^ r :=
  (half_ratio_pow_le_choose ht hmt).trans
    ((choose_le_volume m t).trans hvolume)

/--
Taking an integer `t`-th root of a comparison with `2^r`, with an explicit
rounding loss in the exponent.
-/
theorem base_lt_two_pow_div_add_one {a t r : ℕ}
    (ht : 1 ≤ t) (hpow : a ^ t ≤ 2 ^ r) :
    a < 2 ^ (r / t + 1) := by
  have htpos : 0 < t := by omega
  have hremainder : r < (r / t + 1) * t := by
    simpa [Nat.mul_comm] using Nat.lt_mul_div_succ r htpos
  have htwo :
      2 ^ r < (2 ^ (r / t + 1)) ^ t := by
    rw [← pow_mul]
    exact Nat.pow_lt_pow_right (by omega) hremainder
  by_contra hnot
  have hbase : 2 ^ (r / t + 1) ≤ a := Nat.le_of_not_gt hnot
  have hpowers :
      (2 ^ (r / t + 1)) ^ t ≤ a ^ t :=
    Nat.pow_le_pow_left hbase t
  exact (not_lt_of_ge (hpowers.trans hpow)) htwo

/--
Finite quantitative defect bound deduced from (3.5).  It is a robust integer
version of the paper's estimate `m ≤ t * 2^(r/t)`, up to an absolute factor
and one exponent-rounding bit.
-/
theorem length_lt_of_sum_choose_le_two_pow {m t r : ℕ}
    (ht : 1 ≤ t) (hmt : 2 * t ≤ m)
    (hvolume :
      (∑ j ∈ Finset.range (t + 1), m.choose j) ≤ 2 ^ r) :
    m < 2 * t * 2 ^ (r / t + 1) := by
  have hden : 0 < 2 * t := Nat.mul_pos (by omega) (by omega)
  have hratio :
      m / (2 * t) < 2 ^ (r / t + 1) :=
    base_lt_two_pow_div_add_one ht
      (half_ratio_pow_le_two_pow ht hmt hvolume)
  have hm :
      m < 2 ^ (r / t + 1) * (2 * t) :=
    (Nat.div_lt_iff_lt_mul hden).mp hratio
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hm

end HammingDefectBound
end PaperC
