import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Separation from a dyadic rational

This file isolates the discretization step immediately following (3.3) in
Paper C, Lemma 3.1.  If an integer and a rational with denominator `2 ^ d`
are distinct, then their distance is at least `2 ^ (-d)`.

The last theorem packages the same fact for the value at an integer of a
rational polynomial `P` such that `2 ^ d * P` has integral coefficients:
the integral polynomial is supplied through its evaluation.
-/

namespace PaperC

open scoped Polynomial

/--
An integer and a distinct dyadic rational of denominator `2 ^ d` are
separated by at least `1 / 2 ^ d`.
-/
theorem one_div_two_pow_le_abs_integer_sub_dyadic
    (a b : ℤ) (d : ℕ)
    (hne : (a : ℚ) ≠ (b : ℚ) / (2 : ℚ) ^ d) :
    1 / (2 : ℚ) ^ d ≤
      |(a : ℚ) - (b : ℚ) / (2 : ℚ) ^ d| := by
  have hden : (0 : ℚ) < (2 : ℚ) ^ d := by positivity
  have hrearrange :
      (a : ℚ) - (b : ℚ) / (2 : ℚ) ^ d =
        ((a * (2 : ℤ) ^ d - b : ℤ) : ℚ) / (2 : ℚ) ^ d := by
    norm_num only [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
    field_simp
  have hnum : a * (2 : ℤ) ^ d - b ≠ 0 := by
    intro hzero
    apply sub_ne_zero.mpr hne
    rw [hrearrange, hzero]
    norm_num
  have hone : (1 : ℤ) ≤ |a * (2 : ℤ) ^ d - b| :=
    Int.one_le_abs hnum
  have honeQ :
      (1 : ℚ) ≤ ((|a * (2 : ℤ) ^ d - b| : ℤ) : ℚ) := by
    exact_mod_cast hone
  rw [hrearrange, abs_div, abs_of_pos hden, ← Int.cast_abs]
  exact (div_le_div_iff_of_pos_right hden).2 honeQ

/--
The symmetric orientation of `one_div_two_pow_le_abs_integer_sub_dyadic`.
-/
theorem one_div_two_pow_le_abs_dyadic_sub_integer
    (a b : ℤ) (d : ℕ)
    (hne : (b : ℚ) / (2 : ℚ) ^ d ≠ (a : ℚ)) :
    1 / (2 : ℚ) ^ d ≤
      |(b : ℚ) / (2 : ℚ) ^ d - (a : ℚ)| := by
  rw [abs_sub_comm]
  exact one_div_two_pow_le_abs_integer_sub_dyadic a b d hne.symm

/--
Polynomial-evaluation form of the dyadic gap.  In the application, `p` is
the integral polynomial `2 ^ d * P`; consequently

`P(u) = p(u) / 2 ^ d`.
-/
theorem one_div_two_pow_le_abs_integer_sub_dyadicPolynomialEval
    (a u : ℤ) (p : ℤ[X]) (d : ℕ)
    (hne :
      (a : ℚ) ≠ ((p.eval u : ℤ) : ℚ) / (2 : ℚ) ^ d) :
    1 / (2 : ℚ) ^ d ≤
      |(a : ℚ) - ((p.eval u : ℤ) : ℚ) / (2 : ℚ) ^ d| :=
  one_div_two_pow_le_abs_integer_sub_dyadic a (p.eval u) d hne

/--
Transport the polynomial-evaluation gap across an explicitly supplied
identity `P(u) = p(u) / 2 ^ d`.  This form can be applied without unfolding
the representation of the rational polynomial `P`.
-/
theorem one_div_two_pow_le_abs_integer_sub_polynomialEval
    (a u : ℤ) (P : ℚ[X]) (p : ℤ[X]) (d : ℕ)
    (hscaled :
      P.eval (u : ℚ) = ((p.eval u : ℤ) : ℚ) / (2 : ℚ) ^ d)
    (hne : (a : ℚ) ≠ P.eval (u : ℚ)) :
    1 / (2 : ℚ) ^ d ≤ |(a : ℚ) - P.eval (u : ℚ)| := by
  rw [hscaled] at hne ⊢
  exact one_div_two_pow_le_abs_integer_sub_dyadicPolynomialEval
    a u p d hne

end PaperC
