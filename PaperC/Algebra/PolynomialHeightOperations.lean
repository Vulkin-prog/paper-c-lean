import PaperC.Algebra.IntegerPolynomialRootBound
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.NatAntidiagonal

/-!
# Elementary operations on the height of an integral polynomial

The Runge auxiliary polynomial contains the square of an integral
truncation.  This file records a coefficientwise convolution estimate for
the naive height used in `IntegerPolynomialRootBound`.

The factor `p.natDegree + q.natDegree + 1` simply bounds the number of terms
in every coefficient of `p * q`.  No normed-polynomial infrastructure is
needed.
-/

namespace PaperC

open Finset Polynomial

/--
Every coefficient of a product is bounded by the number of possible
convolution terms times the product of the two heights.
-/
theorem coeff_mul_natAbs_le_degree_mul_height
    (p q : ℤ[X]) (n : ℕ) :
    ((p * q).coeff n).natAbs ≤
      (n + 1) *
        (integerPolynomialHeight p * integerPolynomialHeight q) := by
  rw [Polynomial.coeff_mul]
  calc
    (∑ x ∈ Finset.antidiagonal n,
          p.coeff x.1 * q.coeff x.2).natAbs
        ≤ ∑ x ∈ Finset.antidiagonal n,
            (p.coeff x.1 * q.coeff x.2).natAbs :=
      Int.natAbs_sum_le _ _
    _ = ∑ x ∈ Finset.antidiagonal n,
          (p.coeff x.1).natAbs * (q.coeff x.2).natAbs := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Int.natAbs_mul]
    _ ≤ ∑ _x ∈ Finset.antidiagonal n,
          integerPolynomialHeight p * integerPolynomialHeight q := by
      apply Finset.sum_le_sum
      intro x _
      exact Nat.mul_le_mul
        (coeff_natAbs_le_integerPolynomialHeight p x.1)
        (coeff_natAbs_le_integerPolynomialHeight q x.2)
    _ = (n + 1) *
          (integerPolynomialHeight p * integerPolynomialHeight q) := by
      simp [Finset.Nat.card_antidiagonal]

/--
The height of a product is bounded by a degree factor times the product of
the two heights.
-/
theorem integerPolynomialHeight_mul_le
    (p q : ℤ[X]) :
    integerPolynomialHeight (p * q) ≤
      (p.natDegree + q.natDegree + 1) *
        (integerPolynomialHeight p * integerPolynomialHeight q) := by
  unfold integerPolynomialHeight
  apply Finset.sup_le
  intro n hn
  have hnDegree : n ≤ (p * q).natDegree :=
    Polynomial.le_natDegree_of_mem_supp n hn
  have hdegree :
      n + 1 ≤ p.natDegree + q.natDegree + 1 := by
    exact Nat.add_le_add_right
      (hnDegree.trans
        (Polynomial.natDegree_mul_le (p := p) (q := q))) 1
  exact (coeff_mul_natAbs_le_degree_mul_height p q n).trans
    (Nat.mul_le_mul_right
      (integerPolynomialHeight p * integerPolynomialHeight q)
      hdegree)

/-- Specialization of the product estimate to a square. -/
theorem integerPolynomialHeight_sq_le
    (p : ℤ[X]) :
    integerPolynomialHeight (p ^ 2) ≤
      (2 * p.natDegree + 1) *
        integerPolynomialHeight p ^ 2 := by
  rw [pow_two]
  calc
    integerPolynomialHeight (p * p) ≤
        (p.natDegree + p.natDegree + 1) *
          (integerPolynomialHeight p *
            integerPolynomialHeight p) :=
      integerPolynomialHeight_mul_le p p
    _ = (2 * p.natDegree + 1) *
          integerPolynomialHeight p ^ 2 := by
      ring

end PaperC
