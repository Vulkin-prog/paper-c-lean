import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Cell-family weights for CRT certificates

This file supplies the finite regrouping step used in Paper C, Lemma 7.1.
A cell is tagged by the prime (more generally, the positive modulus) at which
it occurs.  Summing a weight over all tagged cells is therefore the same as
first counting the cells above each modulus and then summing over moduli.
-/

namespace PaperC
namespace CRT

open Finset
open scoped BigOperators

variable {π κ : Type*} [Fintype π]

/-- The dependent finite type of cells, with each cell tagged by its prime. -/
abbrev LabeledCell (cells : π → Finset κ) :=
  Σ p : π, {c : κ // c ∈ cells p}

/-- The modulus carried by a labeled cell. -/
def labeledCellModulus
    (cells : π → Finset κ) (modulus : π → ℕ)
    (z : LabeledCell cells) : ℕ :=
  modulus z.1

/--
Exact regrouping of the one-dimensional weights `u / p` by the prime label.
-/
theorem sum_labeledCell_div_eq
    (cells : π → Finset κ) (modulus : π → ℕ) (u : ℚ) :
    (∑ z : LabeledCell cells,
        u / (labeledCellModulus cells modulus z : ℚ)) =
      u * ∑ p : π, ((cells p).card : ℚ) / (modulus p : ℚ) := by
  rw [Fintype.sum_sigma]
  simp_rw [labeledCellModulus, Finset.sum_const, Finset.card_univ,
    Fintype.card_coe, nsmul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/--
Exact regrouping of the two-dimensional weights `u / p²` by the prime label.
-/
theorem sum_labeledCell_div_sq_eq
    (cells : π → Finset κ) (modulus : π → ℕ) (u : ℚ) :
    (∑ z : LabeledCell cells,
        u / (labeledCellModulus cells modulus z : ℚ) ^ 2) =
      u * ∑ p : π,
        ((cells p).card : ℚ) / (modulus p : ℚ) ^ 2 := by
  rw [Fintype.sum_sigma]
  simp_rw [labeledCellModulus, Finset.sum_const, Finset.card_univ,
    Fintype.card_coe, nsmul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/--
If every prime supports at most `M` cells, their total two-dimensional weight
is at most `u M ∑ₚ 1 / p²`.
-/
theorem sum_labeledCell_div_sq_le
    (cells : π → Finset κ) (modulus : π → ℕ) (M : ℕ) (u : ℚ)
    (hu : 0 ≤ u) (hmodulus : ∀ p, 0 < modulus p)
    (hcard : ∀ p, (cells p).card ≤ M) :
    (∑ z : LabeledCell cells,
        u / (labeledCellModulus cells modulus z : ℚ) ^ 2) ≤
      u * (M : ℚ) * ∑ p : π, 1 / (modulus p : ℚ) ^ 2 := by
  rw [sum_labeledCell_div_sq_eq]
  calc
    u * ∑ p : π,
        ((cells p).card : ℚ) / (modulus p : ℚ) ^ 2 ≤
        u * ∑ p : π, (M : ℚ) / (modulus p : ℚ) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hu
      apply Finset.sum_le_sum
      intro p hp
      have hpq : (0 : ℚ) < (modulus p : ℚ) := by
        exact_mod_cast hmodulus p
      apply div_le_div_of_nonneg_right
      · exact_mod_cast hcard p
      · exact (pow_pos hpq 2).le
    _ = u * (M : ℚ) * ∑ p : π, 1 / (modulus p : ℚ) ^ 2 := by
      have hfactor :
          (∑ p : π, (M : ℚ) / (modulus p : ℚ) ^ 2) =
            (M : ℚ) * ∑ p : π, 1 / (modulus p : ℚ) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
      rw [hfactor]
      ring

end CRT
end PaperC
