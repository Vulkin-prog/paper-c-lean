import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Summing a pointwise residual-prime estimate

This file isolates the algebraic passage from the pointwise cell estimate
(7.3) to the finite prime mass occurring in (7.4).  It deliberately makes
no use of the geometric definition of residual cells: any rational-valued
function satisfying the pointwise majorant can be supplied.
-/

namespace PaperC

open Finset

/--
Dividing a bound of the shape

`E p ≤ C * (1 + q * B / p) * (1 + B / q)`

by each positive `p` and summing produces exactly the two reciprocal-prime
sums used after (7.3).
-/
theorem residualPrimeMass_le
    (P : Finset ℕ) (E : ℕ → ℚ) (C q B : ℚ)
    (hP : ∀ p ∈ P, 0 < p)
    (hpointwise :
      ∀ p ∈ P,
        E p ≤
          C * (1 + q * B / (p : ℚ)) * (1 + B / q)) :
    ∑ p ∈ P, E p / (p : ℚ) ≤
      C * (1 + B / q) *
        ((∑ p ∈ P, (1 : ℚ) / (p : ℚ)) +
          q * B * ∑ p ∈ P, (1 : ℚ) / (p : ℚ) ^ 2) := by
  calc
    ∑ p ∈ P, E p / (p : ℚ) ≤
        ∑ p ∈ P,
          (C * (1 + q * B / (p : ℚ)) *
              (1 + B / q)) / (p : ℚ) := by
      exact Finset.sum_le_sum fun p hp ↦
        div_le_div_of_nonneg_right
          (hpointwise p hp) (by positivity)
    _ = ∑ p ∈ P,
          C * (1 + B / q) *
            ((1 : ℚ) / (p : ℚ) +
              q * B * ((1 : ℚ) / (p : ℚ) ^ 2)) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hp0 : (p : ℚ) ≠ 0 := by
        exact_mod_cast (hP p hp).ne'
      field_simp [hp0]
    _ = C * (1 + B / q) *
        ((∑ p ∈ P, (1 : ℚ) / (p : ℚ)) +
          q * B * ∑ p ∈ P, (1 : ℚ) / (p : ℚ) ^ 2) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      simp only [← Finset.mul_sum]

/--
Natural-valued specialization, convenient when `E p` is the cardinality
of a finite residual-cell family.
-/
theorem residualPrimeMass_natCast_le
    (P : Finset ℕ) (E : ℕ → ℕ) (C q B : ℚ)
    (hP : ∀ p ∈ P, 0 < p)
    (hpointwise :
      ∀ p ∈ P,
        (E p : ℚ) ≤
          C * (1 + q * B / (p : ℚ)) * (1 + B / q)) :
    ∑ p ∈ P, (E p : ℚ) / (p : ℚ) ≤
      C * (1 + B / q) *
        ((∑ p ∈ P, (1 : ℚ) / (p : ℚ)) +
          q * B * ∑ p ∈ P, (1 : ℚ) / (p : ℚ) ^ 2) :=
  residualPrimeMass_le P (fun p ↦ (E p : ℚ))
    C q B hP hpointwise

end PaperC
