import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Scaling the local square-root factors

The analytic series in Lemma 3.1 is evaluated at `1/U`.  This file contains
the finite algebra needed to turn local nonnegative square roots of
`1 + γᵢ/U` into the integer square root of
`G(U) = ∏ᵢ (U + γᵢ)`.

No convergence statement is used here.  The local factors are abstract real
numbers satisfying the required square identities; the analytic module can
therefore plug its sums into this result directly.
-/

namespace PaperC
namespace RungeScaling

open Finset
open scoped BigOperators

/-- The scaled product corresponding to `U^k F(1/U)`. -/
noncomputable def scaledRungeValue
    {k : ℕ} (U : ℕ) (s : Fin (2 * k) → ℝ) : ℝ :=
  (U : ℝ) ^ k * ∏ i, s i

/--
If every local factor squares to `1 + γᵢ/U`, the square of the scaled product
is the split product evaluated at `U`.
-/
theorem scaledRungeValue_sq
    {k U : ℕ} (hU : 1 ≤ U)
    (γ : Fin (2 * k) → ℤ) (s : Fin (2 * k) → ℝ)
    (hsq : ∀ i, (s i) ^ 2 =
      1 + (γ i : ℝ) / (U : ℝ)) :
    (scaledRungeValue U s) ^ 2 =
      ∏ i, ((U : ℝ) + (γ i : ℝ)) := by
  have hU0 : (U : ℝ) ≠ 0 := by
    positivity
  calc
    (scaledRungeValue U s) ^ 2 =
        ((U : ℝ) ^ (2 * k)) * ∏ i, (s i) ^ 2 := by
      rw [scaledRungeValue, mul_pow]
      congr 1
      · rw [← pow_mul]
        congr 1
        omega
      · symm
        simpa using
          (Finset.prod_pow (Finset.univ : Finset (Fin (2 * k)))
            2 s)
    _ = ((U : ℝ) ^ (2 * k)) *
        ∏ i, (1 + (γ i : ℝ) / (U : ℝ)) := by
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      exact hsq i
    _ = ∏ i, ((U : ℝ) *
        (1 + (γ i : ℝ) / (U : ℝ))) := by
      rw [Finset.prod_mul_distrib]
      simp
    _ = ∏ i, ((U : ℝ) + (γ i : ℝ)) := by
      apply Finset.prod_congr rfl
      intro i _
      field_simp

/--
If the split product is the square of an integer and all local factors are
nonnegative, the scaled analytic value is exactly the absolute value of that
integer.  In particular it is integral.
-/
theorem scaledRungeValue_eq_abs_integer
    {k U : ℕ} (hU : 1 ≤ U)
    (γ : Fin (2 * k) → ℤ) (s : Fin (2 * k) → ℝ)
    (hsnonneg : ∀ i, 0 ≤ s i)
    (hsq : ∀ i, (s i) ^ 2 =
      1 + (γ i : ℝ) / (U : ℝ))
    (a : ℤ)
    (hproduct :
      (∏ i, ((U : ℝ) + (γ i : ℝ))) = (a : ℝ) ^ 2) :
    scaledRungeValue U s = |(a : ℝ)| := by
  have hscaledNonneg : 0 ≤ scaledRungeValue U s := by
    apply mul_nonneg
    · positivity
    · exact Finset.prod_nonneg fun i _ ↦ hsnonneg i
  have hsquares :
      (scaledRungeValue U s) ^ 2 = (a : ℝ) ^ 2 := by
    rw [scaledRungeValue_sq hU γ s hsq, hproduct]
  have habsNonneg : 0 ≤ |(a : ℝ)| := abs_nonneg _
  have habsSquare : |(a : ℝ)| ^ 2 = (a : ℝ) ^ 2 := by
    rw [sq_abs]
  nlinarith

end RungeScaling
end PaperC
