import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Int.Order.Lemmas
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Translating a short interval to Runge shifts

This file formalizes the elementary change of variables used between the
coding argument in Proposition 3.2 and Lemma 3.1 of Paper C.

Given distinct natural numbers `n i` in `[U, U + R]`, the shifts

`γ i = n i - U`

are distinct integers with `|γ i| ≤ R`, and evaluating the split product
`∏ i, (T + γ i)` at `T = U` recovers `∏ i, n i`.  In particular, a square
product before translation remains a square after translation.
-/

namespace PaperC
namespace RungeTranslation

open scoped BigOperators

variable {ι : Type*}

/-- The integer shift obtained by translating the value `n i` by the base `U`. -/
def translatedShift (U : ℕ) (n : ι → ℕ) (i : ι) : ℤ :=
  (n i : ℤ) - (U : ℤ)

@[simp]
theorem base_add_translatedShift (U : ℕ) (n : ι → ℕ) (i : ι) :
    (U : ℤ) + translatedShift U n i = n i := by
  simp [translatedShift]

theorem translatedShift_nonneg
    {U : ℕ} {n : ι → ℕ} {i : ι} (hU : U ≤ n i) :
    0 ≤ translatedShift U n i := by
  dsimp [translatedShift]
  omega

theorem translatedShift_le
    {U R : ℕ} {n : ι → ℕ} {i : ι} (hn : n i ≤ U + R) :
    translatedShift U n i ≤ R := by
  dsimp [translatedShift]
  omega

theorem abs_translatedShift_le
    {U R : ℕ} {n : ι → ℕ} {i : ι}
    (hU : U ≤ n i) (hn : n i ≤ U + R) :
    |translatedShift U n i| ≤ R := by
  rw [abs_of_nonneg (translatedShift_nonneg hU)]
  exact translatedShift_le hn

theorem translatedShift_injective
    (U : ℕ) {n : ι → ℕ} (hn : Function.Injective n) :
    Function.Injective (translatedShift U n) := by
  intro i j hij
  apply hn
  have hcast : (n i : ℤ) = n j := by
    dsimp [translatedShift] at hij
    omega
  exact_mod_cast hcast

/-- Evaluation of the translated split product at the base point. -/
theorem prod_base_add_translatedShift [Fintype ι] (U : ℕ) (n : ι → ℕ) :
    (∏ i, ((U : ℤ) + translatedShift U n i)) =
      ∏ i, (n i : ℤ) := by
  simp [translatedShift]

/-- Casting a finite product of natural numbers to the integers. -/
theorem prod_natCast [Fintype ι] (n : ι → ℕ) :
    ((∏ i, n i : ℕ) : ℤ) = ∏ i, (n i : ℤ) := by
  simp

/--
If the original product is a square in `ℕ`, evaluation of the translated
split product at `U` is a square in `ℤ`.
-/
theorem translatedProduct_isSquare
    [Fintype ι]
    (U : ℕ) (n : ι → ℕ)
    (hsquare : ∃ a : ℕ, ∏ i, n i = a ^ 2) :
    ∃ a : ℤ,
      (∏ i, ((U : ℤ) + translatedShift U n i)) = a ^ 2 := by
  obtain ⟨a, ha⟩ := hsquare
  refine ⟨a, ?_⟩
  rw [prod_base_add_translatedShift, ← prod_natCast, ha]
  norm_num

/--
Packaged input conditions for the split-product form of Runge: the shifts are
distinct, bounded by `R`, and their product at `U` is an integer square.
-/
theorem translatedRungeInput
    [Fintype ι]
    {U R : ℕ} {n : ι → ℕ}
    (hinjective : Function.Injective n)
    (hlower : ∀ i, U ≤ n i)
    (hupper : ∀ i, n i ≤ U + R)
    (hsquare : ∃ a : ℕ, ∏ i, n i = a ^ 2) :
    Function.Injective (translatedShift U n) ∧
      (∀ i, |translatedShift U n i| ≤ R) ∧
      ∃ a : ℤ,
        (∏ i, ((U : ℤ) + translatedShift U n i)) = a ^ 2 := by
  refine ⟨translatedShift_injective U hinjective, ?_, translatedProduct_isSquare U n hsquare⟩
  intro i
  exact abs_translatedShift_le (hlower i) (hupper i)

end RungeTranslation
end PaperC
