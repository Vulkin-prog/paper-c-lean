import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Real.Sqrt
import PaperC.Arithmetic.DefectCounting

/-!
# Weighted finite counting of square-defect representations

This file sharpens the coarse counting estimate in `DefectCounting.lean`.
After removing the value zero, one fixed support `S` contributes at most

`Nat.sqrt (X / ∏ p ∈ S, p)`

values.  Summing over all supports and passing to `ℝ` gives the exact
Euler-product majorant

`√X * ∏ p ∈ P, (1 + 1 / √p)`.

No primality is needed for the counting argument: it is enough that every
element of `P` is positive.  Consequently the theorem applies directly to the
finite set of primes at most `H`.  There is no additive loss, because the
single exceptional value produced by square part `a = 0` is explicitly erased.
-/

namespace PaperC
namespace WeightedDefectCounting

open scoped BigOperators
open DefectCounting

/-- Positive candidate values associated with one fixed support. -/
def positiveValuesForSupport (support : Finset ℕ) (X : ℕ) : Finset ℕ :=
  (valuesForSupport support X).erase 0

/-- Positive values represented by a subset of the finite set `P`. -/
def positiveDefectValues (P : Finset ℕ) (X : ℕ) : Finset ℕ :=
  (defectValues P X).erase 0

@[simp]
theorem mem_positiveValuesForSupport_iff
    {support : Finset ℕ} {X n : ℕ} :
    n ∈ positiveValuesForSupport support X ↔
      n ≠ 0 ∧ n ≤ X ∧
        ∃ a ≤ Nat.sqrt X, n = support.prod id * a ^ 2 := by
  simp [positiveValuesForSupport, mem_valuesForSupport_iff, and_assoc]

@[simp]
theorem mem_positiveDefectValues_iff
    {P : Finset ℕ} {X n : ℕ} :
    n ∈ positiveDefectValues P X ↔
      n ≠ 0 ∧ n ≤ X ∧
        ∃ support ⊆ P, ∃ a ≤ Nat.sqrt X,
          n = support.prod id * a ^ 2 := by
  simp [positiveDefectValues, mem_defectValues_iff, and_assoc]

/--
For a positive support product, every positive represented value comes from a
square part in the sharper interval `1 ≤ a ≤ √(X / ∏ S)`.
-/
theorem positiveValuesForSupport_subset_image_Icc
    {support : Finset ℕ} {X : ℕ}
    (hSupport : ∀ p ∈ support, 1 ≤ p) :
    positiveValuesForSupport support X ⊆
      (Finset.Icc 1 (Nat.sqrt (X / support.prod id))).image
        (fun a ↦ support.prod id * a ^ 2) := by
  intro n hn
  rw [mem_positiveValuesForSupport_iff] at hn
  rcases hn with ⟨hn0, hnX, a, _haX, rfl⟩
  have hprod0 : support.prod id ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro p hp
    exact Nat.ne_of_gt (Nat.zero_lt_one.trans_le (hSupport p hp))
  have hprodPos : 0 < support.prod id := Nat.pos_of_ne_zero hprod0
  have ha0 : a ≠ 0 := by
    intro ha
    subst a
    simp at hn0
  have haSqLe : a ^ 2 ≤ X / support.prod id := by
    rw [Nat.le_div_iff_mul_le hprodPos]
    simpa [Nat.mul_comm] using hnX
  rw [Finset.mem_image]
  exact ⟨a, Finset.mem_Icc.mpr
    ⟨Nat.one_le_iff_ne_zero.mpr ha0, (Nat.le_sqrt').mpr haSqLe⟩, rfl⟩

/--
One fixed support contributes at most `√(X / ∏ S)` positive values.

This is the integer estimate that avoids the `+ 1` in the coarse bound from
`DefectCounting.card_valuesForSupport_le`.
-/
theorem card_positiveValuesForSupport_le
    {support : Finset ℕ} {X : ℕ}
    (hSupport : ∀ p ∈ support, 1 ≤ p) :
    (positiveValuesForSupport support X).card ≤
      Nat.sqrt (X / support.prod id) := by
  calc
    (positiveValuesForSupport support X).card
        ≤ ((Finset.Icc 1 (Nat.sqrt (X / support.prod id))).image
            (fun a ↦ support.prod id * a ^ 2)).card :=
      Finset.card_le_card
        (positiveValuesForSupport_subset_image_Icc hSupport)
    _ ≤ (Finset.Icc 1 (Nat.sqrt (X / support.prod id))).card :=
      Finset.card_image_le
    _ = Nat.sqrt (X / support.prod id) := by
      simp [Nat.card_Icc]

/--
Finite weighted count before passing to real square roots.
-/
theorem card_positiveDefectValues_le_sqrtDiv_sum
    {P : Finset ℕ} {X : ℕ}
    (hP : ∀ p ∈ P, 1 ≤ p) :
    (positiveDefectValues P X).card ≤
      ∑ support ∈ P.powerset, Nat.sqrt (X / support.prod id) := by
  calc
    (positiveDefectValues P X).card
        = (P.powerset.biUnion
            (fun support ↦ positiveValuesForSupport support X)).card := by
          simp [positiveDefectValues, positiveValuesForSupport, defectValues,
            Finset.erase_biUnion]
    _ ≤ ∑ support ∈ P.powerset,
          (positiveValuesForSupport support X).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ support ∈ P.powerset,
          Nat.sqrt (X / support.prod id) := by
      exact Finset.sum_le_sum fun support hsupport ↦
        card_positiveValuesForSupport_le fun p hp ↦
          hP p (Finset.mem_powerset.mp hsupport hp)

/-- Real square root commutes with a finite product of natural numbers. -/
theorem sqrt_natCast_prod (support : Finset ℕ) :
    Real.sqrt (↑(support.prod id) : ℝ) =
      ∏ p ∈ support, Real.sqrt p := by
  classical
  induction support using Finset.induction_on with
  | empty => simp
  | @insert p support hp ih =>
      rw [Finset.prod_insert hp, Nat.cast_mul,
        Real.sqrt_mul (Nat.cast_nonneg (id p)), ih]
      simp [hp]

/--
The cast of the integer contribution of one support is bounded by its
Euler-product weight.
-/
theorem cast_sqrt_div_prod_le
    (support : Finset ℕ) (X : ℕ) :
    (Nat.sqrt (X / support.prod id) : ℝ) ≤
      Real.sqrt X * ∏ p ∈ support, (Real.sqrt p)⁻¹ := by
  calc
    (Nat.sqrt (X / support.prod id) : ℝ)
        ≤ Real.sqrt (X / support.prod id : ℕ) :=
      Real.nat_sqrt_le_real_sqrt
    _ ≤ Real.sqrt ((X : ℝ) / (↑(support.prod id) : ℝ)) :=
      Real.sqrt_le_sqrt Nat.cast_div_le
    _ = Real.sqrt X / Real.sqrt (↑(support.prod id) : ℝ) := by
      rw [Real.sqrt_div (Nat.cast_nonneg X)]
    _ = Real.sqrt X * (Real.sqrt (↑(support.prod id) : ℝ))⁻¹ := by
      rw [div_eq_mul_inv]
    _ = Real.sqrt X * ∏ p ∈ support, (Real.sqrt p)⁻¹ := by
      rw [sqrt_natCast_prod]
      simp

/--
The positive represented values satisfy the weighted Euler-product estimate

`#values ≤ √X * ∏ p ∈ P, (1 + 1 / √p)`.

The conclusion is stated in `ℝ`, which is the form consumed by the analytic
Euler-product estimate.  The only hypothesis is positivity of the possible
defect factors.
-/
theorem card_positiveDefectValues_cast_le_eulerProduct
    {P : Finset ℕ} {X : ℕ}
    (hP : ∀ p ∈ P, 1 ≤ p) :
    ((positiveDefectValues P X).card : ℝ) ≤
      Real.sqrt X * ∏ p ∈ P, (1 + (Real.sqrt p)⁻¹) := by
  calc
    ((positiveDefectValues P X).card : ℝ)
        ≤ (∑ support ∈ P.powerset,
            Nat.sqrt (X / support.prod id) : ℕ) := by
          exact_mod_cast card_positiveDefectValues_le_sqrtDiv_sum hP
    _ = ∑ support ∈ P.powerset,
          (Nat.sqrt (X / support.prod id) : ℝ) := by
      norm_cast
    _ ≤ ∑ support ∈ P.powerset,
          (Real.sqrt X * ∏ p ∈ support, (Real.sqrt p)⁻¹) := by
      exact Finset.sum_le_sum fun support _ ↦ cast_sqrt_div_prod_le support X
    _ = Real.sqrt X *
          ∑ support ∈ P.powerset,
            (∏ p ∈ support, (Real.sqrt p)⁻¹) := by
      rw [Finset.mul_sum]
    _ = Real.sqrt X * ∏ p ∈ P, (1 + (Real.sqrt p)⁻¹) := by
      rw [← Finset.prod_one_add]

/-- Prime-specialized form of the weighted count. -/
theorem card_positiveHDefectValues_cast_le_eulerProduct
    (H X : ℕ) :
    ((positiveDefectValues (smallPrimesUpTo H) X).card : ℝ) ≤
      Real.sqrt X *
        ∏ p ∈ smallPrimesUpTo H, (1 + (Real.sqrt p)⁻¹) := by
  apply card_positiveDefectValues_cast_le_eulerProduct
  intro p hp
  exact (mem_smallPrimesUpTo.mp hp).1.one_lt.le

end WeightedDefectCounting
end PaperC
