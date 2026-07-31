import PaperC.Arithmetic.CRT
import PaperC.Arithmetic.IntervalCongruence
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List

/-!
# Counting solutions of finite CRT certificates

This module composes the algebraic CRT certificate with the interval-counting
primitive.  It is the first end-to-end finite counting statement needed in
Lemma 7.1 of Paper C: all congruences in a pairwise-coprime certificate reduce
to one class modulo the product, whose representatives in an interval have
the usual `length / modulus + 1` bound.
-/

namespace PaperC
namespace CRT

open Finset
open scoped Function

variable {ι : Type*}

/--
The natural numbers in `[a,b)` satisfying a finite pairwise-coprime CRT
certificate are bounded by the interval length divided by the product
modulus, plus one.
-/
theorem card_Ico_satisfies_cast_le_div_add_one
    (residue modulus : ι → ℕ) (indices : List ι)
    (hcoprime : indices.Pairwise (Nat.Coprime on modulus))
    (hpositive : ∀ i ∈ indices, 0 < modulus i)
    (a b : ℕ) (hab : a ≤ b) :
    ((#{x ∈ Ico a b |
          ∀ i ∈ indices, x ≡ residue i [MOD modulus i]} : ℕ) : ℚ) ≤
      (((((b : ℤ) - (a : ℤ)) : ℤ) : ℚ) /
          ((indices.map modulus).prod : ℚ)) + 1 := by
  let representative : ℕ :=
    Nat.chineseRemainderOfList residue modulus indices hcoprime
  let productModulus : ℕ := (indices.map modulus).prod
  have hproduct : 0 < productModulus := by
    dsimp [productModulus]
    apply List.prod_pos
    intro m hm
    rw [List.mem_map] at hm
    obtain ⟨i, hi, rfl⟩ := hm
    exact hpositive i hi
  have hsets :
      {x ∈ Ico a b |
          ∀ i ∈ indices, x ≡ residue i [MOD modulus i]} =
        {x ∈ Ico a b | x ≡ representative [MOD productModulus]} := by
    ext x
    simp only [mem_filter]
    apply and_congr_right
    intro _
    dsimp [representative, productModulus]
    exact satisfies_iff_modEq_representative
      residue modulus indices hcoprime x
  rw [hsets]
  exact card_nat_Ico_modEq_cast_le_div_add_one
    a b representative productModulus hproduct hab

/--
Two independent variables satisfying the same finite certificate in two
intervals obey the product of the corresponding one-dimensional bounds.
This matches the explicit rectangular domain of Lemma 7.1 in version 7c.
-/
theorem card_product_Ico_satisfies_cast_le
    (residue₁ residue₂ modulus : ι → ℕ) (indices : List ι)
    (hcoprime : indices.Pairwise (Nat.Coprime on modulus))
    (hpositive : ∀ i ∈ indices, 0 < modulus i)
    (a₁ b₁ a₂ b₂ : ℕ) (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) :
    ((({x ∈ Ico a₁ b₁ |
          ∀ i ∈ indices, x ≡ residue₁ i [MOD modulus i]} ×ˢ
        {y ∈ Ico a₂ b₂ |
          ∀ i ∈ indices, y ≡ residue₂ i [MOD modulus i]}).card : ℕ) : ℚ) ≤
      (((((b₁ : ℤ) - (a₁ : ℤ)) : ℤ) : ℚ) /
          ((indices.map modulus).prod : ℚ) + 1) *
        (((((b₂ : ℤ) - (a₂ : ℤ)) : ℤ) : ℚ) /
          ((indices.map modulus).prod : ℚ) + 1) := by
  have hproduct : 0 < (indices.map modulus).prod := by
    apply List.prod_pos
    intro m hm
    rw [List.mem_map] at hm
    obtain ⟨i, hi, rfl⟩ := hm
    exact hpositive i hi
  rw [card_product, Nat.cast_mul]
  exact mul_le_mul
    (card_Ico_satisfies_cast_le_div_add_one
      residue₁ modulus indices hcoprime hpositive a₁ b₁ h₁)
    (card_Ico_satisfies_cast_le_div_add_one
      residue₂ modulus indices hcoprime hpositive a₂ b₂ h₂)
    (by positivity)
    (by
      apply add_nonneg
      · apply div_nonneg
        · exact_mod_cast (sub_nonneg.mpr (by exact_mod_cast h₁ : (a₁ : ℤ) ≤ b₁))
        · positivity
      · norm_num)

/--
Scaled one-dimensional CRT count used in Lemma 7.1.

If the interval has length at most `C₀ * N` and the product modulus is at
most `N`, the harmless `+ 1` in the elementary interval count can be
absorbed into one further copy of `N / productModulus`.
-/
theorem card_Ico_satisfies_cast_le_scaled
    (residue modulus : ι → ℕ) (indices : List ι)
    (hcoprime : indices.Pairwise (Nat.Coprime on modulus))
    (hpositive : ∀ i ∈ indices, 0 < modulus i)
    (a b C₀ N : ℕ) (hab : a ≤ b)
    (hlength : b - a ≤ C₀ * N)
    (hproduct_le : (indices.map modulus).prod ≤ N) :
    ((#{x ∈ Ico a b |
          ∀ i ∈ indices, x ≡ residue i [MOD modulus i]} : ℕ) : ℚ) ≤
      ((((C₀ + 1) * N : ℕ) : ℚ) /
        ((indices.map modulus).prod : ℚ)) := by
  let productModulus : ℕ := (indices.map modulus).prod
  have hproduct : 0 < productModulus := by
    dsimp [productModulus]
    apply List.prod_pos
    intro m hm
    rw [List.mem_map] at hm
    obtain ⟨i, hi, rfl⟩ := hm
    exact hpositive i hi
  have hlength_cast :
      ((b - a : ℕ) : ℚ) ≤ ((C₀ * N : ℕ) : ℚ) := by
    exact_mod_cast hlength
  have hproduct_le_cast :
      (productModulus : ℚ) ≤ (N : ℚ) := by
    exact_mod_cast hproduct_le
  have hproduct_cast : 0 < (productModulus : ℚ) := by
    exact_mod_cast hproduct
  calc
    ((#{x ∈ Ico a b |
          ∀ i ∈ indices, x ≡ residue i [MOD modulus i]} : ℕ) : ℚ) ≤
        (((((b : ℤ) - (a : ℤ)) : ℤ) : ℚ) /
          (productModulus : ℚ)) + 1 :=
      card_Ico_satisfies_cast_le_div_add_one
        residue modulus indices hcoprime hpositive a b hab
    _ = (((b - a : ℕ) : ℚ) / (productModulus : ℚ)) + 1 := by
      rw [← Int.ofNat_sub hab]
      norm_num
    _ ≤ (((C₀ * N : ℕ) : ℚ) / (productModulus : ℚ)) +
          ((N : ℚ) / (productModulus : ℚ)) := by
      exact add_le_add
        (div_le_div_of_nonneg_right hlength_cast hproduct_cast.le)
        ((one_le_div₀ hproduct_cast).2 hproduct_le_cast)
    _ = ((((C₀ + 1) * N : ℕ) : ℚ) /
          ((indices.map modulus).prod : ℚ)) := by
      dsimp [productModulus]
      push_cast
      ring

/--
Scaled rectangular CRT count used in the two-dimensional part of Lemma 7.1.

Both coordinate intervals have length at most `C₀ * N`; hence each
coordinate contributes the same scaled one-dimensional majorant.
-/
theorem card_product_Ico_satisfies_cast_le_scaled
    (residue₁ residue₂ modulus : ι → ℕ) (indices : List ι)
    (hcoprime : indices.Pairwise (Nat.Coprime on modulus))
    (hpositive : ∀ i ∈ indices, 0 < modulus i)
    (a₁ b₁ a₂ b₂ C₀ N : ℕ) (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂)
    (hlength₁ : b₁ - a₁ ≤ C₀ * N)
    (hlength₂ : b₂ - a₂ ≤ C₀ * N)
    (hproduct_le : (indices.map modulus).prod ≤ N) :
    ((({x ∈ Ico a₁ b₁ |
          ∀ i ∈ indices, x ≡ residue₁ i [MOD modulus i]} ×ˢ
        {y ∈ Ico a₂ b₂ |
          ∀ i ∈ indices, y ≡ residue₂ i [MOD modulus i]}).card : ℕ) : ℚ) ≤
      (((((C₀ + 1) * N : ℕ) : ℚ) /
          ((indices.map modulus).prod : ℚ)) ^ 2) := by
  rw [card_product, Nat.cast_mul]
  have hbound₁ :=
    card_Ico_satisfies_cast_le_scaled
      residue₁ modulus indices hcoprime hpositive
      a₁ b₁ C₀ N h₁ hlength₁ hproduct_le
  have hbound₂ :=
    card_Ico_satisfies_cast_le_scaled
      residue₂ modulus indices hcoprime hpositive
      a₂ b₂ C₀ N h₂ hlength₂ hproduct_le
  have hmajorant_nonneg :
      0 ≤ ((((C₀ + 1) * N : ℕ) : ℚ) /
        ((indices.map modulus).prod : ℚ)) := by positivity
  simpa [pow_two] using
    mul_le_mul hbound₁ hbound₂ (by positivity) hmajorant_nonneg

end CRT
end PaperC
