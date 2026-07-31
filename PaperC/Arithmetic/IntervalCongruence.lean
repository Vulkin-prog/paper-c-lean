import Mathlib.Data.Int.CardIntervalMod

/-!
# Residue classes in finite intervals

Paper C repeatedly uses the elementary fact that one congruence class modulo
a positive modulus has at most `length / modulus + 1` representatives in an
interval.  Mathlib already contains an exact ceiling formula; this module
packages the uniform upper bounds used by replacements R3--R5 of Section 17.
-/

namespace PaperC

open Finset

/--
One residue class modulo a positive integer has at most the ceiling of
`(b - a) / r` representatives in the half-open integer interval `[a,b)`.

This is the exact form of the interval count used before replacing the ceiling
by the softer `length / modulus + 1` notation in the manuscript.
-/
theorem card_Ico_modEq_le_ceil_length
    (a b v r : ℤ) (hr : 0 < r) (hab : a ≤ b) :
    ((#{x ∈ Ico a b | x ≡ v [ZMOD r]} : ℕ) : ℤ) ≤
      ⌈(((b - a : ℤ) : ℚ) / (r : ℚ))⌉ := by
  rw [Int.Ico_filter_modEq_card a b hr v]
  have hrq : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
  have hsplit :
      ((b : ℚ) - (v : ℚ)) / (r : ℚ) =
        ((a : ℚ) - (v : ℚ)) / (r : ℚ) +
          (((b - a : ℤ) : ℚ) / (r : ℚ)) := by
    rw [Int.cast_sub]
    ring
  have hadd :=
    Int.ceil_add_le
      (((a : ℚ) - (v : ℚ)) / (r : ℚ))
      (((b - a : ℤ) : ℚ) / (r : ℚ))
  rw [← hsplit] at hadd
  have hlength_nonneg :
      (0 : ℚ) ≤ ((b - a : ℤ) : ℚ) / (r : ℚ) := by
    apply div_nonneg
    · exact_mod_cast sub_nonneg.mpr hab
    · exact_mod_cast hr.le
  have hceil_nonneg :
      (0 : ℤ) ≤ ⌈(((b - a : ℤ) : ℚ) / (r : ℚ))⌉ :=
    Int.ceil_nonneg hlength_nonneg
  omega

/--
The softer form used in Paper C: the number of representatives is bounded by
the interval length divided by the modulus, plus one.
-/
theorem card_Ico_modEq_cast_le_div_add_one
    (a b v r : ℤ) (hr : 0 < r) (hab : a ≤ b) :
    ((#{x ∈ Ico a b | x ≡ v [ZMOD r]} : ℕ) : ℚ) ≤
      (((b - a : ℤ) : ℚ) / (r : ℚ)) + 1 := by
  let d : ℚ := ((b - a : ℤ) : ℚ) / (r : ℚ)
  have hcard :=
    card_Ico_modEq_le_ceil_length a b v r hr hab
  have hcardq :
      ((#{x ∈ Ico a b | x ≡ v [ZMOD r]} : ℕ) : ℚ) ≤
        (⌈d⌉ : ℚ) := by
    dsimp [d]
    exact_mod_cast hcard
  exact hcardq.trans (Int.ceil_lt_add_one d).le

/--
Natural-number wrapper of the preceding integer interval estimate.  It keeps
the variable in `ℕ` for CRT certificates while expressing the interval length
and modulus in the rational form used by the analytic estimates.
-/
theorem card_nat_Ico_modEq_cast_le_div_add_one
    (a b v r : ℕ) (hr : 0 < r) (hab : a ≤ b) :
    ((#{x ∈ Ico a b | x ≡ v [MOD r]} : ℕ) : ℚ) ≤
      (((((b : ℤ) - (a : ℤ)) : ℤ) : ℚ) / (r : ℚ)) + 1 := by
  have hcast :=
    congrArg Finset.card
      (Nat.Ico_filter_modEq_cast (r := r) a b (v := v))
  have hcard :
      #{x ∈ Ico a b | x ≡ v [MOD r]} =
        #{x ∈ Ico (a : ℤ) (b : ℤ) | x ≡ (v : ℤ) [ZMOD (r : ℤ)]} := by
    simpa using hcast
  rw [hcard]
  exact card_Ico_modEq_cast_le_div_add_one
    (a : ℤ) (b : ℤ) (v : ℤ) (r : ℤ)
    (by exact_mod_cast hr) (by exact_mod_cast hab)

/--
Two independent residue constraints in a Cartesian product of intervals are
bounded by the product of the one-dimensional estimates.  This is the finite
counting input of the two-coordinate form of Lemma 7.1.
-/
theorem card_product_Ico_modEq_cast_le
    (a₁ b₁ v₁ a₂ b₂ v₂ r : ℤ)
    (hr : 0 < r) (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) :
    ((({x ∈ Ico a₁ b₁ | x ≡ v₁ [ZMOD r]} ×ˢ
        {y ∈ Ico a₂ b₂ | y ≡ v₂ [ZMOD r]}).card : ℕ) : ℚ) ≤
      ((((b₁ - a₁ : ℤ) : ℚ) / (r : ℚ)) + 1) *
        ((((b₂ - a₂ : ℤ) : ℚ) / (r : ℚ)) + 1) := by
  rw [card_product, Nat.cast_mul]
  exact mul_le_mul
    (card_Ico_modEq_cast_le_div_add_one a₁ b₁ v₁ r hr h₁)
    (card_Ico_modEq_cast_le_div_add_one a₂ b₂ v₂ r hr h₂)
    (by positivity)
    (by
      apply add_nonneg
      · apply div_nonneg
        · exact_mod_cast sub_nonneg.mpr h₁
        · exact_mod_cast hr.le
      · norm_num)

end PaperC
