import PaperC.Algebra.RungeEquality
import PaperC.Algebra.RungeNonEquality

/-!
# Quantitative Runge bound for a split product

This is the complete Lean counterpart of Paper C, Lemma 3.1.

For `d = 2k ≥ 2`, distinct integral shifts bounded by `R`, and an integer
square value of `∏ (U + γᵢ)`, it proves

`U ≤ (128 * d * R)^(2*d)`.

The manuscript only asserts the existence of an absolute constant `C₀`; the
formalization supplies the concrete value `128`.  The proof separates
`U ≤ 4R`, the dyadic-gap branch of (3.3), and the auxiliary-polynomial
equality branch.
-/

namespace PaperC
namespace RungeBound

open scoped BigOperators

/--
Two distinct integral shifts in `[-R,R]` force the natural radius to be at
least one.  This removes the auxiliary positivity assumption from the final
paper-facing statement.
-/
theorem one_le_radius_of_injective
    {k R : ℕ} (hk : 1 ≤ k)
    (γ : Fin (2 * k) → ℤ)
    (hγBound : ∀ i, |γ i| ≤ (R : ℤ))
    (hγInjective : Function.Injective γ) :
    1 ≤ R := by
  by_contra hnot
  have hRzero : R = 0 := by omega
  have hzero : ∀ i, γ i = 0 := by
    intro i
    have habsLe : |γ i| ≤ 0 := by
      simpa [hRzero] using hγBound i
    have habs : |γ i| = 0 :=
      le_antisymm habsLe (abs_nonneg _)
    exact abs_eq_zero.mp habs
  let i : Fin (2 * k) := ⟨0, by omega⟩
  let j : Fin (2 * k) := ⟨1, by omega⟩
  have hij : i = j := by
    apply hγInjective
    rw [hzero i, hzero j]
  have hvalues := congrArg Fin.val hij
  simp [i, j] at hvalues

/--
Quantitative Runge lemma with the explicit absolute constant `C₀ = 128`.
The exponent `4*k` is `2*d` for `d = 2*k`.
-/
theorem quantitative_runge
    {k U R : ℕ} (hk : 1 ≤ k) (hR : 1 ≤ R)
    (_hU : 2 * R ≤ U)
    (γ : Fin (2 * k) → ℤ)
    (hγBound : ∀ i, |γ i| ≤ (R : ℤ))
    (hγInjective : Function.Injective γ)
    (a : ℤ)
    (hproduct :
      (∏ i, ((U : ℤ) + γ i)) = a ^ 2) :
    U ≤ (128 * (2 * k) * R) ^ (4 * k) := by
  by_cases hlarge : 4 * R < U
  · by_cases heq :
        (((a.natAbs : ℕ) : ℤ) : ℚ) =
          (RungeTruncation.rungeTruncation γ).eval (U : ℚ)
    · exact
        RungeEquality.base_le_paperScale_of_eq
          hk hR γ hγBound hγInjective a hproduct heq
    · have hnonEquality :=
        RungeNonEquality.base_le_paperScale_of_ne
          hk hR hlarge γ hγBound a hproduct heq
      calc
        U ≤ (16 * (2 * k) * R) ^ (2 * k) :=
          hnonEquality
        _ ≤ (128 * (2 * k) * R) ^ (2 * k) := by
          apply Nat.pow_le_pow_left
          have hfactor : 16 ≤ 128 := by norm_num
          exact Nat.mul_le_mul_right R
            (Nat.mul_le_mul_right (2 * k) hfactor)
        _ ≤ (128 * (2 * k) * R) ^ (4 * k) := by
          apply Nat.pow_le_pow_right
          · positivity
          · omega
  · have hsmall : U ≤ 4 * R := Nat.le_of_not_gt hlarge
    calc
      U ≤ 4 * R := hsmall
      _ ≤ 128 * (2 * k) * R := by
        have hkfactor : 4 ≤ 128 * (2 * k) := by omega
        simpa [Nat.mul_assoc] using Nat.mul_le_mul_right R hkfactor
      _ = (128 * (2 * k) * R) ^ 1 := by simp
      _ ≤ (128 * (2 * k) * R) ^ (4 * k) := by
        apply Nat.pow_le_pow_right
        · positivity
        · omega

/--
Paper-facing form of Lemma 3.1.  Its assumptions are exactly: `d=2k≥2`,
distinct shifts bounded by `R`, `U≥2R`, and a square value of the split
product.  The fact `R≥1` is derived from distinctness.
-/
theorem quantitative_runge_of_distinct
    {k U R : ℕ} (hk : 1 ≤ k)
    (hU : 2 * R ≤ U)
    (γ : Fin (2 * k) → ℤ)
    (hγBound : ∀ i, |γ i| ≤ (R : ℤ))
    (hγInjective : Function.Injective γ)
    (a : ℤ)
    (hproduct :
      (∏ i, ((U : ℤ) + γ i)) = a ^ 2) :
    U ≤ (128 * (2 * k) * R) ^ (4 * k) :=
  quantitative_runge hk
    (one_le_radius_of_injective hk γ hγBound hγInjective)
    hU γ hγBound hγInjective a hproduct

end RungeBound
end PaperC
