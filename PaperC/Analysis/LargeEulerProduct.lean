import PaperC.Analysis.ReciprocalThreeHalvesTail

/-!
# Euler product over the large-kernel range

For a finite set `S ⊆ (B,X]`, the convergent reciprocal-three-halves tail
controls the scaled product

`∏ p ∈ S, (1 + B p⁻³ᐟ²)`.

No primality input is used: enlarging `S` to every integer in `(B,X]` only
increases the relevant nonnegative sum.
-/

namespace PaperC
namespace LargeEulerProduct

open scoped BigOperators

/-- Factorwise use of `1 + t ≤ exp t`. -/
theorem prod_one_add_mul_rpow_neg_three_halves_le_exp_sum
    (B : ℕ) (S : Finset ℕ) :
    (∏ p ∈ S,
        (1 + (B : ℝ) * (p : ℝ) ^ (-(3 / 2 : ℝ)))) ≤
      Real.exp
        (∑ p ∈ S,
          (B : ℝ) * (p : ℝ) ^ (-(3 / 2 : ℝ))) := by
  calc
    (∏ p ∈ S,
        (1 + (B : ℝ) * (p : ℝ) ^ (-(3 / 2 : ℝ))))
        ≤ ∏ p ∈ S,
            Real.exp
              ((B : ℝ) * (p : ℝ) ^ (-(3 / 2 : ℝ))) := by
          gcongr with p hp
          simpa [add_comm] using
            Real.add_one_le_exp
              ((B : ℝ) * (p : ℝ) ^ (-(3 / 2 : ℝ)))
    _ = Real.exp
        (∑ p ∈ S,
          (B : ℝ) * (p : ℝ) ^ (-(3 / 2 : ℝ))) := by
      rw [Real.exp_sum]

/--
Large-range Euler-product estimate:

`∏_{p∈S} (1 + B p⁻³ᐟ²) ≤ exp (2 √B)`

whenever `S ⊆ (B,X]` and `B ≥ 1`.
-/
theorem prod_one_add_mul_rpow_neg_three_halves_le_exp_two_sqrt
    (B X : ℕ) (S : Finset ℕ)
    (hB : 1 ≤ B)
    (hS : S ⊆ Finset.Ioc B X) :
    (∏ p ∈ S,
        (1 + (B : ℝ) * (p : ℝ) ^ (-(3 / 2 : ℝ)))) ≤
      Real.exp (2 * Real.sqrt B) := by
  refine
    (prod_one_add_mul_rpow_neg_three_halves_le_exp_sum B S).trans ?_
  apply Real.exp_le_exp.mpr
  have hsumSubset :
      (∑ p ∈ S,
          (B : ℝ) * (p : ℝ) ^ (-(3 / 2 : ℝ))) ≤
        ∑ p ∈ Finset.Ioc B X,
          (B : ℝ) * (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hS
      (fun p _hp _hpS ↦
        mul_nonneg (by positivity)
          (Real.rpow_nonneg (Nat.cast_nonneg p) _))
  have htail :=
    sum_Ioc_rpow_neg_three_halves_le B X hB
  have hBnonneg : 0 ≤ (B : ℝ) := by positivity
  have hsqrtPos : 0 < Real.sqrt B := by
    apply Real.sqrt_pos.2
    exact_mod_cast Nat.zero_lt_of_lt hB
  calc
    (∑ p ∈ S,
        (B : ℝ) * (p : ℝ) ^ (-(3 / 2 : ℝ))) ≤
      ∑ p ∈ Finset.Ioc B X,
        (B : ℝ) * (p : ℝ) ^ (-(3 / 2 : ℝ)) :=
      hsumSubset
    _ = (B : ℝ) *
        (∑ p ∈ Finset.Ioc B X,
          (p : ℝ) ^ (-(3 / 2 : ℝ))) := by
      rw [Finset.mul_sum]
    _ ≤ (B : ℝ) * (2 * (Real.sqrt B)⁻¹) :=
      mul_le_mul_of_nonneg_left htail hBnonneg
    _ = 2 * Real.sqrt B := by
      have hBsquare :
          (B : ℝ) = (Real.sqrt B) ^ 2 :=
        (Real.sq_sqrt hBnonneg).symm
      calc
        (B : ℝ) * (2 * (Real.sqrt B)⁻¹) =
            (Real.sqrt B) ^ 2 *
              (2 * (Real.sqrt B)⁻¹) :=
          congrArg
            (fun z : ℝ => z * (2 * (Real.sqrt B)⁻¹))
            hBsquare
        _ = 2 * (Real.sqrt B *
              (Real.sqrt B * (Real.sqrt B)⁻¹)) := by
          rw [pow_two]
          ring
        _ = 2 * Real.sqrt B := by
          rw [mul_inv_cancel₀ hsqrtPos.ne', mul_one]

/-- Negative three-halves power written with an explicit square root. -/
theorem rpow_neg_three_halves_eq_inv_mul_sqrt
    {p : ℕ} (hp : 1 ≤ p) :
    (p : ℝ) ^ (-(3 / 2 : ℝ)) =
      ((p : ℝ) * Real.sqrt p)⁻¹ := by
  have hpReal : 0 < (p : ℝ) := by
    exact_mod_cast Nat.zero_lt_of_lt hp
  rw [Real.rpow_neg hpReal.le]
  congr 1
  calc
    (p : ℝ) ^ (3 / 2 : ℝ) =
        (p : ℝ) ^ ((1 : ℝ) + 1 / 2) := by
      congr 1
      ring
    _ = (p : ℝ) ^ (1 : ℝ) *
        (p : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_add hpReal 1 (1 / 2)
    _ = (p : ℝ) * Real.sqrt p := by
      rw [Real.rpow_one, ← Real.sqrt_eq_rpow]

/--
Equivalent denominator notation used in some versions of the manuscript.
-/
theorem prod_one_add_B_div_mul_sqrt_le_exp_two_sqrt
    (B X : ℕ) (S : Finset ℕ)
    (hB : 1 ≤ B)
    (hS : S ⊆ Finset.Ioc B X) :
    (∏ p ∈ S,
        (1 + (B : ℝ) / ((p : ℝ) * Real.sqrt p))) ≤
      Real.exp (2 * Real.sqrt B) := by
  calc
    (∏ p ∈ S,
        (1 + (B : ℝ) / ((p : ℝ) * Real.sqrt p))) =
      ∏ p ∈ S,
        (1 + (B : ℝ) * (p : ℝ) ^ (-(3 / 2 : ℝ))) := by
      apply Finset.prod_congr rfl
      intro p hpS
      have hpIoc := hS hpS
      have hp : 1 ≤ p := by
        have hpB : B < p := (Finset.mem_Ioc.mp hpIoc).1
        omega
      rw [div_eq_mul_inv,
        ← rpow_neg_three_halves_eq_inv_mul_sqrt hp]
    _ ≤ Real.exp (2 * Real.sqrt B) :=
      prod_one_add_mul_rpow_neg_three_halves_le_exp_two_sqrt
        B X S hB hS

end LargeEulerProduct
end PaperC
