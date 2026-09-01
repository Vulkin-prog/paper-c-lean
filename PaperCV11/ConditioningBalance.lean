import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Paper C v1.1: the hard-conditioning saddle

Proposition 3.11 balances the removed-start exponent `1 / (2a)` against the
dependency-edge exponent `a`. This file isolates the exact algebraic core:
for positive `u`, `min (B / u) u` is at most `sqrt B`, with equality uniquely
at `u = sqrt B` when `B > 0`.

The public declaration `paper_c_v1_1_hard_conditioning_saddle` specializes
this statement to `B = 1/2`. No asymptotic estimate and no external
literature input is used.
-/

namespace PaperC
namespace V11
namespace ConditioningBalance

/-- The common exponent obtained by balancing `B / u` against `u`. -/
noncomputable def balanceValue (B u : ℝ) : ℝ :=
  min (B / u) u

/-- The product of the two competing branches is exactly `B`. -/
theorem balance_product
    {B u : ℝ} (hu : u ≠ 0) :
    (B / u) * u = B := by
  field_simp

/-- Elementary saddle upper bound. -/
theorem balanceValue_le_sqrt
    {B u : ℝ} (hu : 0 < u) :
    balanceValue B u ≤ Real.sqrt B := by
  by_cases hB : 0 ≤ B
  · by_cases hbranch : u ≤ Real.sqrt B
    · exact (min_le_right _ _).trans hbranch
    · have hsqrt_lt : Real.sqrt B < u := lt_of_not_ge hbranch
      have hsqrt_nonneg : 0 ≤ Real.sqrt B := Real.sqrt_nonneg B
      have hmul : B ≤ Real.sqrt B * u := by
        calc
          B = Real.sqrt B * Real.sqrt B := by
            rw [Real.mul_self_sqrt hB]
          _ ≤ Real.sqrt B * u :=
            mul_le_mul_of_nonneg_left hsqrt_lt.le hsqrt_nonneg
      have hdiv : B / u ≤ Real.sqrt B := by
        apply (div_le_iff₀ hu).2
        simpa [mul_comm] using hmul
      exact (min_le_left _ _).trans hdiv
  · have hBneg : B < 0 := lt_of_not_ge hB
    have hdiv_neg : B / u < 0 := div_neg_of_neg_of_pos hBneg hu
    have hdiv_le : B / u ≤ Real.sqrt B :=
      (le_of_lt hdiv_neg).trans (Real.sqrt_nonneg B)
    exact (min_le_left _ _).trans hdiv_le

/-- The two branches meet at the square-root scale. -/
theorem balanceValue_at_sqrt
    {B : ℝ} (hB : 0 ≤ B) :
    balanceValue B (Real.sqrt B) = Real.sqrt B := by
  rcases eq_or_lt_of_le hB with rfl | hBpos
  · simp [balanceValue]
  · have hsqrt_pos : 0 < Real.sqrt B := Real.sqrt_pos.2 hBpos
    have hquot : B / Real.sqrt B = Real.sqrt B := by
      apply (div_eq_iff (ne_of_gt hsqrt_pos)).2
      simpa [pow_two] using (Real.sq_sqrt hB).symm
    simp [balanceValue, hquot]

/-- Equality in the saddle bound identifies the unique crossing point. -/
theorem eq_sqrt_of_balanceValue_eq_sqrt
    {B u : ℝ} (hB : 0 < B) (hu : 0 < u)
    (hEq : balanceValue B u = Real.sqrt B) :
    u = Real.sqrt B := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt B := Real.sqrt_nonneg B
  have hleft : Real.sqrt B ≤ B / u := by
    rw [← hEq]
    exact min_le_left _ _
  have hright : Real.sqrt B ≤ u := by
    rw [← hEq]
    exact min_le_right _ _
  have hmul_ge : Real.sqrt B * u ≤ B := by
    have := (le_div_iff₀ hu).1 hleft
    simpa [mul_comm] using this
  have hmul_le : B ≤ Real.sqrt B * u := by
    calc
      B = Real.sqrt B * Real.sqrt B := by
        rw [Real.mul_self_sqrt hB.le]
      _ ≤ Real.sqrt B * u :=
        mul_le_mul_of_nonneg_left hright hsqrt_nonneg
  have hmul_eq : Real.sqrt B * u = B := le_antisymm hmul_ge hmul_le
  have hsqrt_pos : 0 < Real.sqrt B := Real.sqrt_pos.2 hB
  apply (mul_left_cancel₀ (ne_of_gt hsqrt_pos))
  calc
    Real.sqrt B * u = B := hmul_eq
    _ = Real.sqrt B * Real.sqrt B := by
      rw [Real.mul_self_sqrt hB.le]

/-- The v1.1 hard-conditioning coefficient in the normalization `B = 1/2`. -/
noncomputable def hardConditioningCoefficient (a : ℝ) : ℝ :=
  balanceValue (1 / 2) a

/-- The crossing point and maximal coefficient. -/
noncomputable def hardConditioningOptimum : ℝ :=
  Real.sqrt (1 / 2)

theorem hardConditioningCoefficient_le
    {a : ℝ} (ha : 0 < a) :
    hardConditioningCoefficient a ≤ hardConditioningOptimum := by
  simpa [hardConditioningCoefficient, hardConditioningOptimum] using
    (balanceValue_le_sqrt (B := (1 / 2 : ℝ)) ha)

theorem hardConditioningCoefficient_at_optimum :
    hardConditioningCoefficient hardConditioningOptimum =
      hardConditioningOptimum := by
  simpa [hardConditioningCoefficient, hardConditioningOptimum] using
    (balanceValue_at_sqrt (B := (1 / 2 : ℝ)) (by norm_num))

theorem eq_optimum_of_hardConditioningCoefficient_eq
    {a : ℝ} (ha : 0 < a)
    (hEq : hardConditioningCoefficient a = hardConditioningOptimum) :
    a = hardConditioningOptimum := by
  simpa [hardConditioningCoefficient, hardConditioningOptimum] using
    (eq_sqrt_of_balanceValue_eq_sqrt
      (B := (1 / 2 : ℝ)) (by norm_num) ha hEq)

/--
Formal algebraic content of Proposition 3.11: the common upper-bound
coefficient has a unique maximum at the crossing point `sqrt (1/2)`.
-/
theorem paper_c_v1_1_hard_conditioning_saddle :
    (∀ a : ℝ, 0 < a →
      hardConditioningCoefficient a ≤ hardConditioningOptimum) ∧
    hardConditioningCoefficient hardConditioningOptimum =
      hardConditioningOptimum ∧
    (∀ a : ℝ, 0 < a →
      hardConditioningCoefficient a = hardConditioningOptimum →
      a = hardConditioningOptimum) := by
  constructor
  · intro a ha
    exact hardConditioningCoefficient_le ha
  constructor
  · exact hardConditioningCoefficient_at_optimum
  · intro a ha hEq
    exact eq_optimum_of_hardConditioningCoefficient_eq ha hEq

end ConditioningBalance
end V11
end PaperC
