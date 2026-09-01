import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Paper C v2: balancing the conditioning errors

After the truncated Rankin estimate, writing `u = log Y`, the two elementary
conditioning exponents are `B / u` (removed starts) and `u` (dependency
edges). This file proves that their minimum is maximized at `u = sqrt B`.

The theorem is purely analytic. It does not yet formalize the arithmetic
Rankin estimate that produces the first exponent.
-/

namespace PaperC
namespace V2
namespace ConditioningBalance

/-- No positive cutoff exponent can make both `B/u` and `u` exceed `sqrt B`. -/
theorem min_div_self_le_sqrt
    {B u : ℝ} (hB : 0 ≤ B) (hu : 0 < u) :
    min (B / u) u ≤ Real.sqrt B := by
  by_cases hsmall : u ≤ Real.sqrt B
  · exact (min_le_right _ _).trans hsmall
  · have hsqrtLe : Real.sqrt B ≤ u := le_of_not_ge hsmall
    have hdiv : B / u ≤ Real.sqrt B := by
      apply (div_le_iff₀ hu).2
      calc
        B = (Real.sqrt B) ^ 2 := (Real.sq_sqrt hB).symm
        _ = Real.sqrt B * Real.sqrt B := by rw [pow_two]
        _ ≤ Real.sqrt B * u :=
          mul_le_mul_of_nonneg_left hsqrtLe (Real.sqrt_nonneg B)
    exact (min_le_left _ _).trans hdiv

/-- At `u = sqrt B`, the two exponents are exactly equal. -/
theorem div_sqrt_eq_sqrt
    {B : ℝ} (hB : 0 < B) :
    B / Real.sqrt B = Real.sqrt B := by
  have hsqrtNe : Real.sqrt B ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hB)
  calc
    B / Real.sqrt B = (Real.sqrt B) ^ 2 / Real.sqrt B := by
      rw [Real.sq_sqrt hB.le]
    _ = Real.sqrt B := by
      field_simp

/-- The balanced value of the two conditioning exponents is `sqrt B`. -/
theorem min_at_sqrt
    {B : ℝ} (hB : 0 < B) :
    min (B / Real.sqrt B) (Real.sqrt B) = Real.sqrt B := by
  rw [div_sqrt_eq_sqrt hB, min_self]

/--
Optimality in max-min form: `sqrt B` is the largest simultaneous exponent
available from the two elementary envelopes.
-/
theorem conditioning_balance_optimal
    {B : ℝ} (hB : 0 < B) :
    (∀ u : ℝ, 0 < u → min (B / u) u ≤ Real.sqrt B) ∧
      min (B / Real.sqrt B) (Real.sqrt B) = Real.sqrt B := by
  constructor
  · intro u hu
    exact min_div_self_le_sqrt hB.le hu
  · exact min_at_sqrt hB

end ConditioningBalance
end V2
end PaperC
