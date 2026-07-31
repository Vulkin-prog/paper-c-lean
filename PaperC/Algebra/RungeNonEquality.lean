import PaperC.Algebra.RungeDichotomy
import PaperC.Analysis.RungeEstimate
import PaperC.Arithmetic.RungeNumerics

/-!
# The non-equality branch of the quantitative Runge argument

Equation (3.3) and dyadic separation force `U` to be small whenever the
nonnegative integer square root differs from the truncation `P(U)`.
-/

namespace PaperC
namespace RungeNonEquality

open scoped BigOperators

/-- Explicit numerator bound produced directly by dyadic separation. -/
theorem base_le_dyadicTailNumerator
    {k U R : ℕ} (hk : 1 ≤ k) (hR : 1 ≤ R)
    (hU : 4 * R < U)
    (γ : Fin (2 * k) → ℤ)
    (hγ : ∀ i, |γ i| ≤ (R : ℤ))
    (a : ℤ)
    (hproduct :
      (∏ i, ((U : ℤ) + γ i)) = a ^ 2)
    (hne :
      (((a.natAbs : ℕ) : ℤ) : ℚ) ≠
        (RungeTruncation.rungeTruncation γ).eval (U : ℚ)) :
    U ≤
      2 ^ (2 * k) *
        (2 ^ (2 * k + 1) * (2 * R) ^ (k + 1)) := by
  apply
    RungeDichotomy.nat_le_two_pow_mul_of_rungeTruncation_gap
      γ ((a.natAbs : ℕ) : ℤ) U
        (2 ^ (2 * k + 1) * (2 * R) ^ (k + 1))
        (by omega) hne
  simpa only [Int.cast_natCast] using
    RungeEstimate.abs_natAbs_sub_rungeTruncation_le
      hk hR hU γ hγ a hproduct

/--
The preceding explicit numerator lies in the manuscript's uniform
`(C d R)^d` scale (and therefore a fortiori in `(C d R)^(2d)`).
-/
theorem base_le_paperScale_of_ne
    {k U R : ℕ} (hk : 1 ≤ k) (hR : 1 ≤ R)
    (hU : 4 * R < U)
    (γ : Fin (2 * k) → ℤ)
    (hγ : ∀ i, |γ i| ≤ (R : ℤ))
    (a : ℤ)
    (hproduct :
      (∏ i, ((U : ℤ) + γ i)) = a ^ 2)
    (hne :
      (((a.natAbs : ℕ) : ℤ) : ℚ) ≠
        (RungeTruncation.rungeTruncation γ).eval (U : ℚ)) :
    U ≤ (16 * (2 * k) * R) ^ (2 * k) := by
  exact
    (base_le_dyadicTailNumerator
      hk hR hU γ hγ a hproduct hne).trans
      (RungeNumerics.dyadicTailNumerator_le_paperScale hk hR)

end RungeNonEquality
end PaperC
