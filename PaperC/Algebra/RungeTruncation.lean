import PaperC.Arithmetic.DyadicGap
import PaperC.Combinatorics.RungeCoefficients
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# The dyadically integral Runge truncation

For `d = 2k`, the polynomial used in Lemma 3.1 is

`P(T) = ∑_{m=0}^k c_m T^(k-m)`.

Equation (3.2) says that `2^d c_m` is integral throughout this range.  This
file constructs the corresponding polynomial in `ℤ[T]`, proves its equality
with `2^d P` after mapping to `ℚ[T]`, and records the evaluation identity
needed by the dyadic-gap lemma.
-/

namespace PaperC
namespace RungeTruncation

open Finset Polynomial
open scoped BigOperators

/-- A chosen integral representative of `2^d c_m`. -/
noncomputable def scaledRungeCoefficient
    {d : ℕ} (γ : Fin d → ℤ) (m : ℕ) (hmd : 2 * m ≤ d) : ℤ :=
  Classical.choose
    (RungeCoefficients.two_pow_mul_rungeCoefficient_isRatInteger
      γ hmd)

theorem scaledRungeCoefficient_spec
    {d : ℕ} (γ : Fin d → ℤ) (m : ℕ) (hmd : 2 * m ≤ d) :
    (2 : ℚ) ^ d * RungeCoefficients.rungeCoefficient γ m =
      (scaledRungeCoefficient γ m hmd : ℚ) :=
  Classical.choose_spec
    (RungeCoefficients.two_pow_mul_rungeCoefficient_isRatInteger
      γ hmd)

/--
The chosen integral representative in the range `m ≤ k`; outside this range
the value is set to zero.
-/
noncomputable def scaledRungeCoefficientUpTo
    {k : ℕ} (γ : Fin (2 * k) → ℤ) (m : ℕ) : ℤ :=
  if hmk : m ≤ k then
    scaledRungeCoefficient γ m (by omega)
  else
    0

theorem scaledRungeCoefficientUpTo_spec
    {k : ℕ} (γ : Fin (2 * k) → ℤ) {m : ℕ} (hmk : m ≤ k) :
    (scaledRungeCoefficientUpTo γ m : ℚ) =
      (2 : ℚ) ^ (2 * k) *
        RungeCoefficients.rungeCoefficient γ m := by
  rw [scaledRungeCoefficientUpTo, dif_pos hmk]
  exact (scaledRungeCoefficient_spec γ m (by omega)).symm

/-- The rational truncation `P(T)` in Lemma 3.1. -/
noncomputable def rungeTruncation
    {k : ℕ} (γ : Fin (2 * k) → ℤ) : ℚ[X] :=
  ∑ m ∈ Finset.range (k + 1),
    Polynomial.monomial (k - m)
      (RungeCoefficients.rungeCoefficient γ m)

/-- The integral polynomial whose rational image is `2^(2k) P`. -/
noncomputable def integralRungeTruncation
    {k : ℕ} (γ : Fin (2 * k) → ℤ) : ℤ[X] :=
  ∑ m ∈ Finset.range (k + 1),
    Polynomial.monomial (k - m)
      (scaledRungeCoefficientUpTo γ m)

/--
Coefficientwise integrality of the truncation: mapping the integral
polynomial to `ℚ[X]` gives `2^(2k) P`.
-/
theorem map_integralRungeTruncation
    {k : ℕ} (γ : Fin (2 * k) → ℤ) :
    (integralRungeTruncation γ).map (Int.castRingHom ℚ) =
      Polynomial.C ((2 : ℚ) ^ (2 * k)) *
        rungeTruncation γ := by
  classical
  rw [integralRungeTruncation, Polynomial.map_sum]
  rw [rungeTruncation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hmk : m ≤ k := by
    simpa only [Finset.mem_range, Nat.lt_succ_iff] using hm
  rw [Polynomial.map_monomial, Polynomial.C_mul_monomial]
  congr 1
  exact scaledRungeCoefficientUpTo_spec γ hmk

/--
Evaluation form used immediately before the dyadic separation argument:

`P(u) = integralP(u) / 2^(2k)`.
-/
theorem eval_rungeTruncation_eq_integral_div
    {k : ℕ} (γ : Fin (2 * k) → ℤ) (u : ℤ) :
    (rungeTruncation γ).eval (u : ℚ) =
      (((integralRungeTruncation γ).eval u : ℤ) : ℚ) /
        (2 : ℚ) ^ (2 * k) := by
  have hpow : (2 : ℚ) ^ (2 * k) ≠ 0 := by positivity
  have hmap := congrArg
    (fun p : ℚ[X] ↦ p.eval (u : ℚ))
    (map_integralRungeTruncation γ)
  have hmapEval :
      ((integralRungeTruncation γ).map
        (Int.castRingHom ℚ)).eval (u : ℚ) =
        (2 : ℚ) ^ (2 * k) *
          (rungeTruncation γ).eval (u : ℚ) := by
    simpa only [Polynomial.eval_mul, Polynomial.eval_C] using hmap
  have hcastEval :
      (((integralRungeTruncation γ).eval u : ℤ) : ℚ) =
        ((integralRungeTruncation γ).map
          (Int.castRingHom ℚ)).eval (u : ℚ) := by
    simp
  rw [hcastEval, hmapEval]
  field_simp

/--
The dyadic separation step for the actual truncation polynomial: if its value
at an integer is not the integer `a`, the distance is at least `2^(-2k)`.
-/
theorem one_div_two_pow_le_abs_integer_sub_rungeTruncation
    {k : ℕ} (γ : Fin (2 * k) → ℤ) (a u : ℤ)
    (hne :
      (a : ℚ) ≠ (rungeTruncation γ).eval (u : ℚ)) :
    1 / (2 : ℚ) ^ (2 * k) ≤
      |(a : ℚ) - (rungeTruncation γ).eval (u : ℚ)| := by
  exact one_div_two_pow_le_abs_integer_sub_polynomialEval
    a u (rungeTruncation γ) (integralRungeTruncation γ)
      (2 * k) (eval_rungeTruncation_eq_integral_div γ u) hne

end RungeTruncation
end PaperC
