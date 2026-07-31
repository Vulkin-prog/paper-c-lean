import PaperC.Combinatorics.RungeCoefficients
import Mathlib.RingTheory.PowerSeries.Binomial

/-!
# The formal power series in Runge's argument

This file identifies the finite multi-index coefficient defined in
`RungeCoefficients` with the coefficient of

`∏ ν, (1 + γ ν * X)^(1/2)`.

The square root is represented by the binomial formal power series.  We also
prove algebraically that its square is `1 + γ * X`, and hence that the square
of the finite product is exactly `∏ ν, (1 + γ ν * X)`.

This closes the formal-series part of equation (3.1)--(3.2).  Convergence and
the analytic choice of the positive square root on a real disk are separate
obligations.
-/

namespace PaperC
namespace RungePowerSeries

open Finset PowerSeries
open scoped BigOperators

/-- The binomial series `(1 + γ X)^(1/2)` over the rationals. -/
noncomputable def sqrtFactorSeries (γ : ℤ) : PowerSeries ℚ :=
  PowerSeries.rescale (γ : ℚ)
    (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ))

@[simp]
theorem coeff_sqrtFactorSeries (γ : ℤ) (n : ℕ) :
    PowerSeries.coeff ℚ n (sqrtFactorSeries γ) =
      RungeCoefficients.halfChoose n * (γ : ℚ) ^ n := by
  simp [sqrtFactorSeries, RungeCoefficients.halfChoose, mul_comm]

/--
The finite product of the square-root series associated with the Runge
shifts.
-/
noncomputable def rungeProductSeries
    {d : ℕ} (γ : Fin d → ℤ) : PowerSeries ℚ :=
  ∏ i, sqrtFactorSeries (γ i)

/--
Finitely supported exponent vectors of total mass `m` are canonically the
weak compositions used to define `rungeCoefficient`.
-/
noncomputable def antidiagEquivWeakComposition (d m : ℕ) :
    {l : Fin d →₀ ℕ //
      l ∈ Finset.finsuppAntidiag
        (Finset.univ : Finset (Fin d)) m} ≃
      RungeCoefficients.WeakComposition d m :=
  Finsupp.equivFunOnFinite.subtypeEquiv fun l ↦ by
    simp

/--
The coefficient of the finite product is exactly the multi-index sum from
equation (3.2).
-/
theorem coeff_rungeProductSeries
    {d : ℕ} (γ : Fin d → ℤ) (m : ℕ) :
    PowerSeries.coeff ℚ m (rungeProductSeries γ) =
      RungeCoefficients.rungeCoefficient γ m := by
  classical
  rw [rungeProductSeries,
    PowerSeries.coeff_prod
      (f := fun i ↦ sqrtFactorSeries (γ i))
      (d := m) (s := Finset.univ)]
  rw [← Finset.sum_coe_sort]
  unfold RungeCoefficients.rungeCoefficient
  apply Fintype.sum_equiv
    (antidiagEquivWeakComposition d m)
  intro l
  simp [antidiagEquivWeakComposition]

/-- The unscaled half-binomial series is a formal square root of `1 + X`. -/
theorem binomialSeries_half_sq :
    (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) ^ 2 =
      (1 + PowerSeries.X : PowerSeries ℚ) := by
  rw [pow_two, ← PowerSeries.binomialSeries_add]
  norm_num
  ext n
  simp only [PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one]
  rw [show Ring.choose (1 : ℚ) n = (Nat.choose 1 n : ℚ) from
    Ring.choose_eq_nat_choose 1 n]
  cases n with
  | zero =>
      simp
  | succ n =>
      cases n with
      | zero =>
          simp
      | succ n =>
          simp [Nat.choose, PowerSeries.coeff_X]

/-- Each rescaled half-binomial series squares to `1 + γ X`. -/
theorem sqrtFactorSeries_sq (γ : ℤ) :
    (sqrtFactorSeries γ) ^ 2 =
      1 + PowerSeries.C ℚ (γ : ℚ) * PowerSeries.X := by
  calc
    (sqrtFactorSeries γ) ^ 2 =
        PowerSeries.rescale (γ : ℚ)
          ((PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) ^ 2) := by
      simp [sqrtFactorSeries]
    _ = PowerSeries.rescale (γ : ℚ)
          (1 + PowerSeries.X : PowerSeries ℚ) := by
      rw [binomialSeries_half_sq]
    _ = 1 + PowerSeries.C ℚ (γ : ℚ) * PowerSeries.X := by
      simp [PowerSeries.rescale_X]

/--
The square of the Runge product series is the finite split product
`∏ ν, (1 + γν X)`.
-/
theorem rungeProductSeries_sq
    {d : ℕ} (γ : Fin d → ℤ) :
    (rungeProductSeries γ) ^ 2 =
      ∏ i, (1 + PowerSeries.C ℚ (γ i : ℚ) * PowerSeries.X) := by
  classical
  rw [rungeProductSeries]
  calc
    (∏ i, sqrtFactorSeries (γ i)) ^ 2 =
        ∏ i, (sqrtFactorSeries (γ i)) ^ 2 := by
      symm
      simpa using
        (Finset.prod_pow (Finset.univ : Finset (Fin d)) 2
          (fun i ↦ sqrtFactorSeries (γ i)))
    _ = ∏ i, (1 + PowerSeries.C ℚ (γ i : ℚ) * PowerSeries.X) := by
      apply Finset.prod_congr rfl
      intro i _
      exact sqrtFactorSeries_sq (γ i)

end RungePowerSeries
end PaperC
