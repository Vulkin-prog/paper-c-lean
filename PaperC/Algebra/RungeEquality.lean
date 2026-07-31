import PaperC.Algebra.RungeQPolynomial
import PaperC.Arithmetic.RungeNumerics

/-!
# The equality branch of the quantitative Runge argument

When the nonnegative integer square root agrees with `P(U)`, the integral
normalization agrees with the corresponding scaled integer.  Hence `U` is a
root of the nonzero auxiliary polynomial `Q`.  The explicit height estimate
and Cauchy's bound then put `U` in the paper's `(C d R)^(2d)` scale.
-/

namespace PaperC
namespace RungeEquality

open Polynomial
open scoped BigOperators

private theorem eval_integerSplitProduct
    {k : ℕ} (γ : Fin (2 * k) → ℤ) (U : ℕ) :
    (RungeQPolynomial.integerSplitProduct γ).eval (U : ℤ) =
      ∏ i, ((U : ℤ) + γ i) := by
  rw [RungeQPolynomial.integerSplitProduct]
  rw [Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp

private theorem eval_integralRungeTruncation_eq_scale_mul_natAbs
    {k U : ℕ} (γ : Fin (2 * k) → ℤ) (a : ℤ)
    (heq :
      (((a.natAbs : ℕ) : ℤ) : ℚ) =
        (RungeTruncation.rungeTruncation γ).eval (U : ℚ)) :
    (RungeTruncation.integralRungeTruncation γ).eval (U : ℤ) =
      RungeQPolynomial.rungeScale k * ((a.natAbs : ℕ) : ℤ) := by
  have hmap :=
    congrArg
      (fun p : ℚ[X] ↦ p.eval (U : ℚ))
      (RungeQPolynomial.map_integralRungeTruncation_eq_scale_mul γ)
  have hcast :
      (((RungeTruncation.integralRungeTruncation γ).eval
          (U : ℤ) : ℤ) : ℚ) =
        (RungeQPolynomial.rungeScale k : ℚ) *
          (((a.natAbs : ℕ) : ℤ) : ℚ) := by
    calc
      (((RungeTruncation.integralRungeTruncation γ).eval
          (U : ℤ) : ℤ) : ℚ) =
          ((RungeTruncation.integralRungeTruncation γ).map
            (Int.castRingHom ℚ)).eval (U : ℚ) := by
        simp
      _ =
          (RungeQPolynomial.rungeScale k : ℚ) *
            (RungeTruncation.rungeTruncation γ).eval (U : ℚ) := by
        simpa only [Polynomial.eval_mul, Polynomial.eval_C] using hmap
      _ =
          (RungeQPolynomial.rungeScale k : ℚ) *
            (((a.natAbs : ℕ) : ℤ) : ℚ) := by
        rw [← heq]
  exact_mod_cast hcast

private theorem rungeScale_sq_natAbs
    (k : ℕ) :
    (RungeQPolynomial.rungeScale k ^ 2).natAbs =
      2 ^ (4 * k) := by
  simp only [RungeQPolynomial.rungeScale, Int.natAbs_pow,
    Int.natAbs_ofNat]
  rw [← pow_mul]
  congr 1
  omega

/--
The equality case is bounded by `(128 d R)^(2d)`, with `d=2k`.
-/
theorem base_le_paperScale_of_eq
    {k U R : ℕ} (hk : 1 ≤ k) (hR : 1 ≤ R)
    (γ : Fin (2 * k) → ℤ)
    (hγBound : ∀ i, |γ i| ≤ (R : ℤ))
    (hγInjective : Function.Injective γ)
    (a : ℤ)
    (hproduct :
      (∏ i, ((U : ℤ) + γ i)) = a ^ 2)
    (heq :
      (((a.natAbs : ℕ) : ℤ) : ℚ) =
        (RungeTruncation.rungeTruncation γ).eval (U : ℚ)) :
    U ≤ (128 * (2 * k) * R) ^ (4 * k) := by
  let b : ℤ := ((a.natAbs : ℕ) : ℤ)
  have hG :
      (RungeQPolynomial.integerSplitProduct γ).eval (U : ℤ) =
        b ^ 2 := by
    rw [eval_integerSplitProduct, hproduct]
    simpa only [b] using (Int.natAbs_sq a).symm
  have hP :
      (RungeTruncation.integralRungeTruncation γ).eval (U : ℤ) =
        RungeQPolynomial.rungeScale k * b := by
    simpa only [b] using
      eval_integralRungeTruncation_eq_scale_mul_natAbs γ a heq
  have hroot :=
    RungeQPolynomial.rungeEquality_root_natAbs_le_explicit
      hk hR γ hγBound hγInjective (U : ℤ) b hG hP
  have hrootNat :
      U ≤
        2 ^ (4 * k) *
            (2 ^ (2 * k) * R ^ (2 * k)) +
          (2 * k + 1) *
            ((k + 1) * (16 * R) ^ (2 * k)) ^ 2 := by
    simpa only [Int.natAbs_natCast, rungeScale_sq_natAbs] using hroot
  calc
    U ≤
        2 ^ (4 * k) *
            (2 ^ (2 * k) * R ^ (2 * k)) +
          (2 * k + 1) *
            ((k + 1) * (16 * R) ^ (2 * k)) ^ 2 :=
      hrootNat
    _ ≤
        1 +
          (2 ^ (4 * k) *
              (2 ^ (2 * k) * R ^ (2 * k)) +
            (2 * k + 1) *
              ((k + 1) * (16 * R) ^ (2 * k)) ^ 2) := by
      omega
    _ ≤ (128 * (2 * k) * R) ^ (4 * k) :=
      RungeNumerics.one_add_auxiliaryHeightExpression_le_paperScale
        hk hR

end RungeEquality
end PaperC
