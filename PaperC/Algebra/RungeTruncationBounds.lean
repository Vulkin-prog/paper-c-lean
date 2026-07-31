import PaperC.Algebra.PolynomialHeightOperations
import PaperC.Algebra.RungeTruncation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Uniform height bounds for the integral Runge truncation

For `d = 2k`, every coefficient of the integral truncation represents
`2^d c_m`.  The coefficient estimate from (3.2) therefore gives the uniform
bound `(16 R)^d`.  Summing over the `k+1` displayed monomials yields a
deliberately robust height estimate; possible collisions of exponents do not
need to be ruled out here.
-/

namespace PaperC
namespace RungeTruncationBounds

open Finset Polynomial

/-- Uniform bound for every chosen scaled Runge coefficient in the range
`m ≤ k`. -/
theorem scaledRungeCoefficientUpTo_natAbs_le
    {k m R : ℕ} (hk : 1 ≤ k) (hR : 1 ≤ R)
    (γ : Fin (2 * k) → ℤ)
    (hγ : ∀ i, |γ i| ≤ (R : ℤ))
    (hm : m ≤ k) :
    (RungeTruncation.scaledRungeCoefficientUpTo γ m).natAbs ≤
      (16 * R) ^ (2 * k) := by
  have hd : 0 < 2 * k := by omega
  have hγq : ∀ i, |(γ i : ℚ)| ≤ (R : ℚ) := by
    intro i
    exact_mod_cast hγ i
  have hc :
      |RungeCoefficients.rungeCoefficient γ m| ≤
        (8 * (R : ℚ)) ^ (2 * k) :=
    RungeCoefficients.abs_rungeCoefficient_le_eight_mul_pow
      hd (by exact_mod_cast hR) (by omega) hγq
  have hspec :=
    RungeTruncation.scaledRungeCoefficientUpTo_spec γ hm
  have hnatAbsCast :
      ((RungeTruncation.scaledRungeCoefficientUpTo γ m).natAbs : ℚ) =
        |((RungeTruncation.scaledRungeCoefficientUpTo γ m : ℤ) : ℚ)| := by
    rw [Int.cast_natAbs, Int.cast_abs]
  have hcast :
      ((RungeTruncation.scaledRungeCoefficientUpTo γ m).natAbs : ℚ) ≤
        (((16 * R) ^ (2 * k) : ℕ) : ℚ) := by
    rw [hnatAbsCast, hspec, abs_mul, abs_pow]
    norm_num only [abs_of_nonneg (show (0 : ℚ) ≤ 2 by norm_num)]
    calc
      (2 : ℚ) ^ (2 * k) *
          |RungeCoefficients.rungeCoefficient γ m| ≤
          (2 : ℚ) ^ (2 * k) *
            (8 * (R : ℚ)) ^ (2 * k) := by
        exact mul_le_mul_of_nonneg_left hc (by positivity)
      _ = (((16 * R) ^ (2 * k) : ℕ) : ℚ) := by
        push_cast
        rw [← mul_pow]
        congr 1
        ring
  exact_mod_cast hcast

/--
Coefficientwise bound for the integral truncation.  The factor `k+1` is a
safe count of the displayed monomials.
-/
theorem coeff_integralRungeTruncation_natAbs_le
    {k R n : ℕ} (hk : 1 ≤ k) (hR : 1 ≤ R)
    (γ : Fin (2 * k) → ℤ)
    (hγ : ∀ i, |γ i| ≤ (R : ℤ)) :
    ((RungeTruncation.integralRungeTruncation γ).coeff n).natAbs ≤
      (k + 1) * (16 * R) ^ (2 * k) := by
  rw [RungeTruncation.integralRungeTruncation,
    Polynomial.finset_sum_coeff]
  calc
    (∑ m ∈ Finset.range (k + 1),
          (Polynomial.monomial (k - m)
            (RungeTruncation.scaledRungeCoefficientUpTo γ m)).coeff n).natAbs
        ≤
      ∑ m ∈ Finset.range (k + 1),
        ((Polynomial.monomial (k - m)
          (RungeTruncation.scaledRungeCoefficientUpTo γ m)).coeff n).natAbs :=
      nat_abs_sum_le _ _
    _ ≤ ∑ _m ∈ Finset.range (k + 1),
          (16 * R) ^ (2 * k) := by
      apply Finset.sum_le_sum
      intro m hm
      have hmk : m ≤ k := by
        simpa only [Finset.mem_range, Nat.lt_succ_iff] using hm
      rw [Polynomial.coeff_monomial]
      split_ifs
      · exact scaledRungeCoefficientUpTo_natAbs_le
          hk hR γ hγ hmk
      · simp
    _ = (k + 1) * (16 * R) ^ (2 * k) := by
      simp

/-- Height form of the preceding coefficient estimate. -/
theorem integerPolynomialHeight_integralRungeTruncation_le
    {k R : ℕ} (hk : 1 ≤ k) (hR : 1 ≤ R)
    (γ : Fin (2 * k) → ℤ)
    (hγ : ∀ i, |γ i| ≤ (R : ℤ)) :
    integerPolynomialHeight
        (RungeTruncation.integralRungeTruncation γ) ≤
      (k + 1) * (16 * R) ^ (2 * k) := by
  unfold integerPolynomialHeight
  exact Finset.sup_le fun n _ ↦
    coeff_integralRungeTruncation_natAbs_le hk hR γ hγ

end RungeTruncationBounds
end PaperC
