import PaperCV11.RankinTilt

/-!
# Paper C v1.1: exponential envelope for the Rankin Euler product

This file isolates the elementary passage from the finite Euler product in
`RankinTilt` to the exponential form used in (3.4).  It is parameterized by a
finite reciprocal-prime bound; the unconditional prime-harmonic estimate is a
separate arithmetic lemma.
-/

namespace PaperC
namespace V11
namespace RankinEnvelope

open scoped BigOperators

open DefectCounting

/--
If the reciprocal-prime sum up to `T` is at most `R`, the Rankin Euler product
is at most `exp (T^σ R)`.  The termwise comparison is
`p^(-1+σ) = p⁻¹ p^σ ≤ p⁻¹ T^σ`.
-/
theorem prod_one_add_rankin_le_exp
    (T : ℕ) {σ R : ℝ}
    (hσ : 0 ≤ σ)
    (hrecip :
      (∑ p ∈ smallPrimesUpTo T, ((p : ℝ)⁻¹)) ≤ R) :
    (∏ p ∈ smallPrimesUpTo T,
      (1 + (p : ℝ) ^ (-1 + σ))) ≤
      Real.exp ((T : ℝ) ^ σ * R) := by
  calc
    (∏ p ∈ smallPrimesUpTo T,
        (1 + (p : ℝ) ^ (-1 + σ))) ≤
        Real.exp (∑ p ∈ smallPrimesUpTo T,
          (p : ℝ) ^ (-1 + σ)) := by
      exact Real.prod_one_add_le_exp_sum _
        (fun p ↦ Real.rpow_nonneg (Nat.cast_nonneg p) _)
    _ ≤ Real.exp ((T : ℝ) ^ σ * R) := by
      apply Real.exp_le_exp.mpr
      calc
        (∑ p ∈ smallPrimesUpTo T,
            (p : ℝ) ^ (-1 + σ)) ≤
            ∑ p ∈ smallPrimesUpTo T,
              (T : ℝ) ^ σ * (p : ℝ)⁻¹ := by
          apply Finset.sum_le_sum
          intro p hp
          have hpdata := mem_smallPrimesUpTo.mp hp
          have hp0 : 0 < (p : ℝ) := by
            exact_mod_cast hpdata.1.pos
          have hpT : (p : ℝ) ≤ (T : ℝ) := by
            exact_mod_cast hpdata.2
          calc
            (p : ℝ) ^ (-1 + σ) =
                (p : ℝ)⁻¹ * (p : ℝ) ^ σ := by
              rw [Real.rpow_add hp0, Real.rpow_neg_one]
            _ ≤ (p : ℝ)⁻¹ * (T : ℝ) ^ σ := by
              apply mul_le_mul_of_nonneg_left
              · exact Real.rpow_le_rpow hp0.le hpT hσ
              · positivity
            _ = (T : ℝ) ^ σ * (p : ℝ)⁻¹ := by ring
        _ = (T : ℝ) ^ σ *
            (∑ p ∈ smallPrimesUpTo T, (p : ℝ)⁻¹) := by
          rw [Finset.mul_sum]
        _ ≤ (T : ℝ) ^ σ * R :=
          mul_le_mul_of_nonneg_left hrecip
            (Real.rpow_nonneg (Nat.cast_nonneg T) _)

/--
The finite defect count satisfies the exponential Rankin envelope whenever a
reciprocal-prime bound is supplied.
-/
theorem card_kernel_one_cast_le_rankin_exp
    (T X : ℕ) {σ R : ℝ}
    (hσ0 : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2)
    (hrecip :
      (∑ p ∈ smallPrimesUpTo T, ((p : ℝ)⁻¹)) ≤ R) :
    ((TerminalKernelCount.boundedLargeKernelValues T 1 X).card : ℝ) ≤
      (X : ℝ) ^ (1 - σ) * Real.exp ((T : ℝ) ^ σ * R) := by
  exact
    (RankinTilt.card_kernel_one_cast_le_rankin_eulerProduct T X hσhalf).trans
      (mul_le_mul_of_nonneg_left
        (prod_one_add_rankin_le_exp T hσ0 hrecip)
        (Real.rpow_nonneg (Nat.cast_nonneg X) _))

end RankinEnvelope
end V11
end PaperC
