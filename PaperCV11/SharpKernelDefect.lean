import PaperCV11.PrimeHarmonic
import PaperCV11.RankinEnvelope

/-!
# Paper C v1.1: paper-shaped sharp kernel-defect contract

This file fixes the exact finite counting function `A(X,T)` from Proposition
3.3, rewrites the Rankin envelope in the literal exponential form of equation
(3.4), and supplies its prime-harmonic input from `PrimeHarmonic`.  The full
Proposition 3.3 endpoint name remains reserved until the compact-uniform
consequence (3.5) is also proved.
-/

namespace PaperC
namespace V11
namespace SharpKernelDefect

open scoped BigOperators

open DefectCounting
open LargeOddKernel
open TerminalKernelCount

/-- The exact finite counting function denoted `A(X,T)` in Section 3.2. -/
noncomputable def rankinDefectCount (X T : ℕ) : ℕ :=
  (boundedLargeKernelValues T 1 X).card

/-- Exact membership statement for the finite set counted by `A(X,T)`. -/
theorem mem_rankinDefectValues_iff
    {X T n : ℕ} :
    n ∈ boundedLargeKernelValues T 1 X ↔
      1 ≤ n ∧ n ≤ X ∧ largeOddKernel T n = 1 := by
  rw [mem_boundedLargeKernelValues]
  constructor
  · rintro ⟨hn1, hnX, hkernel⟩
    exact ⟨hn1, hnX,
      Nat.le_antisymm hkernel (one_le_largeOddKernel T n)⟩
  · rintro ⟨hn1, hnX, hkernel⟩
    exact ⟨hn1, hnX, hkernel.le⟩

@[simp]
theorem rankinDefectCount_eq_card (X T : ℕ) :
    rankinDefectCount X T =
      (boundedLargeKernelValues T 1 X).card :=
  rfl

/-- The explicit correction term in the exponent on the right of (3.4). -/
noncomputable def equationThreeFourEnvelope
    (T : ℕ) (σ C : ℝ) : ℝ :=
  C * (T : ℝ) ^ σ * Real.log (Real.log (3 * (T : ℝ)))

/--
Literal finite form of (3.4), conditional only on the reciprocal-prime bound
that will be supplied by the elementary dyadic-shell argument.
-/
theorem finite_equation_three_four_of_reciprocal_bound
    (X T : ℕ) {σ C : ℝ}
    (hT : 3 ≤ T) (hTX : T ≤ X)
    (hσpos : 0 < σ) (hσ : σ < 1 / 2)
    (hrecip :
      (∑ p ∈ smallPrimesUpTo T, ((p : ℝ)⁻¹)) ≤
        C * Real.log (Real.log (3 * (T : ℝ)))) :
    (rankinDefectCount X T : ℝ) ≤
      (X : ℝ) * Real.exp
        (-σ * Real.log (X : ℝ) +
          equationThreeFourEnvelope T σ C) := by
  have hXnat : 0 < X :=
    lt_of_lt_of_le (by omega : 0 < 3) (hT.trans hTX)
  have hX : 0 < (X : ℝ) := by
    exact_mod_cast hXnat
  have hfinite :=
    RankinEnvelope.card_kernel_one_cast_le_rankin_exp
      T X hσpos.le hσ.le hrecip
  rw [rankinDefectCount_eq_card]
  refine hfinite.trans_eq ?_
  calc
    (X : ℝ) ^ (1 - σ) *
          Real.exp
            ((T : ℝ) ^ σ *
              (C * Real.log (Real.log (3 * (T : ℝ))))) =
        Real.exp
          (Real.log (X : ℝ) * (1 - σ) +
            equationThreeFourEnvelope T σ C) := by
      rw [Real.rpow_def_of_pos hX, Real.exp_add]
      congr 2
      simp only [equationThreeFourEnvelope]
      ring
    _ = Real.exp
          (Real.log (X : ℝ) +
            (-σ * Real.log (X : ℝ) +
              equationThreeFourEnvelope T σ C)) := by
      congr 1
      ring
    _ = (X : ℝ) * Real.exp
          (-σ * Real.log (X : ℝ) +
            equationThreeFourEnvelope T σ C) := by
      rw [Real.exp_add, Real.exp_log hX]

/-- Equation (3.4) with the explicit absolute constant supplied above. -/
theorem finite_equation_three_four
    (X T : ℕ) {σ : ℝ}
    (hT : 3 ≤ T) (hTX : T ≤ X)
    (hσpos : 0 < σ) (hσ : σ < 1 / 2) :
    (rankinDefectCount X T : ℝ) ≤
      (X : ℝ) * Real.exp
        (-σ * Real.log (X : ℝ) +
          equationThreeFourEnvelope T σ 120) := by
  apply finite_equation_three_four_of_reciprocal_bound
    X T hT hTX hσpos hσ
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    PrimeHarmonic.sum_inv_smallPrimesUpTo_real_le_loglog T hT

end SharpKernelDefect
end V11

/--
The complete finite (3.4) half of Proposition 3.3, with one absolute constant
valid for all `3 ≤ T ≤ X` and `0 < σ < 1/2`.
-/
theorem paper_c_v1_1_sharp_kernel_defect_finite :
    ∃ C : ℝ, 0 < C ∧
      ∀ X T : ℕ, ∀ σ : ℝ,
        3 ≤ T → T ≤ X → 0 < σ → σ < 1 / 2 →
          (V11.SharpKernelDefect.rankinDefectCount X T : ℝ) ≤
            (X : ℝ) * Real.exp
              (-σ * Real.log (X : ℝ) +
                C * (T : ℝ) ^ σ *
                  Real.log (Real.log (3 * (T : ℝ)))) := by
  refine ⟨120, by norm_num, ?_⟩
  intro X T σ hT hTX hσpos hσ
  simpa only [V11.SharpKernelDefect.equationThreeFourEnvelope] using
    V11.SharpKernelDefect.finite_equation_three_four
      X T hT hTX hσpos hσ

end PaperC
