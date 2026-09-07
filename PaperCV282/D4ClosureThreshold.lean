import PaperCV282.PoissonThresholdTarget

/-! # The finite joint generating function of the complete threshold process

The last independent coordinate contains the entire upper tail. Thus this
formula concerns the actual infinite configuration, with no mark cutoff.
-/
namespace PaperC.V282.D4ClosureThreshold

open MeasureTheory ProbabilityTheory
open PoissonThresholdTarget ThresholdPathEquivalence GeometricMarkedConfiguration
open GaussianThresholdIncrements CompoundPoissonMarking PoissonFieldMeasure
open scoped BigOperators NNReal

noncomputable section

def prefixProduct (J : ℕ) (z : Fin (J+1) → ℂ) (i : Fin (J+1)) : ℂ :=
  ∏ j : Fin (J+1), if j.val ≤ i.val then z j else 1

theorem threshold_product_eq (J : ℕ) (z : Fin (J+1) → ℂ) (c : ℕ →₀ ℕ) :
    (∏ j : Fin (J+1), z j ^ tailCount c j.val) =
      ∏ i : Fin (J+1), prefixProduct J z i ^ clippedCounts J c i := by
  classical
  simp_rw [← sum_clippedCounts_tail J _ (Nat.le_of_lt_succ (Fin.isLt _)) c,
    ← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i hi
  rw [prefixProduct, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro j hj
  split_ifs <;> simp

/-- The joint PGF of all thresholds from zero through `J`, including their
common infinite tail. Complex arguments are allowed. -/
theorem threshold_joint_pgf (rate : ℝ≥0) (J : ℕ) (z : Fin (J+1) → ℂ) :
    (∫ c, ∏ j : Fin (J+1), z j ^ tailCount c j.val ∂configurationMeasure rate) =
      Complex.exp (∑ i : Fin (J+1),
        ((rate * incrementVariance J i : ℝ≥0) : ℂ) * (prefixProduct J z i - 1)) := by
  simp_rw [threshold_product_eq]
  exact ((hasLaw_clippedCounts rate J).integral_comp
    (measurable_of_countable (fun k : Fin (J+1) → ℕ =>
      ∏ i, prefixProduct J z i ^ k i)).aestronglyMeasurable).trans
        (field_product_transform _ _)

/-- This is the printed finite PGF, with the terminal upper-tail term
separated from the exact-level terms. -/
theorem threshold_joint_pgf_explicit (rate : ℝ≥0) (J : ℕ) (z : Fin (J+1) → ℂ) :
    (∫ c, ∏ j : Fin (J+1), z j ^ tailCount c j.val ∂configurationMeasure rate) =
      Complex.exp ((∑ i : Fin J,
        (rate : ℂ) / 2^(i.val+1) * (prefixProduct J z i.castSucc - 1)) +
          (rate : ℂ) / 2^J * ((∏ j : Fin (J+1), z j) - 1)) := by
  rw [threshold_joint_pgf, Fin.sum_univ_castSucc]
  congr 1
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    simp [incrementVariance, ne_of_lt i.isLt, div_eq_mul_inv]
  · have hlast : prefixProduct J z (Fin.last J) = ∏ j, z j := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [show j.val ≤ J by omega]
    rw [hlast]
    simp [incrementVariance, div_eq_mul_inv]

/-- Every individual threshold has the exact thinned Poisson law. -/
theorem hasLaw_tailCount (rate : ℝ≥0) (k : ℕ) :
    HasLaw (fun c => tailCount c k) (poissonMeasure (rate / 2^k))
      (configurationMeasure rate) := by
  have h := (hasLaw_coordinate (fun i : Fin (k+1) => rate * incrementVariance k i)
    (Fin.last k)).fun_comp (hasLaw_clippedCounts rate k)
  simpa [clippedCounts, incrementVariance, div_eq_mul_inv] using h

end
end PaperC.V282.D4ClosureThreshold
