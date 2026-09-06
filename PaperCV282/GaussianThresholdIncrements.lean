import PaperCV282.GaussianThresholdCovariance
import Mathlib.Algebra.Field.GeomSum

/-! # Independent increments representing the Gaussian threshold vector -/
namespace PaperC.V282.GaussianThresholdIncrements

open MeasureTheory ProbabilityTheory Matrix WithLp GaussianThresholdCovariance FinitePoissonCLT
open scoped BigOperators NNReal

noncomputable section

def incrementVariance (J : ℕ) (i : Fin (J+1)) : ℝ≥0 :=
  if i.val = J then 1 / 2^J else 1 / 2^(i.val+1)

theorem tail_geometric_sum (k n : ℕ) (hkn : k ≤ n) :
    (∑ i ∈ Finset.Ico k n, 1 / (2 : ℝ)^(i+1)) + 1/(2 : ℝ)^n = 1/(2 : ℝ)^k := by
  induction n generalizing k with
  | zero =>
    obtain rfl : k = 0 := by omega
    simp
  | succ n ih =>
    by_cases h : k ≤ n
    · rw [Finset.sum_Ico_succ_top h]
      calc
        _ = (∑ i ∈ Finset.Ico k n, 1/(2 : ℝ)^(i+1)) + 1/(2 : ℝ)^n := by
          rw [pow_succ]
          ring
        _ = _ := ih k h
    · obtain rfl : k = n+1 := by omega
      simp

theorem sum_tail_incrementVariance (J k : ℕ) (hk : k ≤ J) :
    (∑ i : Fin (J+1), if k ≤ i.val then (incrementVariance J i : ℝ) else 0) =
      1/(2 : ℝ)^k := by
  rw [Fin.sum_univ_castSucc]
  have hlast : (if k ≤ (Fin.last J).val then (incrementVariance J (Fin.last J) : ℝ) else 0) =
      1/(2 : ℝ)^J := by simp [incrementVariance, hk]
  rw [hlast]
  have heq : (∑ i : Fin J, if k ≤ i.castSucc.val then
      (incrementVariance J i.castSucc : ℝ) else 0) =
      ∑ i ∈ Finset.Ico k J, 1/(2 : ℝ)^(i+1) := by
    simp only [Fin.val_castSucc]
    have hi (i : Fin J) : (incrementVariance J i.castSucc : ℝ) = 1/(2 : ℝ)^(i.val+1) := by
      simp [incrementVariance, ne_of_lt i.isLt]
    simp_rw [hi]
    rw [Fin.sum_univ_eq_sum_range (fun i => if k ≤ i then 1/(2:ℝ)^(i+1) else 0) J,
      ← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [heq]
  exact tail_geometric_sum k J hk

def thresholdSum (J : ℕ) (x : EuclideanSpace ℝ (Fin (J+1))) :
    EuclideanSpace ℝ (Fin (J+1)) :=
  toLp 2 (fun j => ∑ i : Fin (J+1), if j.val ≤ i.val then x i else 0)

theorem continuous_thresholdSum (J : ℕ) : Continuous (thresholdSum J) := by
  unfold thresholdSum
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro j
  apply continuous_finsetSum
  intro i hi
  split_ifs <;> fun_prop

/-- The quadratic form of the summed independent increments is the stated kernel. -/
theorem increment_quadratic_eq_covariance (J : ℕ) (t : EuclideanSpace ℝ (Fin (J+1))) :
    (∑ i : Fin (J+1), (incrementVariance J i : ℝ) *
      (∑ j : Fin (J+1), if j.val ≤ i.val then t j else 0)^2) =
      t ⬝ᵥ (thresholdCovariance J) *ᵥ t := by
  simp only [pow_two, Finset.sum_mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]
  change (∑ k, ∑ i, (incrementVariance J i : ℝ) *
    ((if j.val ≤ i.val then t j else 0) * (if k.val ≤ i.val then t k else 0))) = _
  change _ = t j * ∑ k, (thresholdCovariance J) j k * t k
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have heq (i : Fin (J+1)) : (incrementVariance J i : ℝ) *
      ((if j.val ≤ i.val then t j else 0) * (if k.val ≤ i.val then t k else 0)) =
        t j * t k * (if max j.val k.val ≤ i.val then (incrementVariance J i : ℝ) else 0) := by
    by_cases hj : j.val ≤ i.val <;> by_cases hk : k.val ≤ i.val <;>
      simp [hj, hk]
    ring
  simp_rw [heq]
  rw [← Finset.mul_sum, sum_tail_incrementVariance J (max j.val k.val)
    (by have := j.isLt; have := k.isLt; omega)]
  simp only [thresholdCovariance]
  ring

/-- The transpose action of the threshold sum on a characteristic-function test. -/
def thresholdTest (J : ℕ) (t : EuclideanSpace ℝ (Fin (J+1))) :
    EuclideanSpace ℝ (Fin (J+1)) :=
  toLp 2 (fun i => ∑ j : Fin (J+1), if j.val ≤ i.val then t j else 0)

theorem threshold_inner (J : ℕ) (x t : EuclideanSpace ℝ (Fin (J+1))) :
    inner ℝ (thresholdSum J x) t = inner ℝ x (thresholdTest J t) := by
  simp only [PiLp.inner_apply, Real.inner_apply, thresholdSum, thresholdTest,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> simp

theorem charFun_map_thresholdSum (J : ℕ)
    (mu : Measure (EuclideanSpace ℝ (Fin (J+1)))) (t : EuclideanSpace ℝ (Fin (J+1))) :
    charFun (mu.map (thresholdSum J)) t = charFun mu (thresholdTest J t) := by
  simp only [charFun_apply]
  rw [integral_map (continuous_thresholdSum J).measurable.aemeasurable (by fun_prop)]
  simp only [threshold_inner]

/-- The independent-increment representation has exactly the target Gaussian law. -/
theorem map_gaussian_increments (J : ℕ) :
    (euclideanProductLaw (fun i => PoissonCLT.centeredGaussianLaw (incrementVariance J i))).map
      (continuous_thresholdSum J).measurable.aemeasurable = gaussianThresholdLaw J := by
  apply Subtype.ext
  change ((euclideanProductLaw (fun i => PoissonCLT.centeredGaussianLaw (incrementVariance J i)) :
      Measure _).map (thresholdSum J)) = multivariateGaussian 0 (thresholdCovariance J)
  apply Measure.ext_of_charFun
  funext t
  change charFun ((euclideanProductLaw (fun i =>
    PoissonCLT.centeredGaussianLaw (incrementVariance J i)) : Measure _).map (thresholdSum J)) t = _
  rw [charFun_map_thresholdSum, charFun_euclideanProductLaw]
  rw [show charFun (multivariateGaussian 0 (thresholdCovariance J)) t =
    Complex.exp (-(t ⬝ᵥ (thresholdCovariance J) *ᵥ t : ℝ) / 2) from gaussianThresholdLaw_charFun J t]
  simp only [PoissonCLT.centeredGaussianLaw, ProbabilityMeasure.coe_mk, charFun_gaussianReal,
    Complex.ofReal_zero, mul_zero, zero_mul, zero_sub, ← Complex.exp_sum]
  congr 1
  rw [Finset.sum_neg_distrib, ← Finset.sum_div, neg_div]
  congr 1
  simp_rw [← Complex.ofReal_pow, ← Complex.ofReal_mul]
  rw [← Complex.ofReal_sum]
  congr 1
  simpa only [thresholdTest, PiLp.toLp_apply] using
    congrArg (fun r : ℝ => (r : ℂ)) (increment_quadratic_eq_covariance J t)

end
end PaperC.V282.GaussianThresholdIncrements
