import PaperCV282.FinitePoissonCLT
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Function.L2Space

/-! # The actual Gaussian threshold vector of Theorem 5.10

The covariance kernel is positive semidefinite because it is the measure of
intersections of the real intervals [0,2^(-j)]. Thus the target is an actual
Gaussian probability law, including all its stated covariances.
-/
namespace PaperC.V282.GaussianThresholdCovariance

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

noncomputable section

def thresholdCovariance (J : ℕ) : Matrix (Fin (J+1)) (Fin (J+1)) ℝ :=
  fun j k => 1 / (2 : ℝ) ^ max j.val k.val

theorem min_inverse_two_pow (j k : ℕ) :
    min (1 / (2 : ℝ)^j) (1 / (2 : ℝ)^k) = 1 / (2 : ℝ)^max j k := by
  rcases le_total j k with h | h
  · rw [max_eq_right h, min_eq_right]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) h)
  · rw [max_eq_left h, min_eq_left]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) h)

theorem thresholdCovariance_posSemidef (J : ℕ) : (thresholdCovariance J).PosSemidef := by
  have heq : thresholdCovariance J = Matrix.of (fun j k : Fin (J+1) =>
      volume.real ((Set.Icc 0 (1/(2:ℝ)^j.val)) ∩ (Set.Icc 0 (1/(2:ℝ)^k.val)))) := by
    ext j k
    simpa [thresholdCovariance, Set.Icc_inter_Icc] using
      (min_inverse_two_pow j.val k.val).symm
  rw [heq]
  exact posSemidef_matrix_measure_inter (fun _ => measurableSet_Icc)
    (fun _ => isCompact_Icc.measure_ne_top)

def gaussianThresholdLaw (J : ℕ) : ProbabilityMeasure (EuclideanSpace ℝ (Fin (J+1))) :=
  ⟨multivariateGaussian 0 (thresholdCovariance J), inferInstance⟩

theorem gaussianThresholdLaw_mean (J : ℕ) :
    ∫ x, x ∂(gaussianThresholdLaw J : Measure (EuclideanSpace ℝ (Fin (J+1)))) = 0 :=
  integral_id_multivariateGaussian

theorem gaussianThresholdLaw_covariance (J : ℕ) (j k : Fin (J+1)) :
    cov[fun x => x j, fun x => x k;
      (gaussianThresholdLaw J : Measure (EuclideanSpace ℝ (Fin (J+1))))] =
        1 / (2 : ℝ)^max j.val k.val :=
  covariance_eval_multivariateGaussian (thresholdCovariance_posSemidef J) j k

theorem gaussianThresholdLaw_charFun (J : ℕ) (t : EuclideanSpace ℝ (Fin (J+1))) :
    charFun (gaussianThresholdLaw J : Measure (EuclideanSpace ℝ (Fin (J+1)))) t =
      Complex.exp (-(t ⬝ᵥ (thresholdCovariance J) *ᵥ t : ℝ) / 2) := by
  simpa [gaussianThresholdLaw, neg_div] using charFun_multivariateGaussian (μ := 0) (thresholdCovariance_posSemidef J) t

end
end PaperC.V282.GaussianThresholdCovariance
