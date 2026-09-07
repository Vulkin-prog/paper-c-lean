import PaperCV282.GaussianThresholdCovariance
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-! # The stationary Gaussian normalization and its AR(1) innovations -/
namespace PaperC.V282.GaussianThresholdAR

open MeasureTheory ProbabilityTheory GaussianThresholdCovariance
open scoped Topology NNReal

noncomputable section

def standardizedProjection (J : ℕ) (j : Fin (J+1)) :
    EuclideanSpace ℝ (Fin (J+1)) →L[ℝ] ℝ :=
  (2 : ℝ)^((j.val : ℝ)/2) • EuclideanSpace.proj j

theorem standardizedProjection_apply (J : ℕ) (j : Fin (J+1))
    (x : EuclideanSpace ℝ (Fin (J+1))) :
    standardizedProjection J j x = (2 : ℝ)^((j.val : ℝ)/2) * x j := rfl

theorem standardizedProjection_gaussian (J : ℕ) (j : Fin (J+1)) :
    HasGaussianLaw (standardizedProjection J j)
      (gaussianThresholdLaw J : Measure (EuclideanSpace ℝ (Fin (J+1)))) := by
  change HasGaussianLaw (standardizedProjection J j) (multivariateGaussian 0 (thresholdCovariance J))
  exact IsGaussian.hasGaussianLaw_id.map (standardizedProjection J j)

theorem standardizedProjection_mean (J : ℕ) (j : Fin (J+1)) :
    ∫ x, standardizedProjection J j x ∂(gaussianThresholdLaw J : Measure _) = 0 := by
  change ∫ x, standardizedProjection J j x ∂multivariateGaussian 0 (thresholdCovariance J) = 0
  rw [(standardizedProjection J j).integral_comp_comm IsGaussian.integrable_fun_id]
  simp

theorem normalized_covariance_numeric (j k : ℕ) :
    (2 : ℝ)^((j : ℝ)/2) * ((2 : ℝ)^((k : ℝ)/2) * (1/(2 : ℝ)^max j k)) =
      (2 : ℝ)^(-|(j : ℝ)-(k : ℝ)|/2) := by
  rw [mul_one_div, ← mul_div_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ)<2),
    ← Real.rpow_natCast, ← Real.rpow_sub (by norm_num : (0 : ℝ)<2)]
  congr 1
  rcases le_total j k with h | h
  · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h))]
    ring
  · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]
    ring

/-- The standardized target has the stationary AR(1) covariance. -/
theorem standardizedProjection_covariance (J : ℕ) (j k : Fin (J+1)) :
    cov[standardizedProjection J j, standardizedProjection J k;
      (gaussianThresholdLaw J : Measure (EuclideanSpace ℝ (Fin (J+1))))] =
      (2 : ℝ)^(-|(j.val : ℝ)-(k.val : ℝ)|/2) := by
  change cov[fun x => (2 : ℝ)^((j.val : ℝ)/2) * x j,
    fun x => (2 : ℝ)^((k.val : ℝ)/2) * x k;
      (gaussianThresholdLaw J : Measure (EuclideanSpace ℝ (Fin (J+1))))] = _
  simp only [covariance_const_mul_left, covariance_const_mul_right,
    gaussianThresholdLaw_covariance]
  simpa only [mul_left_comm] using normalized_covariance_numeric j.val k.val

theorem standardizedProjection_variance (J : ℕ) (j : Fin (J+1)) :
    Var[standardizedProjection J j; (gaussianThresholdLaw J : Measure _)] = 1 := by
  rw [← covariance_self (standardizedProjection_gaussian J j).aemeasurable,
    standardizedProjection_covariance]
  simp

/-- Every standardized coordinate is genuinely standard normal. -/
theorem hasLaw_standardizedProjection (J : ℕ) (j : Fin (J+1)) :
    HasLaw (standardizedProjection J j) (gaussianReal 0 1)
      (gaussianThresholdLaw J : Measure _) := by
  refine ⟨(standardizedProjection_gaussian J j).aemeasurable, ?_⟩
  rw [(standardizedProjection_gaussian J j).map_eq_gaussianReal,
    standardizedProjection_mean, standardizedProjection_variance]
  simp

def innovationProjection (J : ℕ) (j : Fin J) :
    EuclideanSpace ℝ (Fin (J+1)) →L[ℝ] ℝ :=
  (2 : ℝ)^((1 : ℝ)/2) • standardizedProjection J j.succ - standardizedProjection J j.castSucc

theorem innovationProjection_apply (J : ℕ) (j : Fin J)
    (x : EuclideanSpace ℝ (Fin (J+1))) :
    innovationProjection J j x =
      (2 : ℝ)^((1 : ℝ)/2) * standardizedProjection J j.succ x -
        standardizedProjection J j.castSucc x := rfl

theorem innovationProjection_gaussian (J : ℕ) (j : Fin J) :
    HasGaussianLaw (innovationProjection J j)
      (gaussianThresholdLaw J : Measure (EuclideanSpace ℝ (Fin (J+1)))) := by
  change HasGaussianLaw (innovationProjection J j) (multivariateGaussian 0 (thresholdCovariance J))
  exact IsGaussian.hasGaussianLaw_id.map (innovationProjection J j)

theorem innovationProjection_mean (J : ℕ) (j : Fin J) :
    ∫ x, innovationProjection J j x ∂(gaussianThresholdLaw J : Measure _) = 0 := by
  change ∫ x, innovationProjection J j x ∂multivariateGaussian 0 (thresholdCovariance J) = 0
  rw [(innovationProjection J j).integral_comp_comm IsGaussian.integrable_fun_id]
  simp

theorem ar_coefficient_identity : (2 : ℝ)^(-(1 : ℝ)/2) * (2 : ℝ)^((1 : ℝ)/2) = 1 := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ)<2)]
  norm_num

/-- The AR(1) recursion holds pointwise, with the innovations constructed above. -/
theorem standardized_ar_recursion (J : ℕ) (j : Fin J)
    (x : EuclideanSpace ℝ (Fin (J+1))) :
    standardizedProjection J j.succ x =
      (2 : ℝ)^(-(1 : ℝ)/2) * standardizedProjection J j.castSucc x +
      (2 : ℝ)^(-(1 : ℝ)/2) * innovationProjection J j x := by
  rw [innovationProjection_apply]
  calc
    _ = ((2 : ℝ)^(-(1 : ℝ)/2) * (2 : ℝ)^((1 : ℝ)/2)) *
        standardizedProjection J j.succ x := by rw [ar_coefficient_identity, one_mul]
    _ = _ := by ring

/-- Each innovation is orthogonal to every earlier standardized coordinate. -/
theorem innovation_covariance_past (J : ℕ) (j : Fin J) (k : Fin (J+1)) (hk : k.val ≤ j.val) :
    cov[innovationProjection J j, standardizedProjection J k;
      (gaussianThresholdLaw J : Measure (EuclideanSpace ℝ (Fin (J+1))))] = 0 := by
  change cov[fun x => (2 : ℝ)^((1 : ℝ)/2) * standardizedProjection J j.succ x -
    standardizedProjection J j.castSucc x, standardizedProjection J k;
      (gaussianThresholdLaw J : Measure (EuclideanSpace ℝ (Fin (J+1))))] = 0
  rw [covariance_fun_sub_left ((standardizedProjection_gaussian J j.succ).memLp_two.const_mul _)
    (standardizedProjection_gaussian J j.castSucc).memLp_two
    (standardizedProjection_gaussian J k).memLp_two,
    covariance_const_mul_left, standardizedProjection_covariance, standardizedProjection_covariance]
  have h1 : (0 : ℝ) ≤ ((j.succ.val : ℝ) - (k.val : ℝ)) := by
    exact sub_nonneg.mpr (by exact_mod_cast (show k.val ≤ j.succ.val by
      simpa only [Fin.val_succ] using Nat.le_succ_of_le hk))
  have h0 : (0 : ℝ) ≤ ((j.castSucc.val : ℝ) - (k.val : ℝ)) := by
    exact sub_nonneg.mpr (by exact_mod_cast hk)
  rw [abs_of_nonneg h1, abs_of_nonneg h0,
    ← Real.rpow_add (by norm_num : (0 : ℝ)<2)]
  have he : (1 : ℝ)/2 + -((j.succ.val : ℝ) - (k.val : ℝ))/2 =
      -((j.castSucc.val : ℝ) - (k.val : ℝ))/2 := by
    simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
    ring
  rw [he, sub_self]

theorem innovationProjection_variance (J : ℕ) (j : Fin J) :
    Var[innovationProjection J j; (gaussianThresholdLaw J : Measure _)] = 1 := by
  change Var[fun x => (2 : ℝ)^((1 : ℝ)/2) * standardizedProjection J j.succ x -
    standardizedProjection J j.castSucc x; (gaussianThresholdLaw J : Measure _)] = 1
  rw [variance_fun_sub ((standardizedProjection_gaussian J j.succ).memLp_two.const_mul _)
    (standardizedProjection_gaussian J j.castSucc).memLp_two,
    variance_const_mul, standardizedProjection_variance, standardizedProjection_variance,
    covariance_const_mul_left, standardizedProjection_covariance]
  have he : |((j.succ.val : ℝ) - (j.castSucc.val : ℝ))| = 1 := by
    simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
    ring_nf
    norm_num
  rw [he]
  have ha2 : ((2 : ℝ)^((1 : ℝ)/2))^2 = 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ)≤2)]
    norm_num
  have haa : (2 : ℝ)^((1 : ℝ)/2) * (2 : ℝ)^(-(1 : ℝ)/2) = 1 := by
    simpa only [mul_comm] using ar_coefficient_identity
  nlinarith [ha2, haa]

theorem hasLaw_innovationProjection (J : ℕ) (j : Fin J) :
    HasLaw (innovationProjection J j) (gaussianReal 0 1)
      (gaussianThresholdLaw J : Measure _) := by
  refine ⟨(innovationProjection_gaussian J j).aemeasurable, ?_⟩
  rw [(innovationProjection_gaussian J j).map_eq_gaussianReal,
    innovationProjection_mean, innovationProjection_variance]
  simp

theorem innovation_covariance_innovation (J : ℕ) (i j : Fin J) (hij : i ≠ j) :
    cov[innovationProjection J i, innovationProjection J j;
      (gaussianThresholdLaw J : Measure (EuclideanSpace ℝ (Fin (J+1))))] = 0 := by
  have hordered (i j : Fin J) (hji : j.val < i.val) :
      cov[innovationProjection J i, innovationProjection J j;
        (gaussianThresholdLaw J : Measure (EuclideanSpace ℝ (Fin (J+1))))] = 0 := by
    change cov[innovationProjection J i, fun x =>
      (2 : ℝ)^((1 : ℝ)/2) * standardizedProjection J j.succ x -
        standardizedProjection J j.castSucc x; (gaussianThresholdLaw J : Measure _)] = 0
    rw [covariance_fun_sub_right (innovationProjection_gaussian J i).memLp_two
      ((standardizedProjection_gaussian J j.succ).memLp_two.const_mul _)
      (standardizedProjection_gaussian J j.castSucc).memLp_two,
      covariance_const_mul_right, innovation_covariance_past J i j.succ (by simpa only [Fin.val_succ] using Nat.succ_le_of_lt hji),
      innovation_covariance_past J i j.castSucc (by simpa only [Fin.val_castSucc] using hji.le)]
    ring
  rcases lt_or_gt_of_ne (show i.val ≠ j.val from fun h => hij (Fin.ext h)) with h | h
  · rw [covariance_comm]
    exact hordered j i h
  · exact hordered i j h

/-- Initial state and subsequent innovations, as continuous linear observables. -/
def arNoiseProjection (J : ℕ) (i : Option (Fin J)) :
    EuclideanSpace ℝ (Fin (J+1)) →L[ℝ] ℝ :=
  match i with
  | none => standardizedProjection J 0
  | some j => innovationProjection J j

/-- The AR(1) initial state and all innovations are genuinely independent. -/
theorem arNoises_independent (J : ℕ) :
    iIndepFun (fun i : Option (Fin J) => arNoiseProjection J i)
      (gaussianThresholdLaw J : Measure (EuclideanSpace ℝ (Fin (J+1)))) := by
  have hG : HasGaussianLaw (fun x => fun i : Option (Fin J) => arNoiseProjection J i x)
      (gaussianThresholdLaw J : Measure (EuclideanSpace ℝ (Fin (J+1)))) := by
    change HasGaussianLaw (fun x => fun i : Option (Fin J) => arNoiseProjection J i x)
      (multivariateGaussian 0 (thresholdCovariance J))
    exact IsGaussian.hasGaussianLaw_id.map (ContinuousLinearMap.pi (arNoiseProjection J))
  apply hG.iIndepFun_of_covariance_eq_zero
  intro i j hij
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some j =>
      change cov[standardizedProjection J 0, innovationProjection J j;
        (gaussianThresholdLaw J : Measure _)] = 0
      rw [covariance_comm]
      exact innovation_covariance_past J j 0 (by simp)
  | some i =>
    cases j with
    | none => exact innovation_covariance_past J i 0 (by simp)
    | some j => exact innovation_covariance_innovation J i j (by simpa using hij)

theorem hasLaw_arNoise (J : ℕ) (i : Option (Fin J)) :
    HasLaw (arNoiseProjection J i) (gaussianReal 0 1) (gaussianThresholdLaw J : Measure _) := by
  cases i with
  | none => exact hasLaw_standardizedProjection J 0
  | some i => exact hasLaw_innovationProjection J i

end
end PaperC.V282.GaussianThresholdAR
