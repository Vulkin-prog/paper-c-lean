import PaperCV282.PoissonGaussianTarget

/-! # Exact interaction between moving Gaussian thresholds and fixed Poisson levels -/
namespace PaperC.V282.PoissonGaussianTransform

open MeasureTheory ProbabilityTheory WithLp Filter
open PoissonGaussianTarget PoissonConfigurationTransform GeometricClusterTarget
open PoissonThresholdTarget GaussianThresholdCovariance FinitePoissonCLT PoissonCLT
open scoped Topology NNReal

noncomputable section

variable {R : Type*} [Fintype R] [DecidableEq R]

theorem integrable_exp_real (g : ℕ → ℝ) :
    Integrable (fun h => Complex.exp ((g h : ℝ) * Complex.I)) geometricClusterMeasure := by
  refine ⟨(measurable_of_countable _).aestronglyMeasurable, ?_⟩
  apply HasFiniteIntegral.of_bounded (C := 1)
  exact Filter.Eventually.of_forall (fun h => by simp)

theorem spike_integrable (n : ℕ) (z : ℂ) :
    Integrable (fun h : ℕ => if h=n then z else 0) geometricClusterMeasure := by
  have he : ({n} : Set ℕ).indicator (fun _ => z) = (fun h : ℕ => if h=n then z else 0) := by
    funext h
    by_cases hh : h = n <;> simp [hh]
  rw [← he]
  exact (integrable_const (μ := geometricClusterMeasure) z).indicator (measurableSet_singleton n)

theorem integral_spike (n : ℕ) (z : ℂ) :
    (∫ h : ℕ, if h=n then z else 0 ∂geometricClusterMeasure) =
      (geometricClusterMeasure.real {n} : ℂ) * z := by
  simpa [Pi.single_apply] using integral_indicator_const (μ := geometricClusterMeasure) z (measurableSet_singleton n)

theorem mark_exponential_correction (J : ℕ) (scale : ℝ)
    (t : EuclideanSpace ℝ (Fin (J+1))) (u : EuclideanSpace ℝ R) (excess : R → ℕ)
    (hinj : Function.Injective excess) (hlarge : ∀ r, J ≤ excess r) (h : ℕ) :
    Complex.exp ((positiveMarkLinear (fun e => thresholdSignal J scale t e + criticalSignal excess u e) h : ℝ)
      * Complex.I) =
      Complex.exp ((positiveMarkLinear (thresholdSignal J scale t) h : ℝ) * Complex.I) +
      ∑ r, if h = excess r + 1 then
        Complex.exp ((((∑ j, t j) / scale : ℝ) : ℂ) * Complex.I) *
          (Complex.exp ((u r : ℝ) * Complex.I) - 1) else 0 := by
  by_cases hex : ∃ r, h = excess r + 1
  · obtain ⟨r, rfl⟩ := hex
    have he (s : R) : excess r + 1 = excess s + 1 ↔ s = r := by
      constructor
      · intro h
        exact (hinj (by omega)).symm
      · rintro rfl
        rfl
    simp only [he, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hp : 0 < excess r + 1 := Nat.succ_pos _
    simp only [positiveMarkLinear, if_pos hp, Nat.add_sub_cancel,
      criticalSignal_at excess hinj u r, thresholdSignal_of_le J scale t (excess r) (hlarge r),
      Complex.ofReal_add, add_mul, Complex.exp_add]
    ring
  · have he (r : R) : h ≠ excess r+1 := by aesop
    simp only [he, if_false, Finset.sum_const_zero, add_zero]
    by_cases hh : 0 < h
    · have hnot (r : R) : h-1 ≠ excess r := by
        intro hh'
        exact he r (by omega)
      simp [positiveMarkLinear, hh, criticalSignal_of_not_mem excess u (h-1) hnot]
    · simp [positiveMarkLinear, hh]

theorem integral_mark_exponential_correction (J : ℕ) (scale : ℝ)
    (t : EuclideanSpace ℝ (Fin (J+1))) (u : EuclideanSpace ℝ R) (excess : R → ℕ)
    (hinj : Function.Injective excess) (hlarge : ∀ r, J ≤ excess r) :
    (∫ h, Complex.exp ((positiveMarkLinear
      (fun e => thresholdSignal J scale t e + criticalSignal excess u e) h : ℝ) * Complex.I)
      ∂geometricClusterMeasure) =
    (∫ h, Complex.exp ((positiveMarkLinear (thresholdSignal J scale t) h : ℝ) * Complex.I)
      ∂geometricClusterMeasure) +
      ∑ r, ((1/(2 : ℝ)^(excess r+1) : ℝ) : ℂ) *
        (Complex.exp ((((∑ j, t j)/scale : ℝ) : ℂ) * Complex.I) *
          (Complex.exp ((u r : ℝ) * Complex.I) - 1)) := by
  simp_rw [mark_exponential_correction J scale t u excess hinj hlarge]
  rw [integral_add (integrable_exp_real _) (integrable_finsetSum _ (fun r _ => spike_integrable _ _)),
    integral_finsetSum _ (fun r _ => spike_integrable _ _)]
  simp only [integral_spike, geometricClusterMeasure_real_succ]

/-- The only finite-parameter dependence is an explicit vanishing phase factor. -/
theorem charFun_joint_factorization (rate : ℝ≥0) (J : ℕ) (excess : R → ℕ)
    (hinj : Function.Injective excess) (hlarge : ∀ r, J ≤ excess r)
    (t : WithLp 2 ((EuclideanSpace ℝ (Fin (J+1))) × EuclideanSpace ℝ R)) :
    charFun (jointThresholdLaw rate J excess : Measure _) t =
      charFun (normalizedThresholdLaw rate J : Measure _) (ofLp t).1 *
      Complex.exp (Complex.exp (((((∑ j, (ofLp t).1 j)/Real.sqrt rate : ℝ) : ℂ)) * Complex.I) *
        ∑ r, (((rate : ℝ)/(2 : ℝ)^(excess r+1) : ℝ) : ℂ) *
          (Complex.exp (((ofLp t).2 r : ℝ) * Complex.I) - 1)) := by
  rw [charFun_jointThresholdLaw, integral_mark_exponential_correction _ _ _ _ _ hinj hlarge,
    charFun_normalizedThresholdLaw, ← Complex.exp_add]
  congr 1
  have he : (rate : ℂ) * ∑ r, ((1/(2 : ℝ)^(excess r+1) : ℝ) : ℂ) *
      (Complex.exp (((((∑ j, (ofLp t).1 j)/Real.sqrt rate : ℝ) : ℂ)) * Complex.I) *
        (Complex.exp (((ofLp t).2 r : ℝ) * Complex.I) - 1)) =
      Complex.exp (((((∑ j, (ofLp t).1 j)/Real.sqrt rate : ℝ) : ℂ)) * Complex.I) *
        ∑ r, (((rate : ℝ)/(2 : ℝ)^(excess r+1) : ℝ) : ℂ) *
          (Complex.exp (((ofLp t).2 r : ℝ) * Complex.I) - 1) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    push_cast
    ring
  linear_combination he

end
end PaperC.V282.PoissonGaussianTransform
