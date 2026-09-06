import PaperCV282.PoissonConfigurationTransform

/-! # The joint threshold / exact-level target

The source is the genuine geometric Poisson configuration. The limiting target
is a product of the Gaussian threshold law and independent Poisson levels.
-/
namespace PaperC.V282.PoissonGaussianTarget

open MeasureTheory ProbabilityTheory WithLp Filter
open GeometricMarkedConfiguration GeometricClusterTarget PoissonConfigurationTransform
open PoissonThresholdTarget GaussianThresholdCovariance FinitePoissonCLT PoissonCLT
open scoped Topology NNReal

noncomputable section

variable {R : Type*} [Fintype R] [DecidableEq R]

def thresholdSignal (J : ℕ) (scale : ℝ) (t : EuclideanSpace ℝ (Fin (J+1))) (e : ℕ) : ℝ :=
  ∑ j : Fin (J+1), if j.val ≤ e then t j / scale else 0

def criticalSignal (excess : R → ℕ) (u : EuclideanSpace ℝ R) (e : ℕ) : ℝ :=
  ∑ r, if e = excess r then u r else 0

def thresholdCenter (rate : ℝ≥0) (J : ℕ) (t : EuclideanSpace ℝ (Fin (J+1))) : ℝ :=
  ∑ j : Fin (J+1), (rate : ℝ)/(2 : ℝ)^j.val * t j / Real.sqrt rate

def jointThresholdVector (rate : ℝ≥0) (J : ℕ) (excess : R → ℕ) (c : ℕ →₀ ℕ) :
    WithLp 2 ((EuclideanSpace ℝ (Fin (J+1))) × EuclideanSpace ℝ R) :=
  toLp 2 (normalizedThresholdVector rate J c, toLp 2 (fun r => (c (excess r) : ℝ)))

def jointThresholdLaw (rate : ℝ≥0) (J : ℕ) (excess : R → ℕ) :
    ProbabilityMeasure (WithLp 2 ((EuclideanSpace ℝ (Fin (J+1))) × EuclideanSpace ℝ R)) :=
  ⟨(configurationMeasure rate).map (jointThresholdVector rate J excess),
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable⟩

def poissonGaussianTarget (J : ℕ) (criticalRates : R → ℝ≥0) :
    ProbabilityMeasure (WithLp 2 ((EuclideanSpace ℝ (Fin (J+1))) × EuclideanSpace ℝ R)) :=
  ⟨(((gaussianThresholdLaw J : Measure (EuclideanSpace ℝ (Fin (J+1))))).prod
      (euclideanProductLaw (fun r => realPoissonLaw (criticalRates r)) : Measure (EuclideanSpace ℝ R))).map
      (toLp 2), Measure.isProbabilityMeasure_map (by fun_prop)⟩

omit [DecidableEq R] in
theorem charFun_poissonGaussianTarget (J : ℕ) (criticalRates : R → ℝ≥0)
    (t : WithLp 2 ((EuclideanSpace ℝ (Fin (J+1))) × EuclideanSpace ℝ R)) :
    charFun (poissonGaussianTarget J criticalRates : Measure _) t =
      charFun (gaussianThresholdLaw J : Measure _) (ofLp t).1 *
      Complex.exp (∑ r, (criticalRates r : ℂ) *
        (Complex.exp (((ofLp t).2 r : ℝ) * Complex.I) - 1)) := by
  simp only [poissonGaussianTarget, ProbabilityMeasure.coe_mk]
  rw [charFun_prod, charFun_euclideanProductLaw]
  simp only [realPoissonLaw, ProbabilityMeasure.coe_mk, charFun_map_cast_poissonMeasure,
    ← Complex.exp_sum]

theorem threshold_inner_linear (rate : ℝ≥0) (J : ℕ)
    (t : EuclideanSpace ℝ (Fin (J+1))) (c : ℕ →₀ ℕ) :
    inner ℝ (normalizedThresholdVector rate J c) t =
      configurationLinear (thresholdSignal J (Real.sqrt rate) t) c - thresholdCenter rate J t := by
  change inner ℝ (normalizedThresholdVector rate J c) t =
    configurationLinear (fun e => ∑ j : Fin (J+1), if j.val ≤ e then t j / Real.sqrt rate else 0) c - _
  simp only [configurationLinear_sum, configurationLinear_threshold,
    thresholdCenter, normalizedThresholdVector, PiLp.inner_apply, Real.inner_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

omit [DecidableEq R] in
theorem critical_inner_linear (excess : R → ℕ) (u : EuclideanSpace ℝ R) (c : ℕ →₀ ℕ) :
    inner ℝ (toLp 2 (fun r => (c (excess r) : ℝ)) : EuclideanSpace ℝ R) u =
      configurationLinear (criticalSignal excess u) c := by
  change _ = configurationLinear (fun e => ∑ r, if e = excess r then u r else 0) c
  simp only [configurationLinear_sum, configurationLinear_single,
    PiLp.inner_apply, Real.inner_apply]

omit [DecidableEq R] in
/-- Exact characteristic function of the joint vector on the genuine configuration. -/
theorem charFun_jointThresholdLaw (rate : ℝ≥0) (J : ℕ) (excess : R → ℕ)
    (t : WithLp 2 ((EuclideanSpace ℝ (Fin (J+1))) × EuclideanSpace ℝ R)) :
    charFun (jointThresholdLaw rate J excess : Measure _) t =
      Complex.exp ((rate : ℂ) * ((∫ h, Complex.exp (((positiveMarkLinear
        (fun e => thresholdSignal J (Real.sqrt rate) (ofLp t).1 e + criticalSignal excess (ofLp t).2 e)
        h : ℝ) : ℂ) * Complex.I) ∂geometricClusterMeasure) - 1) -
          (thresholdCenter rate J (ofLp t).1 : ℂ) * Complex.I) := by
  change charFun ((configurationMeasure rate).map (jointThresholdVector rate J excess)) t = _
  rw [charFun_apply, integral_map (measurable_of_countable _).aemeasurable (by fun_prop)]
  have he (c : ℕ →₀ ℕ) : inner ℝ (jointThresholdVector rate J excess c) t =
      configurationLinear (fun e => thresholdSignal J (Real.sqrt rate) (ofLp t).1 e +
        criticalSignal excess (ofLp t).2 e) c - thresholdCenter rate J (ofLp t).1 := by
    simp only [jointThresholdVector, prod_inner_apply, threshold_inner_linear,
      critical_inner_linear, configurationLinear_add]
    ring
  simp only [he]
  exact centered_configuration_complex_transform _ _ _

theorem charFun_normalizedThresholdLaw (rate : ℝ≥0) (J : ℕ)
    (t : EuclideanSpace ℝ (Fin (J+1))) :
    charFun (normalizedThresholdLaw rate J : Measure _) t =
      Complex.exp ((rate : ℂ) * ((∫ h, Complex.exp (((positiveMarkLinear
        (thresholdSignal J (Real.sqrt rate) t) h : ℝ) : ℂ) * Complex.I)
        ∂geometricClusterMeasure) - 1) - (thresholdCenter rate J t : ℂ) * Complex.I) := by
  change charFun ((configurationMeasure rate).map (normalizedThresholdVector rate J)) t = _
  rw [charFun_apply, integral_map (measurable_of_countable _).aemeasurable (by fun_prop)]
  simp only [threshold_inner_linear]
  exact centered_configuration_complex_transform _ _ _

theorem thresholdSignal_of_le (J : ℕ) (scale : ℝ) (t : EuclideanSpace ℝ (Fin (J+1)))
    (e : ℕ) (he : J ≤ e) : thresholdSignal J scale t e = (∑ j, t j) / scale := by
  unfold thresholdSignal
  have hj (j : Fin (J+1)) : j.val ≤ e := by omega
  simp only [hj, if_true, Finset.sum_div]

theorem criticalSignal_at (excess : R → ℕ) (hinj : Function.Injective excess)
    (u : EuclideanSpace ℝ R) (r : R) : criticalSignal excess u (excess r) = u r := by
  classical
  unfold criticalSignal
  have he (s : R) : excess r = excess s ↔ s = r := by
    constructor
    · intro h
      exact (hinj h).symm
    · rintro rfl
      rfl
  simp [he]

omit [DecidableEq R] in
theorem criticalSignal_of_not_mem (excess : R → ℕ) (u : EuclideanSpace ℝ R)
    (e : ℕ) (he : ∀ r, e ≠ excess r) : criticalSignal excess u e = 0 := by
  simp [criticalSignal, he]

end
end PaperC.V282.PoissonGaussianTarget
