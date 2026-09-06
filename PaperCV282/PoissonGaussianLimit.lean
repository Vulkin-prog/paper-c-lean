import PaperCV282.PoissonGaussianTransform

/-! # A joint Gaussian / critical-Poisson limit on the true geometric target

No independent replacement of the source configuration is made. The exact
finite-parameter interaction is computed before taking the limit.
-/
namespace PaperC.V282.PoissonGaussianLimit

open MeasureTheory ProbabilityTheory WithLp Filter
open PoissonGaussianTarget PoissonGaussianTransform PoissonThresholdTarget
open GaussianThresholdCovariance
open scoped Topology NNReal

noncomputable section

variable {R : Type*} [Fintype R] [DecidableEq R]

/-- The exact target part of Theorem 5.10, for any moving distinct critical levels. -/
theorem jointThresholdLaw_tendsto (rates : ℕ → ℝ≥0) (J : ℕ) (excess : ℕ → R → ℕ)
    (criticalRates : R → ℝ≥0)
    (hrates : Tendsto (fun n => (rates n : ℝ)) atTop atTop)
    (hinj : ∀ᶠ n in atTop, Function.Injective (excess n))
    (hlarge : ∀ᶠ n in atTop, ∀ r, J ≤ excess n r)
    (hcritical : ∀ r, Tendsto (fun n => (rates n : ℝ)/(2 : ℝ)^(excess n r+1))
      atTop (𝓝 (criticalRates r : ℝ))) :
    Tendsto (fun n => jointThresholdLaw (rates n) J (excess n)) atTop
      (𝓝 (poissonGaussianTarget J criticalRates)) := by
  apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr
  intro t
  rw [charFun_poissonGaussianTarget]
  have hbase := ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp
    (normalizedThresholdLaw_tendsto rates J hrates) (ofLp t).1
  have hphase : Tendsto (fun n => Complex.exp
      (((((∑ j, (ofLp t).1 j) / Real.sqrt (rates n) : ℝ) : ℂ)) * Complex.I)) atTop (𝓝 1) := by
    have hz : Tendsto (fun n => (∑ j, (ofLp t).1 j) / Real.sqrt (rates n)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hrates)
    have h := Complex.continuous_exp.continuousAt.tendsto.comp
      ((Complex.continuous_ofReal.continuousAt.tendsto.comp hz).mul_const Complex.I)
    simpa only [Function.comp_def, Complex.ofReal_zero, zero_mul, Complex.exp_zero] using h
  have hsum : Tendsto (fun n => ∑ r,
      (((rates n : ℝ)/(2 : ℝ)^(excess n r+1) : ℝ) : ℂ) *
        (Complex.exp (((ofLp t).2 r : ℝ) * Complex.I) - 1)) atTop
      (𝓝 (∑ r, (criticalRates r : ℂ) *
        (Complex.exp (((ofLp t).2 r : ℝ) * Complex.I) - 1))) :=
    tendsto_finsetSum _ (fun r _ =>
      (Complex.continuous_ofReal.continuousAt.tendsto.comp (hcritical r)).mul_const _)
  have hcorr := Complex.continuous_exp.continuousAt.tendsto.comp (hphase.mul hsum)
  have h := hbase.mul hcorr
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [hinj, hlarge] with n hi hl
  exact (charFun_joint_factorization (rates n) J (excess n) hi hl t).symm

end
end PaperC.V282.PoissonGaussianLimit
