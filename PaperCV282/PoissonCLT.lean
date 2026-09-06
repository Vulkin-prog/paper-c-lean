import PaperCV282.CompoundPoissonTransform
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Weak Gaussian limits of actual normalized Poisson variables

The proof uses the exact Poisson characteristic function and the second-order
Taylor expansion of the complex exponential. No central limit or Berry
estimate is introduced as an external premise.
-/
namespace PaperC.V282.PoissonCLT

open MeasureTheory ProbabilityTheory Filter CompoundPoissonTransform
open scoped Topology NNReal

noncomputable section

def centeredScaledPoissonLaw (rate : ℝ≥0) (scale : ℝ) : ProbabilityMeasure ℝ :=
  ⟨(poissonMeasure rate).map (fun k : ℕ => ((k : ℝ) - (rate : ℝ)) / scale),
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable⟩

theorem charFun_centeredScaledPoissonLaw (rate : ℝ≥0) (scale t : ℝ) :
    charFun (centeredScaledPoissonLaw rate scale : Measure ℝ) t =
      Complex.exp ((rate : ℂ) * (Complex.exp (((t / scale : ℝ) : ℂ) * Complex.I) - 1 -
        ((t / scale : ℝ) : ℂ) * Complex.I)) := by
  rw [charFun_apply]
  simp only [Real.inner_apply]
  change (∫ x, Complex.exp ((x * t : ℝ) * Complex.I) ∂
    ((poissonMeasure rate).map (fun k : ℕ => ((k : ℝ) - (rate : ℝ)) / scale))) = _
  rw [integral_map (measurable_of_countable _).aemeasurable (by fun_prop)]
  let z : ℂ := ((t / scale : ℝ) : ℂ) * Complex.I
  have hexp (k : ℕ) :
      Complex.exp (((((k : ℝ) - (rate : ℝ)) / scale) * t : ℝ) * Complex.I) =
        (Complex.exp z) ^ k * Complex.exp (-(rate : ℂ) * z) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    dsimp [z]
    push_cast
    ring
  simp_rw [hexp]
  rw [integral_mul_const, integral_poisson_complex_powers, ← Complex.exp_add]
  congr 1
  dsimp [z]
  ring

/-- A second-order Poisson exponent limit, usable for joint triangular arrays. -/
theorem poisson_exponent_tendsto (a z : ℕ → ℂ) (v : ℂ)
    (hz : Tendsto z atTop (𝓝 0))
    (hquad : Tendsto (fun n => a n * (z n)^2) atTop (𝓝 v)) :
    Tendsto (fun n => a n * (Complex.exp (z n) - 1 - z n)) atTop (𝓝 (v / 2)) := by
  have hrem : (fun n => Complex.exp (z n) - 1 - z n - (z n)^2 / 2) =o[atTop]
      (fun n => (z n)^2) := by
    have h := (Complex.exp_sub_sum_range_succ_isLittleO_pow 2).comp_tendsto hz
    convert h using 1
    · funext n
      simp only [Function.comp_apply, Finset.sum_range_succ, Finset.sum_range_zero,
        pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, zero_add, pow_one,
        Nat.factorial_succ, Nat.cast_mul]
      ring
    · rfl
  have hzero := (hrem.mul_isBigO (Asymptotics.isBigO_refl a atTop)).tendsto_zero_of_tendsto
    (by simpa only [mul_comm] using hquad)
  have h := hzero.add (hquad.div_const 2)
  convert h using 1
  · funext n
    ring
  · simp

theorem poisson_normalized_quadratic (rate : ℝ≥0) (hr : 0 < rate) (t : ℝ) :
    (rate : ℂ) * ((((t / Real.sqrt rate : ℝ) : ℂ) * Complex.I)^2) = -(t : ℂ)^2 := by
  have hs : Real.sqrt (rate : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hr)
  have hs2 : (Real.sqrt (rate : ℝ) : ℂ)^2 = (rate : ℂ) := by
    exact_mod_cast Real.sq_sqrt rate.coe_nonneg
  push_cast
  rw [mul_pow, Complex.I_sq, div_pow, ← hs2]
  field_simp [Complex.ofReal_ne_zero.mpr hs]

theorem centered_scaled_poisson_charFun_tendsto (rates : ℕ → ℝ≥0)
    (hrates : Tendsto (fun n => (rates n : ℝ)) atTop atTop) (t : ℝ) :
    Tendsto (fun n => charFun (centeredScaledPoissonLaw (rates n) (Real.sqrt (rates n)) : Measure ℝ) t)
      atTop (𝓝 (Complex.exp (-(t : ℂ)^2 / 2))) := by
  simp_rw [charFun_centeredScaledPoissonLaw]
  apply Complex.continuous_exp.continuousAt.tendsto.comp
  apply poisson_exponent_tendsto
  · have hs := Real.tendsto_sqrt_atTop.comp hrates
    have ht : Tendsto (fun n => t / Real.sqrt (rates n)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hs
    simpa using (Complex.continuous_ofReal.continuousAt.tendsto.comp ht).mul_const Complex.I
  · apply tendsto_const_nhds.congr'
    filter_upwards [hrates.eventually_gt_atTop 0] with n hn
    exact (poisson_normalized_quadratic (rates n) hn t).symm

/-- The quadratic term when the variance is normalized by an independent scale. -/
theorem poisson_scaled_quadratic (rate : ℝ≥0) (base : ℝ) (hb : 0 < base) (t : ℝ) :
    (rate : ℂ) * ((((t / Real.sqrt base : ℝ) : ℂ) * Complex.I)^2) =
      -((rate : ℝ) / base : ℝ) * (t : ℂ)^2 := by
  have hs : Real.sqrt base ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hb)
  have hs2 : (Real.sqrt base : ℂ)^2 = (base : ℂ) := by
    exact_mod_cast Real.sq_sqrt hb.le
  push_cast
  rw [mul_pow, Complex.I_sq, div_pow, ← hs2]
  field_simp [Complex.ofReal_ne_zero.mpr hs]

def centeredGaussianLaw (variance : ℝ≥0) : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 variance, inferInstance⟩

/-- A genuine triangular Poisson CLT, including zero limiting variance. -/
theorem centeredPoisson_tendsto_of_rate_ratio (rates : ℕ → ℝ≥0) (base : ℕ → ℝ)
    (variance : ℝ≥0) (hbase : Tendsto base atTop atTop)
    (hratio : Tendsto (fun n => (rates n : ℝ) / base n) atTop (𝓝 (variance : ℝ))) :
    Tendsto (fun n => centeredScaledPoissonLaw (rates n) (Real.sqrt (base n))) atTop
      (𝓝 (centeredGaussianLaw variance)) := by
  apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr
  intro t
  simp only [charFun_centeredScaledPoissonLaw]
  change Tendsto _ atTop (𝓝 (charFun (gaussianReal 0 variance) t))
  simp only [charFun_gaussianReal, Complex.ofReal_zero]
  have hexp := poisson_exponent_tendsto
    (fun n => (rates n : ℂ))
    (fun n => ((t / Real.sqrt (base n) : ℝ) : ℂ) * Complex.I)
    (-(variance : ℂ) * (t : ℂ)^2)
    (by
      have ht : Tendsto (fun n => t / Real.sqrt (base n)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hbase)
      simpa using (Complex.continuous_ofReal.continuousAt.tendsto.comp ht).mul_const Complex.I)
    (by
      have h := ((Complex.continuous_ofReal.continuousAt.tendsto.comp hratio).neg).mul_const
        ((t : ℂ)^2)
      apply h.congr'
      filter_upwards [hbase.eventually_gt_atTop 0] with n hn
      exact (poisson_scaled_quadratic (rates n) (base n) hn t).symm)
  simpa only [Function.comp_def, mul_zero, zero_mul, zero_sub, neg_mul, neg_div] using
    Complex.continuous_exp.continuousAt.tendsto.comp hexp

/-- The actual Poisson law, regarded as a probability law on the real line. -/
def realPoissonLaw (rate : ℝ≥0) : ProbabilityMeasure ℝ :=
  ⟨(poissonMeasure rate).map (fun n : ℕ => (n : ℝ)),
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable⟩

theorem realPoissonLaw_tendsto (rates : ℕ → ℝ≥0) (rate : ℝ≥0)
    (hrates : Tendsto (fun n => (rates n : ℝ)) atTop (𝓝 (rate : ℝ))) :
    Tendsto (fun n => realPoissonLaw (rates n)) atTop (𝓝 (realPoissonLaw rate)) := by
  apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr
  intro t
  change Tendsto (fun n => charFun ((poissonMeasure (rates n)).map (fun k : ℕ => (k : ℝ))) t)
    atTop (𝓝 (charFun ((poissonMeasure rate).map (fun k : ℕ => (k : ℝ))) t))
  simp only [charFun_map_cast_poissonMeasure]
  exact Complex.continuous_exp.continuousAt.tendsto.comp
    ((Complex.continuous_ofReal.continuousAt.tendsto.comp hrates).mul_const _)

def standardGaussianLaw : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩

/-- The ordinary weak Poisson CLT, along any diverging sequence of real intensities. -/
theorem normalizedPoisson_tendsto (rates : ℕ → ℝ≥0)
    (hrates : Tendsto (fun n => (rates n : ℝ)) atTop atTop) :
    Tendsto (fun n => centeredScaledPoissonLaw (rates n) (Real.sqrt (rates n))) atTop
      (𝓝 standardGaussianLaw) := by
  apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr
  intro t
  simpa [standardGaussianLaw, charFun_gaussianReal, neg_div] using
    centered_scaled_poisson_charFun_tendsto rates hrates t

end
end PaperC.V282.PoissonCLT
