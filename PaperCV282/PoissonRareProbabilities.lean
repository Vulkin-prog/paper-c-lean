import PaperCV282.PoissonResolvedTarget

/-! # Relative non-vacancy and singleton probabilities at small Poisson intensity

The deterministic target errors are bounded by the intensity itself. An
arbitrary true count law adds its total variation error divided by that intensity.
-/
namespace PaperC.V282.PoissonRareProbabilities

open MeasureTheory ProbabilityTheory Real SharpConditioning PoissonResolvedTarget
open scoped NNReal

noncomputable section

theorem exp_neg_relative_error_le {r : ℝ} (hr : 0 ≤ r) : |exp (-r) - 1| ≤ r := by
  have hu : exp (-r) ≤ 1 := exp_le_one_iff.mpr (by linarith)
  have hl := add_one_le_exp (-r)
  rw [abs_of_nonpos (by linarith)]
  linarith

theorem nonvacancy_relative_error_le {r : ℝ} (hr : 0 < r) :
    |(1 - exp (-r)) / r - 1| ≤ r := by
  have hl := add_one_le_exp (-r)
  have hp : (1+r)*exp (-r) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right (add_one_le_exp r) (exp_nonneg (-r))
    rw [← exp_add, add_neg_cancel, exp_zero] at h
    simpa only [add_comm] using h
  have hq : exp (-r) ≤ 1-r+r^2 := by
    nlinarith [mul_nonneg hr.le (show 0 ≤ exp (-r) - (1-r) by linarith)]
  have hlo : 1-r ≤ (1-exp (-r))/r := (le_div_iff₀ hr).mpr (by nlinarith)
  have hhi : (1-exp (-r))/r ≤ 1 := (div_le_iff₀ hr).mpr (by linarith)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem poisson_nonvacancy_probability (rate : ℝ≥0) :
    (poissonMeasure rate).real (Set.Ioi 0) = 1-exp (-(rate : ℝ)) := by
  have heq : (Set.Ioi 0 : Set ℕ) = ({0} : Set ℕ)ᶜ := by ext n; simp; omega
  rw [heq, measureReal_compl (measurableSet_singleton _), probReal_univ,
    poissonMeasure_real_singleton]
  simp

theorem poisson_singleton_probability (rate : ℝ≥0) :
    (poissonMeasure rate).real {1} = exp (-(rate : ℝ)) * rate := by
  rw [poissonMeasure_real_singleton]
  simp

/-- Relative event comparison for genuine probability measures. -/
theorem relative_event_error_le (μ ν : Measure ℕ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (A : Set ℕ) {r e : ℝ} (hr : 0 < r)
    (he : |ν.real A / r - 1| ≤ e) :
    |μ.real A / r - 1| ≤ measureTotalVariation μ ν / r + e := by
  have hd : |μ.real A/r - ν.real A/r| ≤ measureTotalVariation μ ν / r := by
    rw [← sub_div, abs_div, abs_of_pos hr]
    exact div_le_div_of_nonneg_right (discrepancy_le μ ν A (Set.to_countable A).measurableSet) hr.le
  calc
    _ = |(μ.real A/r - ν.real A/r) + (ν.real A/r - 1)| := by congr 1; ring
    _ ≤ |μ.real A/r - ν.real A/r| + |ν.real A/r - 1| := abs_add_le _ _
    _ ≤ _ := add_le_add hd he

/-- Both rare-event probabilities have relative error at most TV/lambda + lambda. -/
theorem rare_probabilities_relative_bound (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (rate : ℝ≥0) (hr : 0 < rate) :
    |μ.real (Set.Ioi 0)/(rate : ℝ)-1| ≤
        measureTotalVariation μ (poissonMeasure rate)/(rate : ℝ)+(rate : ℝ) ∧
      |μ.real {1}/(rate : ℝ)-1| ≤
        measureTotalVariation μ (poissonMeasure rate)/(rate : ℝ)+(rate : ℝ) := by
  have hr' : 0 < (rate : ℝ) := hr
  constructor
  · apply relative_event_error_le μ (poissonMeasure rate) (Set.Ioi 0) hr'
    rw [poisson_nonvacancy_probability]
    exact nonvacancy_relative_error_le hr'
  · apply relative_event_error_le μ (poissonMeasure rate) {1} hr'
    rw [poisson_singleton_probability, mul_div_cancel_right₀ _ hr'.ne']
    exact exp_neg_relative_error_le hr'.le

end
end PaperC.V282.PoissonRareProbabilities
