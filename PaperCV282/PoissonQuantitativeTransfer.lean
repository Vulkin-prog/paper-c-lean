import PaperCV282.PoissonQuantitativeBerry
import PaperCV282.SharpConditioningDiscrete

/-! # Quantitative normal approximation of genuine conditioned observations -/
namespace PaperC.V282.PoissonQuantitativeTransfer

open MeasureTheory ProbabilityTheory Real Set SharpConditioning ConditionedCountableLaw
open PoissonQuantitativeBerry
open scoped NNReal

noncomputable section

theorem law_CDF_error_le (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (rate : ℝ≥0) (hr : 0<rate) (t : ℝ) :
    |μ.real {n : ℕ | ((n : ℝ)-(rate : ℝ))/sqrt rate≤t}-(gaussianReal 0 1).real (Iic t)|≤
      measureTotalVariation μ (poissonMeasure rate)+berryConstant/sqrt rate := by
  exact (abs_sub_le _ ((poissonMeasure rate).real {n : ℕ | ((n : ℝ)-(rate : ℝ))/sqrt rate≤t}) _).trans
    (add_le_add (discrepancy_le μ (poissonMeasure rate) _ ((Set.to_countable _).measurableSet))
      (poisson_gaussian_CDF_error rate hr t))

/-- The source probability is the exact normalized restriction to a positive event. -/
theorem conditional_observation_CDF_error {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : Set Ω) (hE : MeasurableSet E)
    (hpos : 0<μ.real E) {X : Ω→ℕ} (hX : Measurable X)
    (rate : ℝ≥0) (hr : 0<rate) (t : ℝ) :
    |μ.real (E∩{ω | ((X ω : ℝ)-(rate : ℝ))/sqrt rate≤t})/μ.real E-
      (gaussianReal 0 1).real (Iic t)|≤
      measureTotalVariation ((cond μ E).map X) (poissonMeasure rate)+berryConstant/sqrt rate := by
  letI instConditionedProbability : IsProbabilityMeasure (cond μ E) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos μ hpos)
  letI instObservedProbability : IsProbabilityMeasure ((cond μ E).map X) :=
    Measure.isProbabilityMeasure_map hX.aemeasurable
  have h := law_CDF_error_le ((cond μ E).map X) rate hr t
  rw [Measure.real,Measure.map_apply hX ((Set.to_countable _).measurableSet)] at h
  change |(cond μ E).real {ω | ((X ω : ℝ)-(rate : ℝ))/sqrt rate≤t}-_|≤_ at h
  rw [cond_real_apply μ E hE] at h
  exact h

/-- Countable total variation has the same normalization, with no factor two. -/
theorem conditional_observation_CDF_mass_error {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : Set Ω) (hE : MeasurableSet E)
    (hpos : 0<μ.real E) {X : Ω→ℕ} (hX : Measurable X)
    (rate : ℝ≥0) (hr : 0<rate) (t : ℝ) :
    |μ.real (E∩{ω | ((X ω : ℝ)-(rate : ℝ))/sqrt rate≤t})/μ.real E-
      (gaussianReal 0 1).real (Iic t)|≤
      FiniteFieldTotalVariation.massTotalVariation
        (conditionalObservableLaw μ E X) (ScalarSteinInput.poissonMass rate)+berryConstant/sqrt rate := by
  letI instConditionedProbability : IsProbabilityMeasure (cond μ E) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos μ hpos)
  letI instObservedProbability : IsProbabilityMeasure ((cond μ E).map X) :=
    Measure.isProbabilityMeasure_map hX.aemeasurable
  have h := conditional_observation_CDF_error μ E hE hpos hX rate hr t
  rw [SharpConditioningDiscrete.measureTotalVariation_eq_mass] at h
  have he : InfiniteMassCoupling.observableLaw ((cond μ E).map X) id=conditionalObservableLaw μ E X := by
    funext n
    change ((cond μ E).map X).real {n}=(cond μ E).real {ω | X ω=n}
    simp only [Measure.real,Measure.map_apply hX (measurableSet_singleton n)]
    rfl
  rw [he] at h
  exact h

end
end PaperC.V282.PoissonQuantitativeTransfer
