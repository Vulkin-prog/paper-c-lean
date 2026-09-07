import PaperCV282.CrossoverSparseWeights
import PaperCV282.CrossoverSourceCoupling
import PaperCV282.SharpConditioningDiscrete

/-! # Probability normalization and triangle bounds used by the rare crossover -/
namespace PaperC.V282.CrossoverConditioningTools

open MeasureTheory ProbabilityTheory SharpConditioning MicroscopicNonvacancy
open ConditionedCountableLaw

noncomputable section

theorem variation_triangle {Alpha : Type*} [MeasurableSpace Alpha]
    (mu nu rho : Measure Alpha) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] [IsProbabilityMeasure rho] :
    measureTotalVariation mu rho ≤ measureTotalVariation mu nu+measureTotalVariation nu rho := by
  apply (measureTotalVariation_le_iff _ _ _).mpr
  intro A hA
  exact (abs_sub_le (mu.real A) (nu.real A) (rho.real A)).trans
    (add_le_add (discrepancy_le mu nu A hA) (discrepancy_le nu rho A hA))

/-- Compare two actual nested rare conditionings after a measurable observation. -/
theorem nested_mapped_difference {Omega Alpha : Type*} [MeasurableSpace Omega] [MeasurableSpace Alpha]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (E H : Set Omega)
    (hE : MeasurableSet E) (hH : MeasurableSet H) (hEH : E ⊆ H) (hp : 0<mu.real E)
    (f : Omega → Alpha) (hf : Measurable f) :
    measureTotalVariation ((cond mu H).map f) ((cond mu E).map f) ≤
      (mu.real H-mu.real E)/mu.real H := by
  letI instProbabilityE : IsProbabilityMeasure (cond mu E) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hp)
  letI instProbabilityH : IsProbabilityMeasure (cond mu H) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ (hp.trans_le (measureReal_mono hEH)))
  have h := nested_conditioning_le mu E H hE hH hEH hp
  rw [measureReal_sdiff hEH hE] at h
  exact (measureTotalVariation_map_le _ _ hf).trans h

end
end PaperC.V282.CrossoverConditioningTools
