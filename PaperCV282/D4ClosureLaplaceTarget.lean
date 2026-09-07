import PaperCV282.D4ClosureLaplaceRows
import PaperCV282.D4ClosureLaplaceFunctional
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # The complete locally finite target has the printed Laplace functional -/
namespace PaperC.V282.D4ClosureLaplaceTarget

open MeasureTheory ProbabilityTheory Real D4ClosurePointMeasure D4ClosureLaplaceRows
open D4ClosureLaplaceFunctional D4ClosureIntegerLevels UniformSpatialGrid
open scoped BigOperators

noncomputable section

theorem uniform_position_integral (f : ℝ → ℝ) :
    (∫ u : unitInterval, f (1+(u : ℝ)) ∂unitIntervalUniformMeasure) =
      ∫ t in Set.Ico (1 : ℝ) 2, f t := by
  rw [unitIntervalUniformMeasure]
  change (∫ u : Set.Icc (0 : ℝ) 1, f (1+(u : ℝ)) ∂Measure.comap Subtype.val volume) = _
  rw [integral_subtype_comap measurableSet_Icc (fun u : ℝ => f (1+u)),
    integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1),
    intervalIntegral.integral_comp_add_left]
  norm_num only [add_zero]
  rw [intervalIntegral.integral_of_le (by norm_num : (1 : ℝ)≤2),integral_Ico_eq_integral_Ioc]

theorem integral_integerPointRow (sample : IntegerSpatialSample) (r : ℤ) (g : ℝ × ℤ → ℝ) :
    (∫ z, g z ∂integerPointRow sample r) =
      ∑ i ∈ Finset.range ((sample r).1), g (1+((sample r).2 i : ℝ),r) := by
  unfold integerPointRow
  rw [integral_finsetSum_measure (fun i hi => integrable_dirac (by simp))]
  simp only [integral_dirac]

theorem integral_integerPointMeasure_finite_levels (sample : IntegerSpatialSample)
    (g : ℝ × ℤ → ℝ) (s : Finset ℤ) (hs : ∀ t r, r ∉ s → g (t,r) = 0) :
    (∫ z, g z ∂integerPointMeasure sample) =
      ∑ r ∈ s, ∑ i ∈ Finset.range ((sample r).1), g (1+((sample r).2 i : ℝ),r) := by
  have hi (r : ℤ) : Integrable g (integerPointRow sample r) :=
    integrable_finsetSum_measure.mpr (fun i hi => integrable_dirac (by simp))
  have hnorm : Summable (fun r => ∫ z, ‖g z‖ ∂integerPointRow sample r) := by
    apply summable_of_ne_finset_zero (s := s)
    intro r hr
    rw [integral_integerPointRow]
    simp [hs _ r hr]
  have hint := integrable_sum_measure hi hnorm
  change (∫ z, g z ∂Measure.sum (integerPointRow sample)) = _
  rw [← (hasSum_integral_measure hint).tsum_eq]
  rw [tsum_eq_sum (s := s) (fun r hr => by
    rw [integral_integerPointRow]
    simp [hs _ r hr])]
  simp_rw [integral_integerPointRow]

/-- The formula comes from the joint independent row samples and literal Dirac sums. -/
theorem integer_target_laplace (theta : ℝ) (g : ℝ × ℤ → ℝ)
    (hg : Continuous g) (hg0 : ∀ z, 0 ≤ g z) (hgc : HasCompactSupport g) :
    (∫ sample : IntegerSpatialSample, exp (-(∫ z, g z ∂integerPointMeasure sample))
      ∂integerSpatialSampleMeasure theta) = laplaceFunctional theta g := by
  obtain ⟨d,E,hlo,hhi⟩ := compact_support_level_band g hgc
  let s := levelWindow d E
  have hs : ∀ t r, r ∉ s → g (t,r) = 0 := by
    intro t r hr
    change r ∉ levelWindow d E at hr
    rw [mem_levelWindow] at hr
    by_cases h : r < -(d : ℤ)
    · exact hlo t r h
    · exact hhi t r (by omega)
  simp_rw [integral_integerPointMeasure_finite_levels _ g s hs]
  rw [finite_rows_laplace theta s g hg.measurable hg0]
  have hup (r : ℤ) := uniform_position_integral (fun t => 1-exp (-g (t,r)))
  simp_rw [hup]
  unfold laplaceFunctional
  simp_rw [level_integrand_eq_sum theta g s hs]
  have hi (r : ℤ) : IntegrableOn (fun t => 1-exp (-g (t,r))) (Set.Ico (1 : ℝ) 2) := by
    apply (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ico_subset_Icc_self
    exact (continuous_const.sub (Real.continuous_exp.comp
      (hg.comp (continuous_id.prodMk continuous_const)).neg)).continuousOn
  rw [integral_finsetSum s (fun r hr => (hi r).const_mul _)]
  simp_rw [integral_const_mul]

end
end PaperC.V282.D4ClosureLaplaceTarget
