import PaperCV282.D4ClosurePointLaws
import PaperCV282.CompoundPoissonTarget

/-! # Laplace transforms of the genuine independent spatial Poisson rows -/
namespace PaperC.V282.D4ClosureLaplaceRows

open MeasureTheory ProbabilityTheory Real GeneralPoissonMarking CompoundPoissonTarget
open D4ClosurePointMeasure D4ClosurePointLaws D4ClosureIntegerLevels UniformSpatialGrid
open scoped BigOperators NNReal

noncomputable section

theorem integral_real_mark_product {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu] (f : X → ℝ) (hf : Measurable f) (n : ℕ) :
    (∫ marks, ∏ i ∈ Finset.range n, f (marks i) ∂markSequenceMeasure mu) = (∫ x, f x ∂mu)^n := by
  have hdep : iIndepFun (fun i : ℕ => fun marks : ℕ → X => f (marks i)) (markSequenceMeasure mu) :=
    iIndepFun_infinitePi (fun _ => hf)
  have hn := hdep.precomp (fun i j (h : (i : ℕ) = (j : ℕ)) => Fin.ext h)
    (g := fun i : Fin n => i.val)
  have hp := hn.integral_fun_prod_eq_prod_integral
    (fun i => (hf.comp (measurable_pi_apply i.val)).aestronglyMeasurable)
  have hcoord (i : Fin n) :
      (∫ marks : ℕ → X, f (marks i.val) ∂markSequenceMeasure mu) = ∫ x, f x ∂mu :=
    (hasLaw_mark_coordinate mu i.val).integral_comp hf.aestronglyMeasurable
  simp_rw [hcoord] at hp
  calc
    _ = ∫ marks : ℕ → X, ∏ i : Fin n, f (marks i.val) ∂markSequenceMeasure mu := by
      congr 1
      funext marks
      exact (Fin.prod_univ_eq_prod_range (fun i => f (marks i)) n).symm
    _ = _ := by simpa using hp

theorem measurable_real_stopped_product {X : Type*} [MeasurableSpace X]
    (f : X → ℝ) (hf : Measurable f) :
    Measurable (fun sample : ℕ × (ℕ → X) => ∏ i ∈ Finset.range sample.1, f (sample.2 i)) := by
  apply measurable_from_prod_countable_right
  intro n
  change Measurable (fun marks : ℕ → X => ∏ i ∈ Finset.range n, f (marks i))
  exact Finset.measurable_prod _ (fun i _ => hf.comp (measurable_pi_apply i))

theorem real_stopped_product_transform {X : Type*} [MeasurableSpace X]
    (rate : ℝ≥0) (mu : Measure X) [IsProbabilityMeasure mu]
    (f : X → ℝ) (hf : Measurable f) (hb : ∀ x, |f x| ≤ 1) :
    (∫ sample, ∏ i ∈ Finset.range sample.1, f (sample.2 i) ∂markSampleMeasure rate mu) =
      exp ((rate : ℝ)*((∫ x, f x ∂mu)-1)) := by
  have hint : Integrable (fun sample : ℕ × (ℕ → X) => ∏ i ∈ Finset.range sample.1, f (sample.2 i))
      (markSampleMeasure rate mu) := by
    refine ⟨(measurable_real_stopped_product f hf).aestronglyMeasurable,?_⟩
    apply HasFiniteIntegral.of_bounded (C := 1)
    exact Filter.Eventually.of_forall fun sample => by
      rw [norm_prod]
      exact Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => by simpa using hb (sample.2 i))
  rw [markSampleMeasure,integral_prod _ hint]
  simp_rw [integral_real_mark_product mu f hf]
  exact integral_poisson_powers rate _

def rowLaplace (r : ℤ) (g : ℝ × ℤ → ℝ) (sample : ℕ × (ℕ → unitInterval)) : ℝ :=
  exp (-(∑ i ∈ Finset.range sample.1, g (1+(sample.2 i : ℝ),r)))

theorem rowLaplace_eq_product (r : ℤ) (g : ℝ × ℤ → ℝ) (sample : ℕ × (ℕ → unitInterval)) :
    rowLaplace r g sample = ∏ i ∈ Finset.range sample.1, exp (-g (1+(sample.2 i : ℝ),r)) := by
  rw [rowLaplace,← Finset.sum_neg_distrib,exp_sum]

theorem measurable_rowLaplace (r : ℤ) (g : ℝ × ℤ → ℝ) (hg : Measurable g) :
    Measurable (rowLaplace r g) := by
  have h := measurable_real_stopped_product
    (fun u : unitInterval => exp (-g (1+(u : ℝ),r))) (by fun_prop)
  simpa only [← rowLaplace_eq_product] using h

theorem row_laplace_transform (rate : ℝ≥0) (r : ℤ) (g : ℝ × ℤ → ℝ)
    (hg : Measurable g) (hg0 : ∀ z, 0 ≤ g z) :
    (∫ sample, rowLaplace r g sample ∂markSampleMeasure rate unitIntervalUniformMeasure) =
      exp (-(rate : ℝ)*(∫ u : unitInterval, 1-exp (-g (1+(u : ℝ),r)) ∂unitIntervalUniformMeasure)) := by
  simp_rw [rowLaplace_eq_product]
  have hb (u : unitInterval) : |exp (-g (1+(u : ℝ),r))| ≤ 1 := by
    rw [abs_of_pos (exp_pos _)]
    exact exp_le_one_iff.mpr (neg_nonpos.mpr (hg0 _))
  rw [real_stopped_product_transform rate unitIntervalUniformMeasure _ (by fun_prop) hb]
  have hi : Integrable (fun u : unitInterval => exp (-g (1+(u : ℝ),r))) unitIntervalUniformMeasure :=
    (integrable_const (1 : ℝ)).mono'
      ((show Measurable (fun u : unitInterval => exp (-g (1+(u : ℝ),r))) from by fun_prop).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun u => by simpa only [Real.norm_eq_abs] using hb u)
  rw [integral_sub (integrable_const 1) hi,integral_const]
  simp only [probReal_univ,smul_eq_mul,one_mul]
  congr 1
  ring

/-- The entire joint row law, rather than marginal Poisson counts alone, gives the product. -/
theorem finite_rows_laplace (theta : ℝ) (s : Finset ℤ) (g : ℝ × ℤ → ℝ)
    (hg : Measurable g) (hg0 : ∀ z, 0 ≤ g z) :
    (∫ sample : IntegerSpatialSample,
      exp (-(∑ r ∈ s, ∑ i ∈ Finset.range ((sample r).1),
        g (1+((sample r).2 i : ℝ),r))) ∂integerSpatialSampleMeasure theta) =
      exp (-(∑ r ∈ s, (integerLevelRate theta r : ℝ)*
        ∫ u : unitInterval, 1-exp (-g (1+(u : ℝ),r)) ∂unitIntervalUniformMeasure)) := by
  classical
  have hind := (independent_spatialLevelSamples theta).precomp
    (fun i j (h : (i : ℤ) = (j : ℤ)) => Subtype.ext h) (g := fun r : s => r.val)
  have hdep := hind.comp (fun r : s => rowLaplace r.val g) (fun r => measurable_rowLaplace _ g hg)
  have hp := hdep.integral_fun_prod_eq_prod_integral
    (fun r => ((measurable_rowLaplace r.val g hg).comp (measurable_pi_apply r.val)).aestronglyMeasurable)
  have hc (r : s) :
      (∫ sample : IntegerSpatialSample, rowLaplace r.val g (sample r.val) ∂integerSpatialSampleMeasure theta) =
        exp (-(integerLevelRate theta r.val : ℝ)*
          ∫ u : unitInterval, 1-exp (-g (1+(u : ℝ),r.val)) ∂unitIntervalUniformMeasure) :=
    ((hasLaw_spatialLevelSample theta r.val).integral_comp
      (measurable_rowLaplace r.val g hg).aestronglyMeasurable).trans
        (row_laplace_transform _ r.val g hg hg0)
  simp only [Function.comp_def] at hp
  simp_rw [hc] at hp
  rw [← exp_sum] at hp
  have he (sample : IntegerSpatialSample) :
      exp (-(∑ r ∈ s, ∑ i ∈ Finset.range ((sample r).1), g (1+((sample r).2 i : ℝ),r))) =
        ∏ r : s, rowLaplace r.val g (sample r.val) := by
    rw [← Finset.sum_coe_sort s,← Finset.sum_neg_distrib,exp_sum]
    rfl
  simp_rw [he]
  rw [hp]
  congr 1
  rw [← Finset.sum_coe_sort s,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  ring

end
end PaperC.V282.D4ClosureLaplaceRows
