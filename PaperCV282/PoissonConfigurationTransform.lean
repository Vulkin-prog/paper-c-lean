import PaperCV282.PoissonThresholdTarget
import PaperCV282.GeneralPoissonMarking

/-! # Characteristic transforms of the genuine geometric configuration -/
namespace PaperC.V282.PoissonConfigurationTransform

open MeasureTheory ProbabilityTheory GeometricMarkedConfiguration GeometricClusterTarget
open CompoundPoissonTarget GeneralPoissonMarking
open scoped NNReal

noncomputable section

def configurationLinear (g : ℕ → ℝ) (c : ℕ →₀ ℕ) : ℝ :=
  c.sum (fun e n => (n : ℝ) * g e)

def positiveMarkLinear (g : ℕ → ℝ) (h : ℕ) : ℝ :=
  if 0 < h then g (h-1) else 0

theorem configurationLinear_cluster (g : ℕ → ℝ) (sample : ℕ × (ℕ → ℕ)) :
    configurationLinear g (clusterConfiguration sample) =
      ∑ i ∈ Finset.range sample.1, positiveMarkLinear g (sample.2 i) := by
  classical
  unfold configurationLinear clusterConfiguration
  rw [← Finsupp.sum_finsetSum_index]
  · apply Finset.sum_congr rfl
    intro i hi
    by_cases hp : 0 < sample.2 i
    · simp [hp, positiveMarkLinear, Finsupp.sum_single_index]
    · simp [hp, positiveMarkLinear]
  · intro e
    simp
  · intro e n m
    push_cast
    ring

theorem configurationLinear_add (g h : ℕ → ℝ) (c : ℕ →₀ ℕ) :
    configurationLinear (fun e => g e + h e) c =
      configurationLinear g c + configurationLinear h c := by
  simp only [configurationLinear, mul_add]
  exact Finset.sum_add_distrib

theorem configurationLinear_sum {I : Type*} [Fintype I] (g : I → ℕ → ℝ) (c : ℕ →₀ ℕ) :
    configurationLinear (fun e => ∑ i, g i e) c = ∑ i, configurationLinear (g i) c := by
  simp only [configurationLinear, Finset.mul_sum]
  exact Finset.sum_comm

theorem configurationLinear_single (e : ℕ) (a : ℝ) (c : ℕ →₀ ℕ) :
    configurationLinear (fun k => if k=e then a else 0) c = (c e : ℝ) * a := by
  classical
  unfold configurationLinear Finsupp.sum
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq']
  by_cases he : e ∈ c.support
  · simp [he]
  · simp [he, Finsupp.notMem_support_iff.mp he]

theorem configurationLinear_threshold (j : ℕ) (a : ℝ) (c : ℕ →₀ ℕ) :
    configurationLinear (fun e => if j ≤ e then a else 0) c =
      (ThresholdPathEquivalence.tailCount c j : ℝ) * a := by
  unfold configurationLinear Finsupp.sum ThresholdPathEquivalence.tailCount
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e he
  split_ifs <;> simp

/-- Exact compound characteristic transform on the actual finitely supported configuration. -/
theorem configuration_complex_transform (rate : ℝ≥0) (g : ℕ → ℝ) :
    (∫ c, Complex.exp ((configurationLinear g c : ℝ) * Complex.I)
      ∂configurationMeasure rate) =
    Complex.exp ((rate : ℂ) * ((∫ h, Complex.exp ((positiveMarkLinear g h : ℝ) * Complex.I)
      ∂geometricClusterMeasure) - 1)) := by
  rw [configurationMeasure, integral_map measurable_clusterConfiguration.aemeasurable
    (measurable_of_countable _).aestronglyMeasurable]
  simp only [configurationLinear_cluster, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
  exact stopped_mark_product_transform rate geometricClusterMeasure
    (fun h => Complex.exp ((positiveMarkLinear g h : ℝ) * Complex.I))
    (measurable_of_countable _) (fun h => by simp)

theorem centered_configuration_complex_transform (rate : ℝ≥0) (g : ℕ → ℝ) (center : ℝ) :
    (∫ c, Complex.exp (((configurationLinear g c - center : ℝ) : ℂ) * Complex.I)
      ∂configurationMeasure rate) =
    Complex.exp ((rate : ℂ) * ((∫ h, Complex.exp ((positiveMarkLinear g h : ℝ) * Complex.I)
      ∂geometricClusterMeasure) - 1) - (center : ℂ) * Complex.I) := by
  simp_rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub]
  rw [integral_div, configuration_complex_transform, ← Complex.exp_sub]

end
end PaperC.V282.PoissonConfigurationTransform
