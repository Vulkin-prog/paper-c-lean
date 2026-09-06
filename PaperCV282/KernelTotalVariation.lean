import PaperCV282.SharpConditioning
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Probability.Kernel.CondDistrib

/-! # Measurability of the actual total variation between probability kernels

A fixed countable generating algebra determines total variation. The algebra
does not depend on either measure; approximation is applied to their sum.
This supplies the genuine integrable conditional-TV random variable on every
countably generated target, in particular every standard Borel target.
-/
namespace PaperC.V282.KernelTotalVariation

open MeasureTheory ProbabilityTheory MeasurableSpace Set symmDiff
open SharpConditioning

noncomputable section

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

def determiningAlgebra (β : Type*) [MeasurableSpace β] [CountablyGenerated β] : Set (Set β) :=
  generateSetAlgebra (countableGeneratingSet β)

theorem determiningAlgebra_countable [CountablyGenerated β] :
    (determiningAlgebra β).Countable :=
  countable_generateSetAlgebra countable_countableGeneratingSet

theorem determiningAlgebra_isSetAlgebra [CountablyGenerated β] :
    IsSetAlgebra (determiningAlgebra β) := isSetAlgebra_generateSetAlgebra

theorem determiningAlgebra_generates [CountablyGenerated β] :
    generateFrom (determiningAlgebra β) = ‹MeasurableSpace β› := by
  rw [determiningAlgebra, generateFrom_generateSetAlgebra_eq, generateFrom_countableGeneratingSet]

theorem measurableSet_of_mem_determiningAlgebra [CountablyGenerated β]
    {s : Set β} (hs : s ∈ determiningAlgebra β) : MeasurableSet s := by
  rw [← determiningAlgebra_generates (β := β)]
  exact measurableSet_generateFrom hs

/-- Bounds on a fixed generating algebra control every measurable test set. -/
theorem discrepancy_le_of_algebra [CountablyGenerated β]
    (μ ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (c : ℝ)
    (h : ∀ t ∈ determiningAlgebra β, |μ.real t - ν.real t| ≤ c)
    (s : Set β) (hs : MeasurableSet s) : |μ.real s - ν.real s| ≤ c := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hd := Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite
    (μ+ν) determiningAlgebra_isSetAlgebra determiningAlgebra_generates.symm
  obtain ⟨t,ht,happrox⟩ := hd.approx s hs (by finiteness) ε hε
  have htm := measurableSet_of_mem_determiningAlgebra ht
  have hreal : (μ+ν).real (s ∆ t) < ε := by
    have hh := (ENNReal.toReal_lt_toReal (by finiteness) ENNReal.ofReal_ne_top).mpr happrox
    simpa only [Measure.real, ENNReal.toReal_ofReal hε.le] using hh
  have hμ := abs_measureReal_sub_le_measureReal_symmDiff
    (μ := μ) hs.nullMeasurableSet htm.nullMeasurableSet
  have hν := abs_measureReal_sub_le_measureReal_symmDiff
    (μ := ν) hs.nullMeasurableSet htm.nullMeasurableSet
  have htri : |μ.real s - ν.real s| ≤
      |μ.real s - μ.real t| + |μ.real t - ν.real t| + |ν.real s - ν.real t| := by
    calc
      _ = |(μ.real s - μ.real t) + (μ.real t - ν.real t) + (ν.real t - ν.real s)| := by congr 1; ring
      _ ≤ |μ.real s - μ.real t| + |μ.real t - ν.real t| + |ν.real t - ν.real s| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = _ := by rw [abs_sub_comm (ν.real t)]
  rw [measureReal_add_apply] at hreal
  linarith [h t ht]

theorem measureTotalVariation_le_iff_algebra [CountablyGenerated β]
    (μ ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (c : ℝ) :
    measureTotalVariation μ ν ≤ c ↔
      ∀ t ∈ determiningAlgebra β, |μ.real t - ν.real t| ≤ c := by
  rw [measureTotalVariation_le_iff]
  exact ⟨fun h t ht => h t (measurableSet_of_mem_determiningAlgebra ht),
    fun h s hs => discrepancy_le_of_algebra μ ν c h s hs⟩

/-- Actual TV of two Markov kernels is measurable, with no countability assumption on the source. -/
theorem measurable_kernel_totalVariation [CountablyGenerated β]
    (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η] :
    Measurable (fun a => measureTotalVariation (κ a) (η a)) := by
  apply measurable_of_Iic
  intro c
  have heq : (fun a => measureTotalVariation (κ a) (η a)) ⁻¹' Iic c =
      ⋂ t ∈ determiningAlgebra β, {a | |(κ a).real t - (η a).real t| ≤ c} := by
    ext a
    simp only [mem_preimage, mem_Iic, mem_iInter, mem_setOf_eq,
      measureTotalVariation_le_iff_algebra]
  rw [heq]
  apply MeasurableSet.biInter determiningAlgebra_countable
  intro t ht
  have htm := measurableSet_of_mem_determiningAlgebra ht
  simpa only [Real.norm_eq_abs, Pi.sub_apply, Measure.real] using measurableSet_le
    (((κ.measurable_coe htm).ennreal_toReal.sub (η.measurable_coe htm).ennreal_toReal).norm)
    (measurable_const (a := c))

theorem integrable_kernel_totalVariation [CountablyGenerated β]
    (μ : Measure α) [IsFiniteMeasure μ]
    (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η] :
    Integrable (fun a => measureTotalVariation (κ a) (η a)) μ := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_kernel_totalVariation κ η).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun a => by
    rw [Real.norm_eq_abs, abs_of_nonneg (measureTotalVariation_nonneg _ _)]
    exact measureTotalVariation_le_one _ _

end
end PaperC.V282.KernelTotalVariation
