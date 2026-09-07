import PaperCV282.KernelTotalVariation
import Mathlib.Probability.Kernel.Composition.Lemmas

/-! # Total variation of genuine kernel products

The bound integrates the actual pointwise TV of two Markov kernels over the
same marginal. Mapping the first coordinate permits arbitrary recorded spaces.
-/
namespace PaperC.V282.KernelProductVariation

open MeasureTheory ProbabilityTheory Set Filter
open SharpConditioning KernelTotalVariation
open scoped ENNReal

noncomputable section

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

theorem compProd_real_apply (μ : Measure α) [IsFiniteMeasure μ]
    (κ : Kernel α β) [IsMarkovKernel κ] {s : Set (α × β)} (hs : MeasurableSet s) :
    (μ ⊗ₘ κ).real s = ∫ a, (κ a).real (Prod.mk a ⁻¹' s) ∂μ := by
  rw [Measure.real, Measure.compProd_apply hs]
  exact (integral_toReal (Kernel.measurable_kernel_prodMk_left hs).aemeasurable
    (Eventually.of_forall fun a => measure_lt_top (κ a) _)).symm

theorem integrable_kernel_section (μ : Measure α) [IsFiniteMeasure μ]
    (κ : Kernel α β) [IsMarkovKernel κ] {s : Set (α × β)} (hs : MeasurableSet s) :
    Integrable (fun a => (κ a).real (Prod.mk a ⁻¹' s)) μ := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    (Kernel.measurable_kernel_prodMk_left hs).ennreal_toReal.aestronglyMeasurable
  exact Eventually.of_forall fun a => by
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact (measureReal_mono (Set.subset_univ _)).trans_eq probReal_univ

/-- The section argument controls the true product measures, without restricting recorded types. -/
theorem measureTotalVariation_compProd_le [MeasurableSpace.CountablyGenerated β]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η] :
    measureTotalVariation (μ ⊗ₘ κ) (μ ⊗ₘ η) ≤
      ∫ a, measureTotalVariation (κ a) (η a) ∂μ := by
  apply (measureTotalVariation_le_iff _ _ _).mpr
  intro s hs
  have hκ := integrable_kernel_section μ κ hs
  have hη := integrable_kernel_section μ η hs
  rw [compProd_real_apply μ κ hs, compProd_real_apply μ η hs, ← integral_sub hκ hη]
  calc
    _ ≤ ∫ a, |(κ a).real (Prod.mk a ⁻¹' s) - (η a).real (Prod.mk a ⁻¹' s)| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun a => (κ a).real (Prod.mk a ⁻¹' s) - (η a).real (Prod.mk a ⁻¹' s))
    _ ≤ _ := integral_mono (by simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hκ.sub hη).norm)
      (integrable_kernel_totalVariation μ κ η)
      (fun a => discrepancy_le (κ a) (η a) (Prod.mk a ⁻¹' s)
        (measurable_prodMk_left hs))

theorem measureTotalVariation_recorded_kernel_le [MeasurableSpace.CountablyGenerated β]
    (μ : Measure α) [IsProbabilityMeasure μ] (κ : Kernel α β) [IsMarkovKernel κ]
    (ν : Measure β) [IsProbabilityMeasure ν] (V : α → γ) (hV : Measurable V) :
    measureTotalVariation ((μ ⊗ₘ κ).map (Prod.map V id)) ((μ.map V).prod ν) ≤
      ∫ a, measureTotalVariation (κ a) ν ∂μ := by
  have h := measureTotalVariation_map_le (μ ⊗ₘ κ) (μ ⊗ₘ Kernel.const α ν)
    (hV.prodMap measurable_id)
  rw [Measure.compProd_const, ← Measure.map_prod_map μ ν hV measurable_id, Measure.map_id] at h
  exact h.trans (by simpa only [Measure.compProd_const, Kernel.const_apply] using
    measureTotalVariation_compProd_le μ κ (Kernel.const α ν))

/-- Restricting the conditioning marginal pays only its one inverse event probability. -/
theorem integral_cond_kernel_totalVariation_le [MeasurableSpace.CountablyGenerated β]
    (μ : Measure α) [IsProbabilityMeasure μ] (κ η : Kernel α β)
    [IsMarkovKernel κ] [IsMarkovKernel η] (C : Set α) :
    (∫ a, measureTotalVariation (κ a) (η a) ∂cond μ C) ≤
      (∫ a, measureTotalVariation (κ a) (η a) ∂μ) / μ.real C := by
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv]
  have h := setIntegral_le_integral (s := C) (integrable_kernel_totalVariation μ κ η)
    (Eventually.of_forall fun a => measureTotalVariation_nonneg (κ a) (η a))
  simpa only [Measure.real, smul_eq_mul, div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_left h (show 0 ≤ ((μ C).toReal)⁻¹ from
      inv_nonneg.mpr ENNReal.toReal_nonneg)

theorem compProd_restrict_base (μ : Measure α) [IsFiniteMeasure μ]
    (κ : Kernel α β) [IsMarkovKernel κ] (C : Set α) (hC : MeasurableSet C) :
    (μ.restrict C) ⊗ₘ κ = (μ ⊗ₘ κ).restrict (C ×ˢ univ) := by
  ext s hs
  rw [Measure.compProd_apply hs, Measure.restrict_apply hs,
    Measure.compProd_apply (hs.inter (hC.prod MeasurableSet.univ)), ← lintegral_indicator hC]
  apply lintegral_congr
  intro a
  by_cases ha : a ∈ C
  · rw [Set.indicator_of_mem ha]
    congr 1
    ext b
    simp [ha]
  · rw [Set.indicator_of_notMem ha]
    have he : Prod.mk a ⁻¹' (s ∩ C ×ˢ univ) = ∅ := by ext b; simp [ha]
    rw [he, measure_empty]

theorem compProd_cond_base (μ : Measure α) [IsProbabilityMeasure μ]
    (κ : Kernel α β) [IsMarkovKernel κ] (C : Set α) (hC : MeasurableSet C) :
    (cond μ C) ⊗ₘ κ = cond (μ ⊗ₘ κ) (C ×ˢ univ) := by
  have hmass : (μ ⊗ₘ κ) (C ×ˢ univ) = μ C := by
    simp [Measure.compProd_apply_prod hC MeasurableSet.univ]
  rw [ProbabilityTheory.cond, Measure.compProd_smul_left, compProd_restrict_base μ κ C hC,
    ProbabilityTheory.cond, hmass]

theorem map_cond_preimage (μ : Measure α) (f : α → γ) (hf : Measurable f)
    (C : Set γ) (hC : MeasurableSet C) :
    (cond μ (f ⁻¹' C)).map f = cond (μ.map f) C := by
  ext s hs
  rw [Measure.map_apply hf hs, cond_apply (hf hC), cond_apply hC,
    Measure.map_apply hf hC, Measure.map_apply hf (hC.inter hs)]
  rfl

end
end PaperC.V282.KernelProductVariation
