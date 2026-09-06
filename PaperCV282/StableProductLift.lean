import PaperCV282.StableConditionalKernel

/-! # Lemma 6.1: stable product lift on a standard Borel observed space

The error is the actual expected total variation of a regular conditional law.
Both the original probability space and the F-measurable recorded space are
arbitrary. Conditioning on a positive F-event incurs one inverse probability.
-/
namespace PaperC.V282.StableProductLift

open MeasureTheory ProbabilityTheory Set Filter
open SharpConditioning KernelTotalVariation KernelProductVariation StableConditionalKernel

noncomputable section

variable {Ω β γ : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace β] [StandardBorelSpace β] [Nonempty β] [MeasurableSpace γ]

def conditionalTV (μ : @Measure Ω mΩ) [IsFiniteMeasure μ]
    (F : MeasurableSpace Ω) (W : Ω → β) (ν : Measure β) (ω : Ω) : ℝ :=
  measureTotalVariation (conditionalKernel (mΩ := mΩ) μ F W ω) ν

theorem measurable_conditionalTV (μ : @Measure Ω mΩ) [IsFiniteMeasure μ]
    (F : MeasurableSpace Ω) (W : Ω → β) (ν : Measure β) [IsProbabilityMeasure ν] :
    Measurable[F] (conditionalTV (mΩ := mΩ) μ F W ν) := by
  change Measurable[F] (fun ω => measureTotalVariation (conditionalKernel (mΩ := mΩ) μ F W ω) ν)
  simpa only [Kernel.const_apply] using
    measurable_kernel_totalVariation (conditionalKernel (mΩ := mΩ) μ F W) (Kernel.const Ω ν)

theorem conditionalTV_nonneg (μ : @Measure Ω mΩ) [IsFiniteMeasure μ]
    (F : MeasurableSpace Ω) (W : Ω → β) (ν : Measure β) [IsProbabilityMeasure ν] (ω : Ω) :
    0 ≤ conditionalTV (mΩ := mΩ) μ F W ν ω := measureTotalVariation_nonneg _ _

theorem conditionalTV_le_one (μ : @Measure Ω mΩ) [IsFiniteMeasure μ]
    (F : MeasurableSpace Ω) (W : Ω → β) (ν : Measure β) [IsProbabilityMeasure ν] (ω : Ω) :
    conditionalTV (mΩ := mΩ) μ F W ν ω ≤ 1 := measureTotalVariation_le_one _ _

theorem integrable_conditionalTV (μ : @Measure Ω mΩ) [IsFiniteMeasure μ]
    {F : MeasurableSpace Ω} (hF : F ≤ mΩ) (W : Ω → β) (ν : Measure β)
    [IsProbabilityMeasure ν] : Integrable (conditionalTV (mΩ := mΩ) μ F W ν) μ := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    ((measurable_conditionalTV (mΩ := mΩ) μ F W ν).mono hF le_rfl).aestronglyMeasurable
  exact Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (conditionalTV_nonneg (mΩ := mΩ) μ F W ν ω)]
    exact conditionalTV_le_one (mΩ := mΩ) μ F W ν ω

/-- The exact joint-law comparison before any numerical error bound is supplied. -/
theorem stable_product_lift_le_mean (μ : @Measure Ω mΩ) [IsProbabilityMeasure μ]
    {F : MeasurableSpace Ω} (hF : F ≤ mΩ) (W : Ω → β) (hW : Measurable[mΩ] W)
    (ν : Measure β) [IsProbabilityMeasure ν] (V : Ω → γ) (hV : Measurable[F] V) :
    measureTotalVariation ((@Measure.map Ω (γ × β) mΩ _ (fun ω => (V ω,W ω)) μ)) (((@Measure.map Ω γ mΩ _ V μ)).prod ν) ≤
      ∫ ω, conditionalTV (mΩ := mΩ) μ F W ν ω ∂μ := by
  have h := measureTotalVariation_recorded_kernel_le (μ.trim hF)
    (conditionalKernel (mΩ := mΩ) μ F W) ν V hV
  rw [recorded_joint_eq_map_compProd (mΩ := mΩ) μ hF W hW V hV,
    map_trim_of_measurable (mΩ := mΩ) μ hF V hV] at h
  change measureTotalVariation ((@Measure.map Ω (γ × β) mΩ _ (fun ω => (V ω,W ω)) μ)) (((@Measure.map Ω γ mΩ _ V μ)).prod ν) ≤
    ∫ ω, conditionalTV (mΩ := mΩ) μ F W ν ω ∂μ.trim hF at h
  rwa [← integral_trim hF (measurable_conditionalTV (mΩ := mΩ) μ F W ν).stronglyMeasurable] at h

/-- Lemma 6.1, with an arbitrary F-measurable recorded random element. -/
theorem lemma_six_one (μ : @Measure Ω mΩ) [IsProbabilityMeasure μ]
    {F : MeasurableSpace Ω} (hF : F ≤ mΩ) (W : Ω → β) (hW : Measurable[mΩ] W)
    (ν : Measure β) [IsProbabilityMeasure ν] (ε : ℝ)
    (hmean : (∫ ω, conditionalTV (mΩ := mΩ) μ F W ν ω ∂μ) ≤ ε)
    (V : Ω → γ) (hV : Measurable[F] V) :
    measureTotalVariation ((@Measure.map Ω (γ × β) mΩ _ (fun ω => (V ω,W ω)) μ)) (((@Measure.map Ω γ mΩ _ V μ)).prod ν) ≤ ε :=
  (stable_product_lift_le_mean (mΩ := mΩ) μ hF W hW ν V hV).trans hmean

theorem conditioned_stable_product_lift_le_mean
    (μ : @Measure Ω mΩ) [IsProbabilityMeasure μ]
    {F : MeasurableSpace Ω} (hF : F ≤ mΩ) (W : Ω → β) (hW : Measurable[mΩ] W)
    (ν : Measure β) [IsProbabilityMeasure ν] (V : Ω → γ) (hV : Measurable[F] V)
    (C : Set Ω) (hC : MeasurableSet[F] C) (hpos : 0 < μ.real C) :
    measureTotalVariation ((@Measure.map Ω (γ × β) mΩ _ (fun ω => (V ω,W ω)) (@cond Ω mΩ μ C)))
      (((@Measure.map Ω γ mΩ _ V (@cond Ω mΩ μ C))).prod ν) ≤
        (∫ ω, conditionalTV (mΩ := mΩ) μ F W ν ω ∂μ) / μ.real C := by
  have hmass : (μ.trim hF).real C = μ.real C := by
    exact congrArg ENNReal.toReal (trim_measurableSet_eq hF hC)
  have hzero : μ.trim hF C ≠ 0 := by
    intro hz
    have hh : (μ.trim hF).real C = 0 := by simp only [Measure.real, hz, ENNReal.toReal_zero]
    linarith
  letI instProbabilityConditionalTrim : IsProbabilityMeasure (cond (μ.trim hF) C) :=
    cond_isProbabilityMeasure hzero
  have h := measureTotalVariation_recorded_kernel_le (cond (μ.trim hF) C)
    (conditionalKernel (mΩ := mΩ) μ F W) ν V hV
  rw [conditioned_joint_eq_map_compProd (mΩ := mΩ) μ hF W hW V hV C hC,
    conditioned_recorded_marginal (mΩ := mΩ) μ hF V hV C hC] at h
  have hi := integral_cond_kernel_totalVariation_le (μ.trim hF)
    (conditionalKernel (mΩ := mΩ) μ F W) (Kernel.const Ω ν) C
  simp only [Kernel.const_apply] at hi
  rw [hmass] at hi
  change (∫ ω, conditionalTV (mΩ := mΩ) μ F W ν ω ∂cond (μ.trim hF) C) ≤
    (∫ ω, conditionalTV (mΩ := mΩ) μ F W ν ω ∂μ.trim hF) / μ.real C at hi
  rw [← integral_trim hF (measurable_conditionalTV (mΩ := mΩ) μ F W ν).stronglyMeasurable] at hi
  exact h.trans hi

omit [StandardBorelSpace β] [Nonempty β] in
theorem observed_distance_le_joint (μ : @Measure Ω mΩ) [IsProbabilityMeasure μ]
    (ν : Measure β) [IsProbabilityMeasure ν] (W : Ω → β) (hW : Measurable W)
    (V : Ω → γ) (hV : Measurable V) :
    measureTotalVariation (μ.map W) ν ≤
      measureTotalVariation ((@Measure.map Ω (γ × β) mΩ _ (fun ω => (V ω,W ω)) μ)) (((@Measure.map Ω γ mΩ _ V μ)).prod ν) := by
  letI instProbabilityRecordedMap : IsProbabilityMeasure ((@Measure.map Ω γ mΩ _ V μ)) :=
    Measure.isProbabilityMeasure_map hV.aemeasurable
  letI instProbabilityJointMap : IsProbabilityMeasure ((@Measure.map Ω (γ × β) mΩ _ (fun ω => (V ω,W ω)) μ)) :=
    Measure.isProbabilityMeasure_map (hV.prodMk hW).aemeasurable
  have h := measureTotalVariation_map_le ((@Measure.map Ω (γ × β) mΩ _ (fun ω => (V ω,W ω)) μ)) (((@Measure.map Ω γ mΩ _ V μ)).prod ν)
    (measurable_snd (α := γ) (β := β))
  rw [Measure.map_map measurable_snd (hV.prodMk hW), Measure.map_snd_prod, measure_univ, one_smul] at h
  exact h

/-- The positive-event conclusion for both the observed law and its stable product lift. -/
theorem lemma_six_one_conditioned (μ : @Measure Ω mΩ) [IsProbabilityMeasure μ]
    {F : MeasurableSpace Ω} (hF : F ≤ mΩ) (W : Ω → β) (hW : Measurable[mΩ] W)
    (ν : Measure β) [IsProbabilityMeasure ν] (ε : ℝ)
    (hmean : (∫ ω, conditionalTV (mΩ := mΩ) μ F W ν ω ∂μ) ≤ ε)
    (V : Ω → γ) (hV : Measurable[F] V)
    (C : Set Ω) (hC : MeasurableSet[F] C) (hpos : 0 < μ.real C) :
    measureTotalVariation ((@Measure.map Ω β mΩ _ W (@cond Ω mΩ μ C))) ν ≤ ε / μ.real C ∧
      measureTotalVariation ((@Measure.map Ω (γ × β) mΩ _ (fun ω => (V ω,W ω)) (@cond Ω mΩ μ C)))
        (((@Measure.map Ω γ mΩ _ V (@cond Ω mΩ μ C))).prod ν) ≤ ε / μ.real C := by
  have hj := (conditioned_stable_product_lift_le_mean (mΩ := mΩ) μ hF W hW ν V hV C hC hpos).trans
    (div_le_div_of_nonneg_right hmean hpos.le)
  have hzero : μ C ≠ 0 := by
    intro hz
    have hh : μ.real C = 0 := by simp only [Measure.real, hz, ENNReal.toReal_zero]
    linarith
  letI instProbabilityConditionalSource : IsProbabilityMeasure (cond μ C) :=
    cond_isProbabilityMeasure hzero
  exact ⟨(observed_distance_le_joint (mΩ := mΩ) (@cond Ω mΩ μ C) ν W hW V
    (hV.mono hF le_rfl)).trans hj,hj⟩

end
end PaperC.V282.StableProductLift
