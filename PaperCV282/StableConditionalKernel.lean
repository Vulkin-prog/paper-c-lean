import PaperCV282.KernelProductVariation
import Mathlib.Probability.Kernel.CondDistrib

/-! # The regular conditional law over an arbitrary sub-sigma-algebra

Only the observed space is standard Borel. The underlying probability space,
the sub-sigma-algebra and the recorded space are otherwise arbitrary.
-/
namespace PaperC.V282.StableConditionalKernel

open MeasureTheory ProbabilityTheory Set Filter
open KernelProductVariation
open scoped MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω β γ : Type*} [mΩ : MeasurableSpace Ω]
  [mβ : MeasurableSpace β] [StandardBorelSpace β] [Nonempty β]
  [MeasurableSpace γ]

def conditionalKernel (μ : @Measure Ω mΩ) [IsFiniteMeasure μ]
    (F : MeasurableSpace Ω) (W : Ω → β) : @Kernel Ω β F mβ :=
  @condDistrib Ω Ω β mβ _ _ mΩ F W id μ _

instance instMarkovConditionalKernel (μ : @Measure Ω mΩ) [IsFiniteMeasure μ]
    (F : MeasurableSpace Ω) (W : Ω → β) : IsMarkovKernel (conditionalKernel (mΩ := mΩ) μ F W) := by
  unfold conditionalKernel
  infer_instance

instance instProbabilityTrim (μ : @Measure Ω mΩ) [IsProbabilityMeasure μ]
    {F : MeasurableSpace Ω} (hF : F ≤ mΩ) : IsProbabilityMeasure (μ.trim hF) where
  measure_univ := by rw [trim_measurableSet_eq hF MeasurableSet.univ, measure_univ]

theorem conditionalKernel_disintegrate (μ : @Measure Ω mΩ) [IsFiniteMeasure μ]
    {F : MeasurableSpace Ω} (hF : F ≤ mΩ) (W : Ω → β) (hW : Measurable[mΩ] W) :
    (μ.trim hF) ⊗ₘ conditionalKernel (mΩ := mΩ) μ F W =
      @Measure.map Ω (Ω × β) mΩ (F.prod mβ) (fun ω => (ω,W ω)) μ := by
  rw [trim_eq_map hF]
  exact compProd_map_condDistrib (mβ := F) (X := id) (Y := W) hW.aemeasurable

/-- This is the actual conditional distribution, identified with conditional expectations. -/
theorem conditionalKernel_ae_eq_condExp (μ : @Measure Ω mΩ) [IsFiniteMeasure μ]
    {F : MeasurableSpace Ω} (hF : F ≤ mΩ) (W : Ω → β) (hW : Measurable[mΩ] W)
    (s : Set β) (hs : MeasurableSet s) :
    (fun ω => (conditionalKernel (mΩ := mΩ) μ F W ω).real s) =ᵐ[μ] μ⟦W ⁻¹' s | F⟧ := by
  have h := condDistrib_ae_eq_condExp (mβ := F) (μ := μ) (X := id) (Y := W) (s := s)
    (measurable_id'' hF) hW hs
  simpa only [conditionalKernel, MeasurableSpace.comap_id, id_eq] using h

theorem map_trim_of_measurable (μ : @Measure Ω mΩ) {F : MeasurableSpace Ω}
    (hF : F ≤ mΩ) (V : Ω → γ) (hV : Measurable[F] V) :
    (μ.trim hF).map V = @Measure.map Ω γ mΩ _ V μ := by
  ext s hs
  rw [Measure.map_apply hV hs, trim_measurableSet_eq hF (hV hs),
    Measure.map_apply (hV.mono hF le_rfl) hs]

theorem recorded_joint_eq_map_compProd (μ : @Measure Ω mΩ) [IsFiniteMeasure μ]
    {F : MeasurableSpace Ω} (hF : F ≤ mΩ) (W : Ω → β) (hW : Measurable[mΩ] W)
    (V : Ω → γ) (hV : Measurable[F] V) :
    ((μ.trim hF) ⊗ₘ conditionalKernel (mΩ := mΩ) μ F W).map (Prod.map V id) =
      @Measure.map Ω (γ × β) mΩ _ (fun ω => (V ω,W ω)) μ := by
  rw [conditionalKernel_disintegrate (mΩ := mΩ) μ hF W hW]
  have hj : @Measurable Ω (Ω × β) mΩ (F.prod mβ) (fun ω => (ω,W ω)) :=
    (measurable_id'' hF).prodMk hW
  ext s hs
  rw [Measure.map_apply (hV.prodMap measurable_id) hs,
    Measure.map_apply hj ((hV.prodMap measurable_id) hs),
    Measure.map_apply ((hV.mono hF le_rfl).prodMk hW) hs]
  rfl

theorem conditioned_joint_eq_map_compProd (μ : @Measure Ω mΩ) [IsProbabilityMeasure μ]
    {F : MeasurableSpace Ω} (hF : F ≤ mΩ) (W : Ω → β) (hW : Measurable[mΩ] W)
    (V : Ω → γ) (hV : Measurable[F] V) (C : Set Ω) (hC : MeasurableSet[F] C) :
    ((cond (μ.trim hF) C) ⊗ₘ conditionalKernel (mΩ := mΩ) μ F W).map (Prod.map V id) =
      @Measure.map Ω (γ × β) mΩ _ (fun ω => (V ω,W ω)) (@cond Ω mΩ μ C) := by
  rw [compProd_cond_base (μ.trim hF) (conditionalKernel (mΩ := mΩ) μ F W) C hC,
    conditionalKernel_disintegrate (mΩ := mΩ) μ hF W hW]
  have hj : @Measurable Ω (Ω × β) mΩ (F.prod mβ) (fun ω => (ω,W ω)) :=
    (measurable_id'' hF).prodMk hW
  ext s hs
  have ho := hV.prodMap (measurable_id (α := β))
  rw [Measure.map_apply ho hs, cond_apply (hC.prod MeasurableSet.univ),
    Measure.map_apply hj (hC.prod MeasurableSet.univ),
    Measure.map_apply hj ((hC.prod MeasurableSet.univ).inter (ho hs)),
    Measure.map_apply ((hV.mono hF le_rfl).prodMk hW) hs, cond_apply (hF C hC)]
  have hpreC : (fun ω => (ω,W ω)) ⁻¹' (C ×ˢ univ) = C := by ext ω; simp
  have hpreS : (fun ω => (ω,W ω)) ⁻¹' (C ×ˢ univ ∩ Prod.map V id ⁻¹' s) =
      C ∩ (fun ω => (V ω,W ω)) ⁻¹' s := by
    ext ω
    simp only [mem_preimage, mem_inter_iff, mem_prod, mem_univ, and_true, Prod.map_apply, id_eq]
  rw [hpreC,hpreS]

theorem conditioned_recorded_marginal (μ : @Measure Ω mΩ)
    {F : MeasurableSpace Ω} (hF : F ≤ mΩ)
    (V : Ω → γ) (hV : Measurable[F] V) (C : Set Ω) (hC : MeasurableSet[F] C) :
    (cond (μ.trim hF) C).map V = @Measure.map Ω γ mΩ _ V (@cond Ω mΩ μ C) := by
  ext s hs
  rw [Measure.map_apply hV hs, Measure.map_apply (hV.mono hF le_rfl) hs,
    cond_apply hC, cond_apply (hF C hC),
    trim_measurableSet_eq hF hC, trim_measurableSet_eq hF (hC.inter (hV hs))]

end
end PaperC.V282.StableConditionalKernel
