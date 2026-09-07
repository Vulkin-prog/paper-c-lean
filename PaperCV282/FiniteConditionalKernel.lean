import PaperCV282.StableProductLift
import PaperCV282.SharpConditioningDiscrete

/-! # Regular conditional kernels and actual observed atoms

For a countable recorded environment, the regular conditional kernel agrees
almost everywhere with conditioning on the observed atom. The observed space
remains standard Borel in the kernel identity; countability is used only when
identifying total variation with the established mass-based expression.
-/
namespace PaperC.V282.FiniteConditionalKernel

open MeasureTheory ProbabilityTheory Set Filter MeasurableSpace
open StableConditionalKernel StableProductLift KernelTotalVariation SharpConditioning
open SharpConditioningDiscrete InfiniteMassCoupling ConditionedCountableLaw
open FiniteFieldTotalVariation

noncomputable section

variable {Ω α β : Type*} [mΩ : MeasurableSpace Ω] [mα : MeasurableSpace α]
  [MeasurableSpace β] [StandardBorelSpace β] [Nonempty β]

theorem conditionalKernel_comap_ae_eq_condDistrib
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (hX : Measurable X)
    (W : Ω → β) (hW : Measurable W) :
    (fun ω => conditionalKernel (mΩ := mΩ) μ (mα.comap X) W ω) =ᵐ[μ]
      (fun ω => condDistrib W X μ (X ω)) := by
  have hsets : ∀ᵐ ω ∂μ, ∀ s ∈ determiningAlgebra β,
      (conditionalKernel (mΩ := mΩ) μ (mα.comap X) W ω).real s =
        (condDistrib W X μ (X ω)).real s := by
    apply (ae_ball_iff determiningAlgebra_countable).mpr
    intro s hs
    have hsm := measurableSet_of_mem_determiningAlgebra hs
    exact (conditionalKernel_ae_eq_condExp μ hX.comap_le W hW s hsm).trans
      (condDistrib_ae_eq_condExp hX hW hsm).symm
  filter_upwards [hsets] with ω hω
  apply Measure.ext
  intro s hs
  have hd := discrepancy_le_of_algebra
    (conditionalKernel (mΩ := mΩ) μ (mα.comap X) W ω) (condDistrib W X μ (X ω)) 0
    (fun t ht => by rw [hω t ht]; simp) s hs
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hd)

theorem condDistrib_eq_conditional_map [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → α) (hX : Measurable X)
    (W : Ω → β) (hW : Measurable W) (x : α) (hx : μ.map X {x} ≠ 0) :
    condDistrib W X μ x = (cond μ (X ⁻¹' {x})).map W := by
  ext s hs
  rw [condDistrib_apply_of_ne_zero hW x hx s,
    Measure.map_apply hX (measurableSet_singleton x),
    Measure.map_apply (hX.prodMk hW) ((measurableSet_singleton x).prod hs),
    Measure.map_apply hW hs, cond_apply (hX (measurableSet_singleton x))]
  rfl

theorem observed_atom_nonzero_ae [Countable α]
    (μ : Measure Ω) (X : Ω → α) (hX : Measurable X) :
    ∀ᵐ ω ∂μ, μ.map X {X ω} ≠ 0 := by
  apply ae_of_ae_map (μ := μ) (p := fun x => μ.map X {x} ≠ 0) hX.aemeasurable
  exact ae_iff_of_countable.mpr (fun x hx => hx)

theorem conditionalKernel_comap_ae_eq_atom [Countable α] [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (hX : Measurable X)
    (W : Ω → β) (hW : Measurable W) :
    (fun ω => conditionalKernel (mΩ := mΩ) μ (mα.comap X) W ω) =ᵐ[μ]
      (fun ω => (cond μ (X ⁻¹' {X ω})).map W) := by
  filter_upwards [conditionalKernel_comap_ae_eq_condDistrib μ X hX W hW,
    observed_atom_nonzero_ae μ X hX] with ω hκ hp
  exact hκ.trans (condDistrib_eq_conditional_map μ X hX W hW (X ω) hp)

theorem conditionalTV_comap_ae_eq_atom_mass [Countable α] [MeasurableSingletonClass α]
    [Countable β] [MeasurableSingletonClass β]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (hX : Measurable X)
    (W : Ω → β) (hW : Measurable W) (ν : Measure β) [IsProbabilityMeasure ν] :
    conditionalTV μ (mα.comap X) W ν =ᵐ[μ]
      (fun ω => massTotalVariation (conditionalObservableLaw μ (X ⁻¹' {X ω}) W)
        (observableLaw ν id)) := by
  filter_upwards [conditionalKernel_comap_ae_eq_atom μ X hX W hW,
    observed_atom_nonzero_ae μ X hX] with ω hκ hp
  have hpos : μ (X ⁻¹' {X ω}) ≠ 0 := by
    rwa [Measure.map_apply hX (measurableSet_singleton _)] at hp
  letI instProbabilityAtom : IsProbabilityMeasure (cond μ (X ⁻¹' {X ω})) :=
    cond_isProbabilityMeasure hpos
  letI instProbabilityAtomMap : IsProbabilityMeasure ((cond μ (X ⁻¹' {X ω})).map W) :=
    Measure.isProbabilityMeasure_map hW.aemeasurable
  unfold conditionalTV
  rw [hκ, measureTotalVariation_eq_mass]
  congr 1
  funext b
  rw [observableLaw_eq_map _ measurable_id, Measure.map_id]
  exact (observableLaw_eq_map _ hW b).symm

end
end PaperC.V282.FiniteConditionalKernel
