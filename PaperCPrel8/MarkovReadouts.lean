import PaperCPrel8.MicroscopicReadouts
import PaperCV282.CountableExpectationTransfer
import PaperCV282.SharpConditioningDiscrete
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-! # Sharp contraction for a common Markov kernel on the actual countable field

Centering a [0,1]-valued test at 1/2 removes the factor two from a signed
bounded-test estimate. The kernel and output space are otherwise arbitrary.
-/
namespace PaperC.Prel8.MarkovReadouts
open MeasureTheory ProbabilityTheory Filter
open PaperC.V282.CountableExpectationTransfer PaperC.V282.FiniteFieldTotalVariation
open PaperC.V282.SharpConditioning PaperC.V282.SharpConditioningDiscrete
open PaperC.V282.InfiniteMassCoupling
noncomputable section

/-- The half-L1 convention bounds every [0,1]-valued test with constant one. -/
theorem unit_interval_integral_discrepancy {α : Type*} [MeasurableSpace α]
    [Countable α] [MeasurableSingletonClass α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : α → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    |(∫ x, f x ∂μ)-(∫ x, f x ∂ν)| ≤ measureTotalVariation μ ν := by
  have hb : ∀ x, |f x-1/2| ≤ (1/2:ℝ) := fun x => abs_le.mpr (by constructor <;> linarith [hf x])
  have hint (ρ : Measure α) [IsProbabilityMeasure ρ] : Integrable f ρ := by
    apply (integrable_const (1:ℝ)).mono' (measurable_of_countable f).aestronglyMeasurable
    exact Eventually.of_forall fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hf x).1]; exact (hf x).2
  have h := integral_difference_le_tv μ ν measurable_id measurable_id (fun x => f x-1/2) (1/2) hb
  simp only [id_eq] at h
  rw [integral_sub (hint μ) (integrable_const _),integral_sub (hint ν) (integrable_const _)] at h
  simp only [integral_const,probReal_univ,one_smul] at h
  rw [measureTotalVariation_eq_mass]
  convert h using 1 <;> ring_nf

/-- The composed event mass is the integral of the actual conditional kernel probabilities. -/
theorem kernel_comp_real {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α)
    [IsFiniteMeasure μ] (κ : Kernel α β) [IsMarkovKernel κ]
    {B : Set β} (hB : MeasurableSet B) :
    (κ ∘ₘ μ).real B = ∫ x, (κ x).real B ∂μ := by
  rw [Measure.real,Measure.bind_apply hB κ.aemeasurable]
  exact (integral_toReal (κ.measurable_coe hB).aemeasurable
    (Eventually.of_forall fun x => measure_lt_top (κ x) B)).symm

/-- A common Markov kernel contracts TV into any measurable output space. -/
theorem common_kernel_contraction {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [MeasurableSingletonClass α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (κ : Kernel α β) [IsMarkovKernel κ] :
    measureTotalVariation (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ measureTotalVariation μ ν := by
  apply (measureTotalVariation_le_iff _ _ _).mpr
  intro B hB
  rw [kernel_comp_real μ κ hB,kernel_comp_real ν κ hB]
  apply unit_interval_integral_discrepancy
  intro x
  exact ⟨measureReal_nonneg, (measureReal_mono (Set.subset_univ B)).trans_eq probReal_univ⟩

open PaperC.InfiniteRademacher PaperC.Prel8.MicroscopicSiteRestoration
open PaperC.V282.BulkMarkedTypes PaperC.V282.BulkMarkedSource
open PaperC.V282.BulkMarkedTarget PaperC.V282.BulkMarkedComparison
open PaperC.V282.ConditionedCountableLaw PaperC.V282.MacroTransportRestoration
local instance : MeasurableSpace PaperC.F₂ := ⊤
local instance : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- The Markov-kernel clause of 7.8 for the genuine conditioned full microscopic field. -/
theorem microscopic_kernel_readout_le {β : Type*} [MeasurableSpace β]
    (M L : ℕ) (A : Set InfiniteSample) (hpos : 0 < infiniteRademacherMeasure.real A)
    (κ : Kernel (SpatialMarkedConfig (interiorStarts M L)) β) [IsMarkovKernel κ] :
    measureTotalVariation
      (κ ∘ₘ ((cond infiniteRademacherMeasure A).map (spatialMarkedSource (interiorStarts M L) L)))
      (κ ∘ₘ spatialTargetMeasure (interiorStarts M L) L) ≤
    massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure A
      (spatialMarkedSource (interiorStarts M L) L)) (spatialTargetLaw (interiorStarts M L) L) := by
  let : IsProbabilityMeasure (cond infiniteRademacherMeasure A) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hpos)
  have hm := measurable_spatialMarkedSource (interiorStarts M L) L
  let : IsProbabilityMeasure ((cond infiniteRademacherMeasure A).map (spatialMarkedSource (interiorStarts M L) L)) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  have h := common_kernel_contraction
    ((cond infiniteRademacherMeasure A).map (spatialMarkedSource (interiorStarts M L) L))
    (spatialTargetMeasure (interiorStarts M L) L) κ
  rwa [map_distance_eq_mass _ _ hm] at h

/-- Auxiliary marking followed by any measurable readout has the same bound. -/
theorem microscopic_marking_then_readout_le {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (M L : ℕ) (A : Set InfiniteSample) (hpos : 0 < infiniteRademacherMeasure.real A)
    (κ : Kernel (SpatialMarkedConfig (interiorStarts M L)) β) [IsMarkovKernel κ]
    (f : β → γ) (hf : Measurable f) :
    measureTotalVariation
      ((κ ∘ₘ ((cond infiniteRademacherMeasure A).map (spatialMarkedSource (interiorStarts M L) L))).map f)
      ((κ ∘ₘ spatialTargetMeasure (interiorStarts M L) L).map f) ≤
    massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure A
      (spatialMarkedSource (interiorStarts M L) L)) (spatialTargetLaw (interiorStarts M L) L) := by
  let : IsMarkovKernel (κ.map f) := Kernel.IsMarkovKernel.map κ hf
  rw [Measure.map_comp _ _ hf,Measure.map_comp _ _ hf]
  exact microscopic_kernel_readout_le M L A hpos (κ.map f)

end
end PaperC.Prel8.MarkovReadouts
