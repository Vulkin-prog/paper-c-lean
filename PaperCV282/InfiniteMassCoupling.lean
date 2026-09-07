import PaperCV282.PoissonFieldMeasure

/-!
# Coupling actual countable laws on an arbitrary probability space

The source may be an infinite product space. The law and the disagreement
probability are both taken in the same actual probability measure.
-/

namespace PaperC.V282.InfiniteMassCoupling

open MeasureTheory FiniteFieldTotalVariation PoissonFieldMeasure MassPushforward
open scoped BigOperators ENNReal

noncomputable section

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- The real singleton masses of the actual observable. -/
def observableLaw {Ω α : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → α) (a : α) : ℝ := μ.real {ω | f ω=a}

theorem observableLaw_nonneg {Ω α : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → α) (a : α) : 0 ≤ observableLaw μ f a :=
  ENNReal.toReal_nonneg

theorem observableLaw_eq_map {Ω α : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [MeasurableSingletonClass α] (μ : Measure Ω)
    {f : Ω → α} (hf : Measurable f) (a : α) :
    observableLaw μ f a = (μ.map f).real {a} := by
  unfold observableLaw Measure.real
  rw [Measure.map_apply hf (measurableSet_singleton a)]
  rfl

theorem hasSum_observableLaw {Ω α : Type*} [MeasurableSpace Ω]
    [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → α} (hf : Measurable f) :
    HasSum (observableLaw μ f) 1 := by
  letI : IsProbabilityMeasure (μ.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  have hsum : (∑' a : α, (μ.map f) {a})=1 := by
    simpa using (μ.map f).tsum_indicator_apply_singleton Set.univ MeasurableSet.univ
  have h := ENNReal.hasSum_toReal (f := fun a : α => (μ.map f) {a}) (by rw [hsum]; simp)
  rw [← ENNReal.tsum_toReal_eq (fun a => measure_ne_top (μ.map f) {a}),hsum,ENNReal.toReal_one] at h
  convert h using 1
  funext a
  exact observableLaw_eq_map μ hf a

theorem restricted_observableLaw_eq_event {Ω α : Type*} [MeasurableSpace Ω]
    [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsFiniteMeasure μ] {f : Ω → α} (hf : Measurable f) (A : Set α) :
    (∑' a : α, if a ∈ A then observableLaw μ f a else 0)=μ.real (f ⁻¹' A) := by
  classical
  change (∑' a : α, A.indicator (observableLaw μ f) a)=_
  rw [← tsum_subtype A]
  simp_rw [observableLaw_eq_map μ hf]
  rw [real_tsum_singletons,Measure.real,Measure.map_apply hf (Set.to_countable A).measurableSet]
  rfl

theorem event_discrepancy_le_disagreement {Ω α : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f g : Ω → α) (A : Set α) :
    |μ.real (f ⁻¹' A)-μ.real (g ⁻¹' A)| ≤ μ.real {ω | f ω≠g ω} := by
  have hfg : f ⁻¹' A ⊆ g ⁻¹' A ∪ {ω | f ω≠g ω} := by
    intro ω hω
    by_cases h : f ω=g ω
    · exact Or.inl (by simpa [← h] using hω)
    · exact Or.inr h
  have hgf : g ⁻¹' A ⊆ f ⁻¹' A ∪ {ω | f ω≠g ω} := by
    intro ω hω
    by_cases h : f ω=g ω
    · exact Or.inl (by simpa [h] using hω)
    · exact Or.inr h
  have h1 := (measureReal_mono (μ := μ) hfg).trans (measureReal_union_le _ _)
  have h2 := (measureReal_mono (μ := μ) hgf).trans (measureReal_union_le _ _)
  exact abs_sub_le_iff.mpr ⟨by linarith,by linarith⟩

/-- A coupling of two measurable observables bounds their exact half-L1 distance. -/
theorem massTotalVariation_observableLaw_le_disagreement {Ω α : Type*}
    [MeasurableSpace Ω] [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f g : Ω → α}
    (hf : Measurable f) (hg : Measurable g) :
    massTotalVariation (observableLaw μ f) (observableLaw μ g) ≤ μ.real {ω | f ω≠g ω} := by
  apply massTotalVariation_le_of_test_sets (hasSum_observableLaw μ hf)
    (hasSum_observableLaw μ hg) (observableLaw_nonneg μ f) (observableLaw_nonneg μ g)
  intro A
  rw [restricted_observableLaw_eq_event μ hf,restricted_observableLaw_eq_event μ hg]
  exact event_discrepancy_le_disagreement μ f g A

/-- An event containing every discrepancy is enough; it need not be an independent event. -/
theorem massTotalVariation_observableLaw_le_event {Ω α : Type*}
    [MeasurableSpace Ω] [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f g : Ω → α}
    (hf : Measurable f) (hg : Measurable g) {E : Set Ω}
    (h : ∀ ω, ω ∉ E → f ω=g ω) :
    massTotalVariation (observableLaw μ f) (observableLaw μ g) ≤ μ.real E := by
  apply (massTotalVariation_observableLaw_le_disagreement μ hf hg).trans
  apply measureReal_mono (μ := μ) _ (measure_ne_top μ E)
  intro ω hω
  by_contra hn
  exact hω (h ω hn)

end
end PaperC.V282.InfiniteMassCoupling
