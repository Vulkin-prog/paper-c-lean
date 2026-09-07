import PaperCV282.SharpConditioning

/-! # The sharp general conditioning inequality in the discrete law convention -/
namespace PaperC.V282.SharpConditioningDiscrete

open MeasureTheory ProbabilityTheory SharpConditioning InfiniteMassCoupling
open FiniteFieldTotalVariation ConditionedCountableLaw

noncomputable section

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

variable {α β Ω : Type*}

theorem restricted_difference_le {p q : α → ℝ}
    (hp : HasSum p 1) (hq : HasSum q 1)
    (hp0 : ∀ a, 0 ≤ p a) (hq0 : ∀ a, 0 ≤ q a) (A : Set α) :
    (∑' a, if a ∈ A then p a else 0) - (∑' a, if a ∈ A then q a else 0) ≤
      massTotalVariation p q := by
  classical
  rw [massTotalVariation_eq_positive_set hp hq hp0 hq0]
  have hpA := summable_restricted_mass hp.summable hp0 A
  have hqA := summable_restricted_mass hq.summable hq0 A
  have hpP : Summable (fun a => if q a ≤ p a then p a else 0) := by
    apply hp.summable.of_nonneg_of_le
    · intro a; split_ifs <;> simp [hp0]
    · intro a; split_ifs <;> simp [hp0]
  have hqP : Summable (fun a => if q a ≤ p a then q a else 0) := by
    apply hq.summable.of_nonneg_of_le
    · intro a; split_ifs <;> simp [hq0]
    · intro a; split_ifs <;> simp [hq0]
  have h := (hpA.sub hqA).tsum_le_tsum (g := fun a =>
      (if q a ≤ p a then p a else 0) - (if q a ≤ p a then q a else 0))
    (fun a => by
      by_cases hA : a ∈ A
      · by_cases hP : q a ≤ p a
        · simp [hA, hP]
        · simp [hA, hP, le_of_not_ge hP]
      · by_cases hP : q a ≤ p a
        · simp [hA, hP]
        · simp [hA, hP])
    (hpP.sub hqP)
  rw [hpA.tsum_sub hqA, hpP.tsum_sub hqP] at h
  convert h using 1

theorem restricted_discrepancy_le {p q : α → ℝ}
    (hp : HasSum p 1) (hq : HasSum q 1)
    (hp0 : ∀ a, 0 ≤ p a) (hq0 : ∀ a, 0 ≤ q a) (A : Set α) :
    |(∑' a, if a ∈ A then p a else 0) - (∑' a, if a ∈ A then q a else 0)| ≤
      massTotalVariation p q := by
  have h1 := restricted_difference_le hp hq hp0 hq0 A
  have h2 := restricted_difference_le hq hp hq0 hp0 A
  rw [massTotalVariation_comm q p] at h2
  exact abs_sub_le_iff.mpr ⟨h1,h2⟩

theorem measureTotalVariation_eq_mass [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    measureTotalVariation μ ν = massTotalVariation (observableLaw μ id) (observableLaw ν id) := by
  apply le_antisymm
  · apply (measureTotalVariation_le_iff _ _ _).mpr
    intro A _
    have h := restricted_discrepancy_le (hasSum_observableLaw μ measurable_id)
      (hasSum_observableLaw ν measurable_id) (observableLaw_nonneg μ id)
      (observableLaw_nonneg ν id) A
    simpa only [restricted_observableLaw_eq_event μ measurable_id,
      restricted_observableLaw_eq_event ν measurable_id, Set.preimage_id_eq, id_eq] using h
  · apply massTotalVariation_le_of_test_sets (hasSum_observableLaw μ measurable_id)
      (hasSum_observableLaw ν measurable_id) (observableLaw_nonneg μ id)
      (observableLaw_nonneg ν id)
    intro A
    rw [restricted_observableLaw_eq_event μ measurable_id,
      restricted_observableLaw_eq_event ν measurable_id]
    exact discrepancy_le μ ν A (Set.to_countable A).measurableSet

theorem measureTotalVariation_map_eq_mass [MeasurableSpace Ω]
    [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : Ω → α} (hf : Measurable f) :
    measureTotalVariation (μ.map f) (ν.map f) =
      massTotalVariation (observableLaw μ f) (observableLaw ν f) := by
  letI instProbabilityLocal1 : IsProbabilityMeasure (μ.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  letI instProbabilityLocal2 : IsProbabilityMeasure (ν.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  rw [measureTotalVariation_eq_mass]
  congr 1 <;> funext a
  · change (μ.map f).real {a} = observableLaw μ f a
    exact (observableLaw_eq_map μ hf a).symm
  · change (ν.map f).real {a} = observableLaw ν f a
    exact (observableLaw_eq_map ν hf a).symm

/-- Conditioning commutes with a genuine measurable observation. -/
theorem map_cond_eq [MeasurableSpace Ω] [MeasurableSpace α]
    (μ : Measure Ω) {f : Ω → α} (hf : Measurable f)
    (B : Set α) (hB : MeasurableSet B) :
    (cond μ (f ⁻¹' B)).map f = cond (μ.map f) B := by
  ext A hA
  rw [Measure.map_apply hf hA, cond_apply (hf hB), cond_apply hB,
    Measure.map_apply hf hB, Measure.map_apply hf (hB.inter hA)]
  rfl

/-- A marginal of the conditioned laws obeys the same sharp denominator. -/
theorem lemma_six_two_observable [MeasurableSpace Ω]
    [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (B : Set Ω) (hB : MeasurableSet B) {f : Ω → α} (hf : Measurable f)
    {ε : ℝ} (htv : measureTotalVariation μ ν ≤ ε) (hε : ε < ν.real B) :
    0 < μ.real B ∧
    massTotalVariation (conditionalObservableLaw μ B f) (conditionalObservableLaw ν B f) ≤
      ε / max (ν.real B) (μ.real B) := by
  obtain ⟨hq, hb, _⟩ := lemma_six_two μ ν B hB htv hε
  have hp : 0 < ν.real B := lt_of_le_of_lt ((measureTotalVariation_nonneg μ ν).trans htv) hε
  letI instProbabilityLocal3 : IsProbabilityMeasure (cond μ B) := cond_isProbabilityMeasure (measure_ne_zero_of_real_pos μ hq)
  letI instProbabilityLocal4 : IsProbabilityMeasure (cond ν B) := cond_isProbabilityMeasure (measure_ne_zero_of_real_pos ν hp)
  refine ⟨hq, ?_⟩
  rw [conditionalObservableLaw, conditionalObservableLaw, ← measureTotalVariation_map_eq_mass _ _ hf]
  exact (measureTotalVariation_map_le _ _ hf).trans hb

end
end PaperC.V282.SharpConditioningDiscrete
