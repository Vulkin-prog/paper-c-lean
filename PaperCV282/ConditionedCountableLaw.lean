import PaperCV282.CountableLawTransfer
import Mathlib.Probability.ConditionalProbability

/-!
# Genuine conditional laws on countable configuration spaces

Conditioning uses the normalized restriction of the original probability
measure. In particular, a discarded source event costs its original mass
divided by the actual positive conditioning probability.
-/
namespace PaperC.V282.ConditionedCountableLaw

open MeasureTheory ProbabilityTheory InfiniteMassCoupling FiniteFieldTotalVariation

noncomputable section

def conditionalObservableLaw {Ω α : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (C : Set Ω) (f : Ω → α) : α → ℝ :=
  observableLaw (cond μ C) f

theorem measure_ne_zero_of_real_pos {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {C : Set Ω} (hC : 0 < μ.real C) : μ C ≠ 0 := by
  intro h
  simp [Measure.real,h] at hC

theorem conditionalObservableLaw_eq_ratio {Ω α : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (C : Set Ω) (hC : MeasurableSet C) (f : Ω → α) (a : α) :
    conditionalObservableLaw μ C f a = μ.real ({ω | f ω=a} ∩ C) / μ.real C := by
  unfold conditionalObservableLaw observableLaw Measure.real
  rw [cond_apply hC, ENNReal.toReal_mul, ENNReal.toReal_inv]
  rw [Set.inter_comm]
  ring

theorem conditionalObservableLaw_nonneg {Ω α : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (C : Set Ω) (f : Ω → α) (a : α) :
    0 ≤ conditionalObservableLaw μ C f a := observableLaw_nonneg _ _ _

theorem hasSum_conditionalObservableLaw {Ω α : Type*} [MeasurableSpace Ω]
    [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsFiniteMeasure μ] (C : Set Ω) (hC : 0 < μ.real C)
    {f : Ω → α} (hf : Measurable f) : HasSum (conditionalObservableLaw μ C f) 1 := by
  letI : IsProbabilityMeasure (cond μ C) := cond_isProbabilityMeasure (measure_ne_zero_of_real_pos μ hC)
  exact hasSum_observableLaw _ hf

theorem conditional_event_le_div_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (C : Set Ω) (hC : MeasurableSet C) (A : Set Ω) :
    (cond μ C).real A ≤ μ.real A / μ.real C := by
  unfold Measure.real
  rw [cond_apply hC,ENNReal.toReal_mul,ENNReal.toReal_inv]
  have h := measureReal_mono (μ := μ) (Set.inter_subset_right : C ∩ A ⊆ A)
  change (μ C).toReal⁻¹*(μ (C ∩ A)).toReal ≤ _
  calc
    _ ≤ (μ C).toReal⁻¹*(μ A).toReal := mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

/-- The actual event-conditioned coupling is controlled by the unconditioned tail. -/
theorem conditional_tv_le_disagreement_div_probability {Ω α : Type*}
    [MeasurableSpace Ω] [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsFiniteMeasure μ] (C : Set Ω) (hC : MeasurableSet C)
    (hpos : 0 < μ.real C) {f g : Ω → α} (hf : Measurable f) (hg : Measurable g) :
    massTotalVariation (conditionalObservableLaw μ C f) (conditionalObservableLaw μ C g) ≤
      μ.real {ω | f ω≠g ω} / μ.real C := by
  letI : IsProbabilityMeasure (cond μ C) := cond_isProbabilityMeasure (measure_ne_zero_of_real_pos μ hpos)
  exact (massTotalVariation_observableLaw_le_disagreement (cond μ C) hf hg).trans
    (conditional_event_le_div_probability μ C hC _)

theorem conditional_statistic_tv_le {Ω Ω' α β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsFiniteMeasure μ] (C : Set Ω) (hpos : 0 < μ.real C)
    (ν : Measure Ω') [IsProbabilityMeasure ν] {f : Ω → α} {g : Ω' → α}
    (hf : Measurable f) (hg : Measurable g) (stat : α → β) :
    massTotalVariation (conditionalObservableLaw μ C (stat ∘ f)) (observableLaw ν (stat ∘ g)) ≤
      massTotalVariation (conditionalObservableLaw μ C f) (observableLaw ν g) := by
  letI : IsProbabilityMeasure (cond μ C) := cond_isProbabilityMeasure (measure_ne_zero_of_real_pos μ hpos)
  exact CountableLawTransfer.observableLaw_statistic_tv_le (cond μ C) ν hf hg stat

end
end PaperC.V282.ConditionedCountableLaw
