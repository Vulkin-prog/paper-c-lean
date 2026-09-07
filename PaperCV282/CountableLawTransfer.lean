import PaperCV282.InfiniteMassCoupling

/-!
# Removing truncations on actual countable probability spaces

The two probability spaces are arbitrary. A finite-coordinate comparison is
transported into a common countable configuration space, and both discarded
parts are charged by their actual disagreement probabilities.
-/
namespace PaperC.V282.CountableLawTransfer

open MeasureTheory InfiniteMassCoupling FiniteFieldTotalVariation MassPushforward

noncomputable section

/-- The image of the singleton masses is exactly the law of the composed observable. -/
theorem pushforwardMass_observableLaw {Ω α β : Type*}
    [MeasurableSpace Ω] [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsFiniteMeasure μ] {f : Ω → α} (hf : Measurable f) (g : α → β) :
    pushforwardMass g (observableLaw μ f) = observableLaw μ (g ∘ f) := by
  classical
  funext b
  rw [pushforwardMass_eq_restricted]
  have h := restricted_observableLaw_eq_event μ hf {a | g a = b}
  exact h

/-- Deterministic statistics contract the distance between actual laws. -/
theorem observableLaw_statistic_tv_le {Ω Ω' α β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : Ω → α} {g : Ω' → α} (hf : Measurable f) (hg : Measurable g) (stat : α → β) :
    massTotalVariation (observableLaw μ (stat ∘ f)) (observableLaw ν (stat ∘ g)) ≤
      massTotalVariation (observableLaw μ f) (observableLaw ν g) := by
  rw [← pushforwardMass_observableLaw μ hf, ← pushforwardMass_observableLaw ν hg]
  exact massTotalVariation_pushforward_le stat (hasSum_observableLaw μ hf)
    (hasSum_observableLaw ν hg) (observableLaw_nonneg μ f) (observableLaw_nonneg ν g)

/-- A genuine law identity gives the corresponding real singleton masses. -/
theorem observableLaw_of_hasLaw {Ω α : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure Ω) (ν : Measure α) {f : Ω → α} (h : ProbabilityTheory.HasLaw f ν μ) :
    observableLaw μ f = fun a => ν.real {a} := by
  funext a
  exact h.measureReal_eq (measurableSet_singleton a)

/-- A source/target truncation comparison needs no independence of either tail event. -/
theorem truncation_tv_le {Ω Ω' α β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [Countable β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : Ω → α} {g : Ω' → α} {fE : Ω → β} {gE : Ω' → β}
    (hf : Measurable f) (hg : Measurable g) (hfE : Measurable fE) (hgE : Measurable gE)
    (embed : β → α) :
    massTotalVariation (observableLaw μ f) (observableLaw ν g) ≤
      μ.real {ω | f ω ≠ embed (fE ω)} +
      massTotalVariation (observableLaw μ fE) (observableLaw ν gE) +
      ν.real {ω | g ω ≠ embed (gE ω)} := by
  have he : Measurable embed := measurable_of_countable _
  have hfe := he.comp hfE
  have hge := he.comp hgE
  have h1 := massTotalVariation_triangle (hasSum_observableLaw μ hf).summable
    (hasSum_observableLaw μ hfe).summable (hasSum_observableLaw ν hg).summable
    (observableLaw_nonneg μ f) (observableLaw_nonneg μ (embed ∘ fE)) (observableLaw_nonneg ν g)
  have h2 := massTotalVariation_triangle (hasSum_observableLaw μ hfe).summable
    (hasSum_observableLaw ν hge).summable (hasSum_observableLaw ν hg).summable
    (observableLaw_nonneg μ (embed ∘ fE)) (observableLaw_nonneg ν (embed ∘ gE))
    (observableLaw_nonneg ν g)
  have hs := massTotalVariation_observableLaw_le_disagreement μ hf hfe
  have ht := massTotalVariation_observableLaw_le_disagreement ν hg hge
  have hm := observableLaw_statistic_tv_le μ ν hfE hgE embed
  rw [massTotalVariation_comm (observableLaw ν g)] at ht
  dsimp only [Function.comp_apply] at hs ht
  linarith

/-- Any verified upper bounds for the two actual tails and the truncated comparison combine. -/
theorem truncation_tv_le_of_bounds {Ω Ω' α β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [Countable β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : Ω → α} {g : Ω' → α} {fE : Ω → β} {gE : Ω' → β}
    (hf : Measurable f) (hg : Measurable g) (hfE : Measurable fE) (hgE : Measurable gE)
    (embed : β → α) {sourceTail finiteError targetTail : ℝ}
    (hs : μ.real {ω | f ω ≠ embed (fE ω)} ≤ sourceTail)
    (hm : massTotalVariation (observableLaw μ fE) (observableLaw ν gE) ≤ finiteError)
    (ht : ν.real {ω | g ω ≠ embed (gE ω)} ≤ targetTail) :
    massTotalVariation (observableLaw μ f) (observableLaw ν g) ≤
      sourceTail + finiteError + targetTail := by
  exact (truncation_tv_le μ ν hf hg hfE hgE embed).trans (by gcongr)

end
end PaperC.V282.CountableLawTransfer
