import PaperCV282.CrossoverSparseSource

/-! # A total sequence of moving crossover targets and the actual comparison distances

The border-only default at an empty bulk population permits statements for
arbitrary initial indices. The rare logarithmic regime eventually has a
nonempty bulk population, where this is exactly the printed mixed law.
-/
namespace PaperC.V282.CrossoverMovingTarget

open MeasureTheory CrossoverMarkedModel CrossoverMarkedTarget CrossoverSparseSource
open CrossoverMarkedCandidate BulkMarkedGeometry SharpConditioning

noncomputable section
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

def targetLaw (M L : ℕ) (delta : ℝ) : Measure Record :=
  if hs : (bulkStarts M L delta).Nonempty then mixedLaw (bulkStarts M L delta) hs L else borderLaw

instance instProbabilityTargetLaw (M L : ℕ) (delta : ℝ) : IsProbabilityMeasure (targetLaw M L delta) := by
  unfold targetLaw
  split_ifs <;> infer_instance

theorem targetLaw_eq {M L : ℕ} {delta : ℝ} (hs : (bulkStarts M L delta).Nonempty) :
    targetLaw M L delta=mixedLaw (bulkStarts M L delta) hs L := by simp only [targetLaw,dif_pos hs]

def actualDistance (M L : ℕ) (delta : ℝ) : ℝ :=
  measureTotalVariation (conditionalGammaLaw M L delta) (targetLaw M L delta)

def cappedDistance (M L K : ℕ) (delta : ℝ) : ℝ :=
  measureTotalVariation ((conditionalGammaLaw M L delta).map (capBorder K))
    ((targetLaw M L delta).map (capBorder K))

theorem actualDistance_nonneg {M L : ℕ} (delta : ℝ) (hLM : L≤M) : 0≤actualDistance M L delta := by
  letI instProbabilityGamma : IsProbabilityMeasure (conditionalGammaLaw M L delta) :=
    conditionalGammaLaw_probability delta hLM
  exact measureTotalVariation_nonneg _ _

theorem cappedDistance_nonneg {M L : ℕ} (K : ℕ) (delta : ℝ) (hLM : L≤M) : 0≤cappedDistance M L K delta := by
  letI instProbabilityGamma : IsProbabilityMeasure (conditionalGammaLaw M L delta) :=
    conditionalGammaLaw_probability delta hLM
  letI instProbabilityCappedGamma : IsProbabilityMeasure ((conditionalGammaLaw M L delta).map (capBorder K)) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  letI instProbabilityCappedTarget : IsProbabilityMeasure ((targetLaw M L delta).map (capBorder K)) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  exact measureTotalVariation_nonneg _ _

end
end PaperC.V282.CrossoverMovingTarget
