import PaperC.Probability.ExactLengthCountVectorTransfer
import PaperC.Probability.ConditionalAGGAverage
import PaperC.Probability.SectionThirteenCouplings

/-!
# Conditional mixture identity for the retained marked count vector

The marked dependency graph is used after fixing the prime signs up to
`Y_Q`.  This file identifies the uniform mixture of the resulting
conditional vector laws with the concrete full-cylinder retained law used by
`CorollaryFourteenEightCounts`.

The identity is exact and finite; it is the vector-valued analogue of the
scalar mixture identity in Section 13.
-/

namespace PaperC
namespace MarkedCountVectorMixture

open ArratiaGoldsteinGordonInput
open ConditionalAGGAverage
open ConditionalAGGInstantiation
open ConditionalStartProbability
open ExactLengthCountVectorTransfer
open MarkedConditionalDependencyGraph
open SectionThirteenFiniteBound
open SectionThirteenCouplings

noncomputable section

local instance (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- Retained vector after fixing the small-prime assignment. -/
def conditionedRetainedExactLengthCountVector
    (N L E : ℕ)
    (σ :
      SmallSample
        (markedCylinderCutoff N L E) (markedPrimeCutoff L E))
    (η :
      LargeSample
        (markedCylinderCutoff N L E) (markedPrimeCutoff L E)) :
    ExactLengthCountVector E :=
  finiteRetainedExactLengthCountVector N L E
    (assemble (markedCylinderCutoff N L E)
      (markedPrimeCutoff L E) σ η)

/-- Conditional joint law of the retained count vector. -/
def conditionalRetainedExactLengthCountVectorLaw
    (N L E : ℕ)
    (σ :
      SmallSample
        (markedCylinderCutoff N L E) (markedPrimeCutoff L E))
    (k : ExactLengthCountVector E) : ℝ :=
  eventProbability
    (largeUniformPMF
      (markedCylinderCutoff N L E) (markedPrimeCutoff L E))
    (fun η ↦
      conditionedRetainedExactLengthCountVector N L E σ η = k)

/-- Uniform mixture of the conditional retained vector laws. -/
def averagedConditionalRetainedExactLengthCountVectorLaw
    (N L E : ℕ) (k : ExactLengthCountVector E) : ℝ :=
  finiteUniformAverage
    (fun σ :
        SmallSample
          (markedCylinderCutoff N L E) (markedPrimeCutoff L E) ↦
      conditionalRetainedExactLengthCountVectorLaw N L E σ k)

/--
The conditional mixture is exactly the retained law on the full common
prime cylinder.
-/
theorem averagedConditionalRetainedExactLengthCountVectorLaw_eq_finite
    (N L E : ℕ) (k : ExactLengthCountVector E) :
    averagedConditionalRetainedExactLengthCountVectorLaw N L E k =
      finiteRetainedExactLengthCountVectorLaw N L E k := by
  classical
  let P : SampleSpace (markedCylinderCutoff N L E) → Prop :=
    fun ω ↦ finiteRetainedExactLengthCountVector N L E ω = k
  have htotal :=
    finiteUniformAverage_largeEventProbability_eq_full
      (markedCylinderCutoff N L E) (markedPrimeCutoff L E) P
  simpa only [
    averagedConditionalRetainedExactLengthCountVectorLaw,
    conditionalRetainedExactLengthCountVectorLaw,
    conditionedRetainedExactLengthCountVector,
    finiteRetainedExactLengthCountVectorLaw, P] using htotal

end

end MarkedCountVectorMixture
end PaperC
