import PaperCV282.SpatialPointConvergence
import PaperCV282.SpatialMarkedCritical
import PaperCV282.CountableWeakTransfer

/-!
# The diffuse limit of the actual complete signed run field

The complete arithmetic source is embedded as a finite sum of Dirac measures
at its physical positions. Its lattice total variation error transfers the
independently proved weak limit of the complete Poisson target. Block sizes
may follow any diverging subsequence, as required for the oscillating dyadic
intensity; no convergence is assumed along all consecutive sizes.
-/
namespace PaperC.V282.SpatialMarkedDiffuse

open MeasureTheory Filter InfiniteRademacher SpatialMarkedTypes SpatialMarkedSource
open SpatialMarkedTarget SpatialMarkedFieldComparison SpatialMarkedCritical
open SpatialPointEmbedding SpatialPointConvergence CountableWeakTransfer PointMeasureSpace
open AllStartSoftPoisson CriticalRunWindow PrimeEulerPNT ProcessAGGInput
open scoped Topology NNReal

noncomputable section

local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

def spatialPointSourceLaw (N L : ℕ) : ProbabilityMeasure (PointMeasure (ℝ × (ℕ × F₂))) :=
  imageProbabilityLaw infiniteRademacherMeasure
    ((spatialPointEmbedding N) ∘ (spatialMarkedSource N L))
    ((measurable_spatialPointEmbedding N).comp (measurable_spatialMarkedSource N L))

/-- The weak-limit assertion of Theorem 1.1, on the true infinite multiplicative
probability space and with every excess and both signs retained simultaneously. -/
theorem theorem_one_one_diffuse (hAGG : ProcessAGGStatement)
    (hPNT : PrimeNumberTheoremRemainder) (C : ℝ) (hC : 0 ≤ C)
    (sizes lengths : ℕ → ℕ) (rate : ℝ≥0)
    (hsizes : Tendsto sizes atTop atTop)
    (hwindow : ∀ᶠ j in atTop, InRunLengthWindow C (sizes j) (lengths j))
    (hrate : Tendsto (fun j => (fullRate (sizes j) (lengths j) : ℝ)) atTop (𝓝 (rate : ℝ))) :
    Tendsto (fun j => spatialPointSourceLaw (sizes j) (lengths j)) atTop
      (𝓝 (diffusePoissonLaw rate)) := by
  have htv := spatial_signed_critical_tendsto_zero_along hAGG hPNT C hC
    sizes lengths hsizes hwindow
  have htarget := spatialPointTargetLaw_tendsto sizes lengths rate hsizes hrate
  exact countable_lattice_weak_transfer (fun j => SpatialMarkedConfig (sizes j))
    infiniteRademacherMeasure (fun j => spatialTargetMeasure (sizes j) (lengths j))
    (fun j => spatialMarkedSource (sizes j) (lengths j))
    (fun j => measurable_spatialMarkedSource (sizes j) (lengths j))
    (fun j => spatialPointEmbedding (sizes j)) (diffusePoissonLaw rate) htv htarget

end
end PaperC.V282.SpatialMarkedDiffuse
