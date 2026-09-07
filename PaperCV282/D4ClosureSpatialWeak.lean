import PaperCV282.D4ClosureSpatialHalfLines
import PaperCV282.PoissonPointProcess

/-! # Coupled grid convergence on the entire upper half-line

The source measure may also be the actual conditional measure given a count.
The pointwise convergence retains all geometric excesses simultaneously.
-/
namespace PaperC.V282.D4ClosureSpatialWeak

open MeasureTheory ProbabilityTheory Filter
open D4ClosurePointMeasure D4ClosureSpatialHalfLines PointMeasureSpace
open scoped Topology BoundedContinuousFunction

noncomputable section

def gridPointLaw (mu : Measure IntegerSpatialSample) [IsProbabilityMeasure mu]
    (N : ℕ) (hN : 0<N) (m : ℤ) : ProbabilityMeasure (PointMeasure (ℝ × (ℕ × F₂))) :=
  ⟨mu.map (halfLineGridPoints N hN m),
    Measure.isProbabilityMeasure_map (measurable_halfLineGridPoints N hN m).aemeasurable⟩

def upperPointLaw (mu : Measure IntegerSpatialSample) [IsProbabilityMeasure mu]
    (m : ℤ) : ProbabilityMeasure (PointMeasure (ℝ × (ℕ × F₂))) :=
  ⟨mu.map (halfLinePointConfiguration m),
    Measure.isProbabilityMeasure_map (measurable_halfLinePointConfiguration m).aemeasurable⟩

/-- This applies in particular to conditioning the actual integer-level process
on any positive-probability count event. -/
theorem gridPointLaw_tendsto (mu : Measure IntegerSpatialSample) [IsProbabilityMeasure mu]
    (sizes : ℕ → ℕ) (hN : ∀ n, 0<sizes n) (hsizes : Tendsto sizes atTop atTop) (m : ℤ) :
    Tendsto (fun n => gridPointLaw mu (sizes n) (hN n) m) atTop (𝓝 (upperPointLaw mu m)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have hg (n : ℕ) :
      (∫ x, f x ∂(gridPointLaw mu (sizes n) (hN n) m : Measure _)) =
      ∫ sample, f (halfLineGridPoints (sizes n) (hN n) m sample) ∂mu :=
    integral_map (measurable_halfLineGridPoints _ _ _).aemeasurable
      f.continuous.measurable.aestronglyMeasurable
  have hu : (∫ x, f x ∂(upperPointLaw mu m : Measure _)) =
      ∫ sample, f (halfLinePointConfiguration m sample) ∂mu :=
    integral_map (measurable_halfLinePointConfiguration m).aemeasurable
      f.continuous.measurable.aestronglyMeasurable
  simp_rw [hg,hu]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
  · intro n
    exact (f.continuous.measurable.comp (measurable_halfLineGridPoints _ _ _)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact Filter.Eventually.of_forall (fun sample => f.norm_coe_le_norm _)
  · exact Filter.Eventually.of_forall (fun sample => f.continuous.continuousAt.tendsto.comp
      (halfLineGridPoints_tendsto sizes hN hsizes m sample))

end
end PaperC.V282.D4ClosureSpatialWeak
