import PaperCV282.SpatialMarkedCritical
import PaperCV282.SpatialMarkedTargetAggregation

/-!
# Complete-field consequences without losing positions, marks, or signs first

Every deterministic statistic contracts the actual spatial comparison.
The total-count consequence uses the almost-sure source identity (5.11)
and the independently proved exact Poisson law of the target total.
-/
namespace PaperC.V282.SpatialMarkedStatistics

open MeasureTheory ProbabilityTheory InfiniteMassCoupling CountableLawTransfer
open FiniteFieldTotalVariation SpatialMarkedTypes SpatialMarkedSource SpatialMarkedTarget
open SpatialMarkedTargetAggregation SpatialMarkedFieldComparison SpatialMarkedCritical
open InfiniteRademacher InfiniteExactLengthProbabilityTransfer AllStartSoftPoisson
open PrimeEulerPNT ProcessAGGInput CriticalRunWindow SaddleErrorExponent
open InfiniteStartProbabilityTransfer

noncomputable section

local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

theorem observableLaw_congr_ae {Ω α : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {f g : Ω → α} (h : f=ᵐ[μ]g) : observableLaw μ f=observableLaw μ g := by
  funext a
  unfold observableLaw Measure.real
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [h] with ω hω
  change (f ω=a)=(g ω=a)
  rw [hω]

/-- No choice of deterministic statistic can increase the full configuration error. -/
theorem spatial_statistic_tv_le {α : Type*} (N L : ℕ) (stat : SpatialMarkedConfig N → α) :
    massTotalVariation (observableLaw infiniteRademacherMeasure (stat ∘ spatialMarkedSource N L))
      (observableLaw (spatialTargetMeasure N L) stat) ≤ spatialSignedDistance N L := by
  exact observableLaw_statistic_tv_le infiniteRademacherMeasure (spatialTargetMeasure N L)
    (measurable_spatialMarkedSource N L) measurable_id stat

theorem spatial_start_count_law_eq {N L : ℕ} (hN : 2≤N) :
    observableLaw infiniteRademacherMeasure ((totalSpatialCount N) ∘ spatialMarkedSource N L)=
      observableLaw infiniteRademacherMeasure (infiniteDyadicStartCount N L) :=
  observableLaw_congr_ae infiniteRademacherMeasure (ae_spatial_source_total_eq_startCount hN)

theorem spatial_target_total_law_eq (N L : ℕ) :
    observableLaw (spatialTargetMeasure N L) (totalSpatialCount N)=
      fun k => (poissonMeasure (fullRate N L)).real {k} :=
  observableLaw_of_hasLaw _ _ (hasLaw_totalSpatialCount N L)

/-- The same full-field upper bound applies to the actual scalar start count. -/
theorem spatial_start_count_tv_le {N L : ℕ} (hN : 2≤N) :
    massTotalVariation (observableLaw infiniteRademacherMeasure (infiniteDyadicStartCount N L))
      (fun k => (poissonMeasure (fullRate N L)).real {k}) ≤ spatialSignedDistance N L := by
  have h := spatial_statistic_tv_le N L (totalSpatialCount N)
  rw [spatial_start_count_law_eq hN,spatial_target_total_law_eq] at h
  exact h

/-- The scalar assertion in Theorem 1.1 inherits its coefficient from the complete signed field. -/
theorem theorem_one_one_start_count (hAGG : ProcessAGGStatement)
    (hPNT : PrimeNumberTheoremRemainder) (C : ℝ) (hC : 0≤C) (a : ℝ) (ha : a<1/Real.sqrt 2) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ, InRunLengthWindow C N L →
      massTotalVariation (observableLaw infiniteRademacherMeasure (infiniteDyadicStartCount N L))
        (fun k => (poissonMeasure (fullRate N L)).real {k}) ≤ Real.exp (-a*criticalScale N) := by
  obtain ⟨Nr,hr⟩ := theorem_one_one_lattice hAGG hPNT C hC a ha
  exact ⟨max Nr 2,fun N hN L hw =>
    (spatial_start_count_tv_le (by omega : 2≤N)).trans (hr N (by omega) L hw)⟩

end
end PaperC.V282.SpatialMarkedStatistics
