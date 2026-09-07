import PaperCV282.SpatialDiffuseMarks

/-! # The spatial configuration as a genuine finite point measure

The location attached to site i is 1+i/N. Multiplicities are preserved by
the sum of Dirac measures. The complete grid target has exactly the law of
the independently marked Poisson sample constructed from a uniform position.
-/
namespace PaperC.V282.SpatialPointEmbedding

open MeasureTheory ProbabilityTheory PointMeasureSpace SpatialDiffuseMarks
open SpatialMarkedTypes SpatialMarkedTarget SpatialMarkedPoissonIdentification
open PoissonPointProcess GeneralPoissonMarking AllStartSoftPoisson
open scoped BigOperators NNReal Topology

noncomputable section

def spatialPosition (N : ℕ) (j : SpatialMarkedIndex N) : ℝ × (ℕ × F₂) :=
  (1 + (j.1.val : ℝ) / (N : ℝ), j.2)

def spatialPointEmbedding (N : ℕ) (config : SpatialMarkedConfig N) :
    PointMeasure (ℝ × (ℕ × F₂)) :=
  config.sum (fun j n => n • pointDirac (spatialPosition N j))

theorem measurable_spatialPointEmbedding (N : ℕ) : Measurable (spatialPointEmbedding N) :=
  measurable_of_countable _

theorem spatialPosition_mem_interval (N : ℕ) (j : SpatialMarkedIndex N) :
    (spatialPosition N j).1 ∈ Set.Icc (1 : ℝ) 2 := by
  have hN : 0 < N := Nat.zero_lt_of_lt j.1.isLt
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hj : (j.1.val : ℝ) < (N : ℝ) := by exact_mod_cast j.1.isLt
  change 1 ≤ 1 + (j.1.val : ℝ) / (N : ℝ) ∧ 1 + (j.1.val : ℝ) / (N : ℝ) ≤ 2
  have hlo : 0 ≤ (j.1.val : ℝ) / (N : ℝ) := div_nonneg (Nat.cast_nonneg _) hNR.le
  have hhi : (j.1.val : ℝ) / (N : ℝ) ≤ 1 := (div_le_one hNR).mpr hj.le
  constructor <;> linarith

def gridPhysicalMark (N : ℕ) (hN : 0 < N) (x : unitInterval × (ℕ × F₂)) :
    ℝ × (ℕ × F₂) := spatialPosition N (gridMark N hN x)

theorem measurable_gridPhysicalMark (N : ℕ) (hN : 0 < N) :
    Measurable (gridPhysicalMark N hN) :=
  (measurable_of_countable (spatialPosition N)).comp (measurable_gridMark N hN)

theorem spatialPointEmbedding_sampledConfiguration {X : Type*} (N : ℕ)
    (mark : X → SpatialMarkedIndex N) (sample : ℕ × (ℕ → X)) :
    spatialPointEmbedding N (sampledConfiguration N mark sample) =
      mappedPointMeasure (fun x => spatialPosition N (mark x)) sample := by
  classical
  unfold spatialPointEmbedding sampledConfiguration mappedPointMeasure samplePointMeasure fixedPointMeasure
  rw [← Finsupp.sum_finsetSum_index]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finsupp.sum_single_index (by simp)]
    simp only [one_nsmul]
  · intro j
    simp only [zero_nsmul]
  · intro j n m
    exact add_nsmul _ _ _

def spatialPointTargetLaw (N L : ℕ) : ProbabilityMeasure (PointMeasure (ℝ × (ℕ × F₂))) :=
  ⟨(spatialTargetMeasure N L).map (spatialPointEmbedding N),
    Measure.isProbabilityMeasure_map (measurable_spatialPointEmbedding N).aemeasurable⟩

theorem spatialPointTargetLaw_eq_poissonPointLaw (N L : ℕ) (hN : 0 < N) :
    spatialPointTargetLaw N L = poissonPointLaw (fullRate N L) spatialMarkMeasure
      (gridPhysicalMark N hN) (measurable_gridPhysicalMark N hN) := by
  apply Subtype.ext
  have hm : HasLaw (spatialPointEmbedding N) (spatialPointTargetLaw N L)
      (spatialTargetMeasure N L) := ⟨(measurable_spatialPointEmbedding N).aemeasurable, rfl⟩
  have h := hm.comp (hasLaw_grid_configuration N L hN)
  have heq : spatialPointEmbedding N ∘ sampledConfiguration N (gridMark N hN) =
      mappedPointMeasure (gridPhysicalMark N hN) := by
    funext sample
    exact spatialPointEmbedding_sampledConfiguration N (gridMark N hN) sample
  rw [heq] at h
  exact h.map_eq.symm

end
end PaperC.V282.SpatialPointEmbedding
