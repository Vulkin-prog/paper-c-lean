import PaperCV282.D4ClosureHalfLines
import PaperCV282.UniformSpatialGrid
import Mathlib.MeasureTheory.Measure.GiryMonad

/-! # A genuine locally finite spatial target on all integer levels

There are independent Poisson counts at every integer level, and independent
uniform positions for every possible point. The total measure need not be
finite; every compact set, and each entire fixed level, has finite mass.
-/
namespace PaperC.V282.D4ClosurePointMeasure

open MeasureTheory ProbabilityTheory
open D4ClosureIntegerLevels UniformSpatialGrid GeneralPoissonMarking
open scoped BigOperators NNReal ENNReal Topology

noncomputable section

@[reducible]
def IntegerSpatialSample := ℤ → (ℕ × (ℕ → unitInterval))

@[reducible]
instance instMeasurableIntegerSpatialSample : MeasurableSpace IntegerSpatialSample :=
  inferInstanceAs (MeasurableSpace (ℤ → (ℕ × (ℕ → unitInterval))))

def integerSpatialSampleMeasure (theta : ℝ) : Measure IntegerSpatialSample :=
  Measure.infinitePi (fun r : ℤ => markSampleMeasure (integerLevelRate theta r) unitIntervalUniformMeasure)

instance instProbabilityIntegerSpatialSample (theta : ℝ) :
    IsProbabilityMeasure (integerSpatialSampleMeasure theta) := by
  unfold integerSpatialSampleMeasure
  infer_instance

def integerPointRow (sample : IntegerSpatialSample) (r : ℤ) : Measure (ℝ × ℤ) :=
  ∑ i ∈ Finset.range ((sample r).1), Measure.dirac (1+((sample r).2 i : ℝ), r)

def integerPointMeasure (sample : IntegerSpatialSample) : Measure (ℝ × ℤ) :=
  Measure.sum (integerPointRow sample)

theorem measurable_stoppedDirac (r : ℤ) :
    Measurable (fun p : ℕ × (ℕ → unitInterval) =>
      ∑ i ∈ Finset.range p.1, Measure.dirac (1+(p.2 i : ℝ), r)) := by
  apply measurable_from_prod_countable_right
  intro n
  change Measurable (fun marks : ℕ → unitInterval =>
    ∑ i ∈ Finset.range n, Measure.dirac (1+(marks i : ℝ), r))
  apply Finset.measurable_sum
  intro i hi
  exact Measure.measurable_dirac.comp
    (((measurable_const.add (measurable_subtype_coe.comp (measurable_pi_apply i)))).prodMk measurable_const)

theorem measurable_integerPointRow (r : ℤ) :
    Measurable (fun sample : IntegerSpatialSample => integerPointRow sample r) :=
  (measurable_stoppedDirac r).comp (measurable_pi_apply r)

theorem measurable_integerPointMeasure : Measurable integerPointMeasure := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [integerPointMeasure, Measure.sum_apply _ hs]
  exact Measurable.tsum (fun r =>
    (Measure.measurable_coe hs).comp (measurable_integerPointRow r))

def integerPointLaw (theta : ℝ) : Measure (Measure (ℝ × ℤ)) :=
  (integerSpatialSampleMeasure theta).map integerPointMeasure

instance instProbabilityIntegerPointLaw (theta : ℝ) : IsProbabilityMeasure (integerPointLaw theta) :=
  Measure.isProbabilityMeasure_map measurable_integerPointMeasure.aemeasurable

theorem integerPointRow_level (sample : IntegerSpatialSample) (r k : ℤ) :
    integerPointRow sample r (Set.univ ×ˢ {k}) = if r = k then ((sample r).1 : ℝ≥0∞) else 0 := by
  classical
  by_cases hr : r = k <;>
    simp [integerPointRow, Measure.coe_finsetSum, Finset.sum_apply, hr,
      Measure.dirac_apply' _ (MeasurableSet.univ.prod (measurableSet_singleton k)), Set.indicator]

/-- The count at each complete spatial level is literally the sampled Poisson coordinate. -/
theorem integerPointMeasure_level (sample : IntegerSpatialSample) (r : ℤ) :
    integerPointMeasure sample (Set.univ ×ˢ {r}) = ((sample r).1 : ℝ≥0∞) := by
  classical
  rw [integerPointMeasure, Measure.sum_apply _ (MeasurableSet.univ.prod (measurableSet_singleton r))]
  simp_rw [integerPointRow_level]
  simp

instance instLocallyFiniteIntegerPointMeasure (sample : IntegerSpatialSample) :
    IsLocallyFiniteMeasure (integerPointMeasure sample) := by
  constructor
  intro p
  refine ⟨Set.univ ×ˢ {p.2}, ?_, ?_⟩
  · exact (isOpen_univ.prod (isOpen_discrete _)).mem_nhds (by simp)
  · rw [integerPointMeasure_level]
    exact ENNReal.natCast_lt_top _

theorem integerPointMeasure_compact_finite (sample : IntegerSpatialSample)
    (K : Set (ℝ × ℤ)) (hK : IsCompact K) : integerPointMeasure sample K < ⊤ :=
  hK.measure_lt_top

/-- Every point is genuinely supported in the stated unit spatial interval. -/
theorem integerPointMeasure_outside (sample : IntegerSpatialSample) :
    integerPointMeasure sample ((Set.Icc (1 : ℝ) 2 ×ˢ (Set.univ : Set ℤ))ᶜ) = 0 := by
  classical
  rw [integerPointMeasure, Measure.sum_apply _ ((measurableSet_Icc.prod MeasurableSet.univ).compl)]
  apply ENNReal.tsum_eq_zero.mpr
  intro r
  have hpos (i : ℕ) : 1 ≤ 1+((sample r).2 i : ℝ) ∧ 1+((sample r).2 i : ℝ) ≤ 2 := by
    constructor <;> linarith [((sample r).2 i).property.1, ((sample r).2 i).property.2]
  simp [integerPointRow, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.dirac_apply' _ ((measurableSet_Icc.prod MeasurableSet.univ).compl), hpos]

end
end PaperC.V282.D4ClosurePointMeasure
