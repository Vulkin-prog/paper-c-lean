import PaperCV282.UniformSpatialGrid
import PaperCV282.GeometricClusterTarget
import PaperCV282.SpatialMarkedPoissonIdentification
import PaperCV282.PoissonPointProcess
import PaperCV282.AllStartSoftPoisson

/-! # Independent continuous positions, geometric excesses and signs

The continuous position is exactly 1+U with U uniform on [0,1]. The mark
space retains every nonnegative excess and both signs. Its grid image has
the exact atom intensities of the spatial marked target.
-/
namespace PaperC.V282.SpatialDiffuseMarks

open MeasureTheory ProbabilityTheory UniformSpatialGrid GeometricClusterTarget
open SpatialMarkedTypes ExactMarkedModel ConditionalStartProbability
open scoped NNReal ENNReal Topology

noncomputable section

instance instTopologicalSign : TopologicalSpace F₂ := ⊥
instance instDiscreteTopologySign : DiscreteTopology F₂ := ⟨rfl⟩

def signMeasure : Measure F₂ := (PMF.uniformOfFintype F₂).toMeasure

instance instProbabilitySignMeasure : IsProbabilityMeasure signMeasure := by
  unfold signMeasure
  infer_instance

def spatialMarkMeasure : Measure (unitInterval × (ℕ × F₂)) :=
  unitIntervalUniformMeasure.prod ((geometricMeasure halfSuccess).prod signMeasure)

instance instProbabilitySpatialMark : IsProbabilityMeasure spatialMarkMeasure := by
  unfold spatialMarkMeasure
  infer_instance

def continuousMark (x : unitInterval × (ℕ × F₂)) : ℝ × (ℕ × F₂) :=
  (1 + (x.1 : ℝ), x.2)

theorem continuous_continuousMark : Continuous continuousMark := by
  exact (continuous_const.add (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd

theorem measurable_continuousMark : Measurable continuousMark :=
  continuous_continuousMark.measurable

theorem continuousMark_position_mem (x : unitInterval × (ℕ × F₂)) :
    (continuousMark x).1 ∈ Set.Icc (1 : ℝ) 2 := by
  obtain ⟨hlo,hhi⟩ := x.1.property
  change 1 ≤ 1 + (x.1 : ℝ) ∧ 1 + (x.1 : ℝ) ≤ 2
  constructor <;> linarith

def gridMark (N : ℕ) (hN : 0 < N) (x : unitInterval × (ℕ × F₂)) : SpatialMarkedIndex N :=
  (gridSite N hN x.1, x.2)

theorem measurable_gridMark (N : ℕ) (hN : 0 < N) : Measurable (gridMark N hN) :=
  ((measurable_gridSite N hN).comp measurable_fst).prodMk measurable_snd

theorem geometric_excess_real (e : ℕ) :
    (geometricMeasure halfSuccess).real {e} = 1 / (2 : ℝ) ^ (e + 1) := by
  rw [geometricMeasure_real_singleton halfSuccess_ne_zero]
  simp only [halfSuccess, Subtype.coe_mk]
  norm_num
  rw [pow_succ, div_pow]
  ring

theorem signMeasure_real_singleton (s : F₂) : signMeasure.real {s} = 1 / 2 := by
  rw [Measure.real]
  simp [signMeasure, PMF.uniformOfFintype_apply]

theorem gridMark_atom_probability (N : ℕ) (hN : 0 < N) (j : SpatialMarkedIndex N) :
    spatialMarkMeasure.real {x | gridMark N hN x = j} =
      (1 / (N : ℝ)) * (1 / (2 : ℝ) ^ (j.2.1 + 1)) * (1 / 2) := by
  have heq : {x | gridMark N hN x = j} =
      {u | gridSite N hN u = j.1} ×ˢ ({j.2.1} ×ˢ {j.2.2}) := by
    ext x
    simp [gridMark, Prod.ext_iff]
  rw [heq, spatialMarkMeasure, measureReal_prod_prod, measureReal_prod_prod,
    geometric_excess_real, signMeasure_real_singleton]
  have hcell : unitIntervalUniformMeasure.real {u | gridSite N hN u = j.1} = 1 / (N : ℝ) := by
    rw [Measure.real, grid_cell_probability, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    simp only [one_div]
  rw [hcell]
  ring

theorem gridMark_atom_rates (N L : ℕ) (hN : 0 < N) (j : SpatialMarkedIndex N) :
    AllStartSoftPoisson.fullRate N L *
      (spatialMarkMeasure {x | gridMark N hN x = j}).toNNReal = signedMarkRate L j.2.1 := by
  apply NNReal.coe_injective
  rw [NNReal.coe_mul]
  change (AllStartSoftPoisson.fullRate N L : ℝ) *
    spatialMarkMeasure.real {x | gridMark N hN x = j} = _
  rw [gridMark_atom_probability]
  change ((N : ℝ) / 2 ^ L) * ((1 / (N : ℝ)) * (1 / (2 : ℝ) ^ (j.2.1 + 1)) * (1 / 2)) =
    1 / (2 : ℝ) ^ (L + j.2.1 + 2)
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  rw [show L + j.2.1 + 2 = L + (j.2.1 + 1) + 1 by omega, pow_add, pow_succ]
  field_simp
  ring

theorem hasLaw_grid_configuration (N L : ℕ) (hN : 0 < N) :
    HasLaw (SpatialMarkedPoissonIdentification.sampledConfiguration N (gridMark N hN))
      (SpatialMarkedTarget.spatialTargetMeasure N L)
      (GeneralPoissonMarking.markSampleMeasure (AllStartSoftPoisson.fullRate N L)
        spatialMarkMeasure) :=
  SpatialMarkedPoissonIdentification.hasLaw_sampledConfiguration_of_atom_rates
    N L _ spatialMarkMeasure _ (measurable_gridMark N hN) (gridMark_atom_rates N L hN)

end
end PaperC.V282.SpatialDiffuseMarks
