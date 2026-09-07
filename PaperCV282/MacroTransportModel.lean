import PaperCV282.BulkMarkedComparison
import PaperCV282.BulkMarkedGeometry
import PaperCV282.MovingMarkedLevels
import PaperCV282.GrowingLevelParameters
import PaperCV282.PrimeEnvironmentStableLift

/-! # The exact base-contained macroscopic field

Every signed excess is kept at each start in [2,M-L+1]. Larger exact runs may
continue past M: no right censoring is introduced by this source definition.
-/
namespace PaperC.V282.MacroTransportModel

open MeasureTheory ProbabilityTheory InfiniteRademacher InfiniteCylinderTransfer BulkMarkedTypes
open BulkMarkedSource BulkMarkedTarget BulkMarkedComparison BulkMarkedGeometry
open FiniteStartMaskAverages SharpConditioning AllStartSoftPoisson ConditionedCountableLaw
open scoped BigOperators NNReal ENNReal

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- Starts whose base L-window is contained, excluding the separately treated border. -/
def containedStarts (M L : ℕ) : Finset ℕ := Finset.Icc 2 (M-L+1)

def source (M L : ℕ) : InfiniteSample → SpatialMarkedConfig (containedStarts M L) :=
  spatialMarkedSource (containedStarts M L) L

def targetMeasure (M L : ℕ) : Measure (SpatialMarkedConfig (containedStarts M L)) :=
  spatialTargetMeasure (containedStarts M L) L

instance instProbabilityTarget (M L : ℕ) : IsProbabilityMeasure (targetMeasure M L) := by
  unfold targetMeasure
  infer_instance

/-- Exact total target intensity; the arithmetic majorants may use M/2^L instead. -/
def containedRate (M L : ℕ) : ℝ≥0 := maskRate L (containedStarts M L)

def conditionalDistance (M L : ℕ) (A : Set InfiniteSample) : ℝ :=
  measureTotalVariation ((cond infiniteRademacherMeasure A).map (source M L)) (targetMeasure M L)

def distance (M L : ℕ) : ℝ :=
  measureTotalVariation (infiniteRademacherMeasure.map (source M L)) (targetMeasure M L)

theorem mem_containedStarts {M L x : ℕ} : x∈containedStarts M L ↔ 2≤x ∧ x≤M-L+1 := by
  simp [containedStarts]

theorem card_containedStarts (M L : ℕ) : (containedStarts M L).card=M-L := by
  simp [containedStarts, Nat.card_Icc]

theorem containedRate_coe (M L : ℕ) : (containedRate M L : ℝ)=((M-L : ℕ) : ℝ)/(2 : ℝ)^L := by
  change ((containedStarts M L).card : ℝ)/(2 : ℝ)^L=_
  rw [card_containedStarts]

theorem containedRate_le_fullRate (M L : ℕ) : containedRate M L≤fullRate M L := by
  apply NNReal.coe_le_coe.mp
  rw [containedRate_coe,fullRate_coe]
  exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.sub_le M L) (by positivity)

theorem containedStarts_subset_Icc {M L : ℕ} (hL : 1≤L) : containedStarts M L⊆Finset.Icc 2 M := by
  intro x hx
  obtain ⟨hl,hu⟩ := mem_containedStarts.mp hx
  exact Finset.mem_Icc.mpr ⟨hl,by omega⟩

theorem bulkStarts_subset_contained {M L : ℕ} {delta : ℝ} (hM : 2≤M) (hdelta : 0<delta) :
    bulkStarts M L delta⊆containedStarts M L := by
  intro x hx
  obtain ⟨hl,hu⟩ := (mem_bulkStarts M L x delta).mp hx
  exact mem_containedStarts.mpr ⟨(MacroscopicGeometry.two_le_macroscopic_lowerEndpoint hM hdelta).trans hl,hu⟩

theorem source_coordinate (M L : ℕ) (omega : InfiniteSample) (j : SpatialMarkedIndex (containedStarts M L)) :
    source M L omega j=ExactMarkedModel.signedMarkValue (infiniteValueBit omega) j.1.val L j.2.1 j.2.2 := rfl

theorem measurable_source (M L : ℕ) : Measurable (source M L) := measurable_spatialMarkedSource _ _

theorem conditionalDistance_nonneg (M L : ℕ) (A : Set InfiniteSample)
    (hpos : 0 < infiniteRademacherMeasure.real A) :
    0≤conditionalDistance M L A := by
  letI instProbabilityConditional : IsProbabilityMeasure (cond infiniteRademacherMeasure A) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hpos)
  letI instProbabilitySource : IsProbabilityMeasure ((cond infiniteRademacherMeasure A).map (source M L)) :=
    Measure.isProbabilityMeasure_map (measurable_source M L).aemeasurable
  exact measureTotalVariation_nonneg _ _

end
end PaperC.V282.MacroTransportModel
