import PaperCV282.MacroTransportStatistics
import PaperCV282.BulkMarkedTargetProjection

/-! # The literal macroscopic positions and moving signed levels

The map retains x/M, e-d and the sign. For M>0 it is injective on complete
finite configurations, so its actual conditional distance is exactly the
original one. The resulting laws remain genuine singleton masses.
-/
namespace PaperC.V282.MacroTransportCoordinates

open MeasureTheory ProbabilityTheory MacroTransportModel MacroTransportRestoration
open BulkMarkedTypes BulkMarkedSource BulkMarkedTarget BulkMarkedTargetProjection BulkMarkedTransfer
open MovingMarkedLevels GrowingLevelParameters InfiniteRademacher InfiniteCylinderTransfer
open InfiniteMassCoupling CountableLawTransfer ConditionedCountableLaw FiniteFieldTotalVariation
open MassPushforward ExactMarkedModel BulkSupportGraph
open scoped BigOperators NNReal ENNReal

noncomputable section
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

@[reducible]
def PositionedConfiguration := (ℝ × (ℤ × F₂)) →₀ ℕ

instance instMeasurablePositionedConfiguration : MeasurableSpace PositionedConfiguration := ⊤
instance instSingletonPositionedConfiguration : MeasurableSingletonClass PositionedConfiguration := by infer_instance

def positionLevelMap (M L d : ℕ) (j : SpatialMarkedIndex (containedStarts M L)) : ℝ × (ℤ × F₂) :=
  ((j.1.val : ℝ)/M,((j.2.1 : ℤ)-d,j.2.2))

def positionedConfiguration (M L d : ℕ) (c : SpatialMarkedConfig (containedStarts M L)) : PositionedConfiguration :=
  c.mapDomain (positionLevelMap M L d)

theorem positionLevelMap_injective {M : ℕ} (hM : 1≤M) (L d : ℕ) :
    Function.Injective (positionLevelMap M L d) := by
  intro i j he
  have hn : (M : ℝ)≠0 := by exact_mod_cast (show M≠0 by omega)
  have hx := congrArg (fun z : ℝ × (ℤ × F₂) => z.1) he
  have hi : (i.1.val : ℝ)=(j.1.val : ℝ) := (div_left_inj' hn).mp hx
  have hs := congrArg (fun z : ℝ × (ℤ × F₂) => z.2.2) he
  have hl := congrArg (fun z : ℝ × (ℤ × F₂) => z.2.1) he
  have heq : i.2.1=j.2.1 := by
    change (i.2.1 : ℤ)-d=(j.2.1 : ℤ)-d at hl
    omega
  exact Prod.ext (Subtype.ext (by exact_mod_cast hi)) (Prod.ext heq hs)

theorem positionedConfiguration_injective {M : ℕ} (hM : 1≤M) (L d : ℕ) :
    Function.Injective (positionedConfiguration M L d) :=
  Finsupp.mapDomain_injective (positionLevelMap_injective hM L d)

theorem positionedConfiguration_apply {M : ℕ} (hM : 1≤M) (L d : ℕ)
    (c : SpatialMarkedConfig (containedStarts M L)) (j : SpatialMarkedIndex (containedStarts M L)) :
    positionedConfiguration M L d c (positionLevelMap M L d j)=c j :=
  Finsupp.mapDomain_apply (positionLevelMap_injective hM L d) _ _

def positionedSource (M d : ℕ) : InfiniteSample → PositionedConfiguration :=
  positionedConfiguration M (movingLength M d) d ∘ source M (movingLength M d)

def positionedTargetMeasure (M d : ℕ) : Measure PositionedConfiguration :=
  (targetMeasure M (movingLength M d)).map (positionedConfiguration M (movingLength M d) d)

instance instProbabilityPositionedTarget (M d : ℕ) : IsProbabilityMeasure (positionedTargetMeasure M d) := by
  unfold positionedTargetMeasure
  exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

theorem measurable_positionedSource (M d : ℕ) : Measurable (positionedSource M d) :=
  (measurable_of_countable _).comp (measurable_source _ _)

def positionedDistance (M d : ℕ) (A : Set InfiniteSample) : ℝ :=
  massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure A (positionedSource M d))
    (observableLaw (positionedTargetMeasure M d) id)

/-- The physical coordinate at a true site is exactly the signed exact-mark indicator. -/
theorem positionedSource_apply {M : ℕ} (hM : 1≤M) (d : ℕ) (omega : InfiniteSample)
    (j : SpatialMarkedIndex (containedStarts M (movingLength M d))) :
    positionedSource M d omega ((j.1.val : ℝ)/M,((j.2.1 : ℤ)-d,j.2.2))=
      signedMarkValue (infiniteValueBit omega) j.1.val (movingLength M d) j.2.1 j.2.2 :=
  positionedConfiguration_apply hM _ _ _ j

/-- Actual physical lengths are b+r, without truncating subtraction. -/
theorem positioned_run_length {M d : ℕ} (hd : d≤criticalBase M) (e : ℕ) :
    ((movingLength M d+e : ℕ) : ℤ)=(criticalBase M : ℤ)+((e : ℤ)-d) := by
  exact runLength_eq (criticalBase M) d e hd

/-- Each target spatial/excess/sign coordinate has the correct Poisson marginal. -/
theorem target_coordinate_hasLaw (sites : Finset ℕ) (L : ℕ) (j : SpatialMarkedIndex sites) :
    HasLaw (fun c : SpatialMarkedConfig sites => c j) (poissonMeasure (signedMarkRate L j.2.1))
      (spatialTargetMeasure sites L) := by
  let E := j.2.1
  let i : LabelledIndex sites (Fin (E+1) × F₂) := (j.1,(⟨j.2.1,by dsimp [E];omega⟩,j.2.2))
  have h := (PoissonFieldMeasure.hasLaw_coordinate (allSignedRates sites L E sites) i).fun_comp
    (hasLaw_projectConfiguration sites L E)
  have hr : allSignedRates sites L E sites i=signedMarkRate L j.2.1 := by
    simp [allSignedRates,i,j.1.property]
  rw [hr] at h
  exact h

/-- The signed lattice mean is 2^(-b-r-2), half the unsigned mean printed in 7.6. -/
theorem positioned_signed_mean {M d : ℕ} (hd : d≤criticalBase M) (e : ℕ) :
    (signedMarkRate (movingLength M d) e : ℝ)=
      (2 : ℝ)^(-(criticalBase M : ℝ)-((e : ℤ)-d : ℤ)-2) := by
  simpa only [signedMarkRate_coe,levelEquiv_val] using signed_site_mean hd e

/-- The total target mean uses the number of base-contained starts exactly. -/
theorem positioned_total_rate (M d : ℕ) :
    (containedRate M (movingLength M d) : ℝ)=
      ((M-movingLength M d : ℕ) : ℝ)/(2 : ℝ)^(movingLength M d) := containedRate_coe _ _

/-- Naming actual positions and levels loses no total variation at positive events. -/
theorem positionedDistance_eq {M : ℕ} (hM : 1≤M) (d : ℕ) (A : Set InfiniteSample)
    (hpos : 0 < infiniteRademacherMeasure.real A) :
    positionedDistance M d A=conditionalDistance M (movingLength M d) A := by
  letI instProbabilityConditional : IsProbabilityMeasure (cond infiniteRademacherMeasure A) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hpos)
  have htarget : observableLaw (positionedTargetMeasure M d) id=
      observableLaw (targetMeasure M (movingLength M d)) (positionedConfiguration M (movingLength M d) d) := by
    funext a
    exact (observableLaw_eq_map _ (measurable_of_countable _) a).symm
  unfold positionedDistance positionedSource conditionalObservableLaw
  rw [htarget,← pushforwardMass_observableLaw _ (measurable_source _ _)]
  have hp := pushforwardMass_observableLaw (targetMeasure M (movingLength M d)) measurable_id
    (positionedConfiguration M (movingLength M d) d)
  change pushforwardMass _ (observableLaw _ id)=observableLaw _ (positionedConfiguration M (movingLength M d) d) at hp
  rw [← hp]
  rw [massTotalVariation_injective _ (positionedConfiguration_injective hM _ _)]
  exact (map_distance_eq_mass _ _ (measurable_source _ _)).symm


/-- The coordinate source law has total mass one, even in its uncountable ambient position space. -/
theorem hasSum_positioned_conditionalLaw (M d : ℕ) (A : Set InfiniteSample)
    (hpos : 0 < infiniteRademacherMeasure.real A) :
    HasSum (conditionalObservableLaw infiniteRademacherMeasure A (positionedSource M d)) 1 := by
  letI instProbabilityConditional : IsProbabilityMeasure (cond infiniteRademacherMeasure A) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hpos)
  have h := hasSum_pushforwardMass (positionedConfiguration M (movingLength M d) d)
    (hasSum_observableLaw (cond infiniteRademacherMeasure A) (measurable_source _ _))
  rw [pushforwardMass_observableLaw _ (measurable_source _ _)] at h
  exact h

theorem hasSum_positioned_targetLaw (M d : ℕ) :
    HasSum (observableLaw (positionedTargetMeasure M d) id) 1 := by
  have h := hasSum_pushforwardMass (positionedConfiguration M (movingLength M d) d)
    (hasSum_observableLaw (targetMeasure M (movingLength M d)) measurable_id)
  have he : observableLaw (positionedTargetMeasure M d) id=
      pushforwardMass (positionedConfiguration M (movingLength M d) d)
        (observableLaw (targetMeasure M (movingLength M d)) id) := by
    rw [pushforwardMass_observableLaw _ measurable_id]
    funext a
    exact (observableLaw_eq_map _ (measurable_of_countable _) a).symm
  rw [he]
  exact h

/-- Every displayed coordinate lies in the actual unit prefix and retained level half-line. -/
theorem positionLevelMap_domain {M L d : ℕ} (hM : 1≤M) (hL : 1≤L)
    (j : SpatialMarkedIndex (containedStarts M L)) :
    0<(positionLevelMap M L d j).1 ∧ (positionLevelMap M L d j).1≤1 ∧
      -(d : ℤ)≤(positionLevelMap M L d j).2.1 := by
  have hx := Finset.mem_Icc.mp (containedStarts_subset_Icc hL j.1.property)
  have hMp : (0 : ℝ)<M := by exact_mod_cast (show 0<M by omega)
  refine ⟨div_pos (by exact_mod_cast (show 0<j.1.val by omega)) hMp,?_,?_⟩
  · exact (div_le_one hMp).mpr (by exact_mod_cast hx.2)
  · dsimp [positionLevelMap]
    omega

end
end PaperC.V282.MacroTransportCoordinates
