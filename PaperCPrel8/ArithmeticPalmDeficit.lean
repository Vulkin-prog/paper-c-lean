import PaperCPrel8.ArithmeticPalmMass
import PaperCPrel8.PalmDeficitProbability

/-! # Countable Palm deficit and deletion for the actual arithmetic field -/
namespace PaperC.Prel8.ArithmeticPalmDeficit
open MeasureTheory ProbabilityTheory InfiniteRademacher
open V282.BulkMarkedTypes V282.BulkMarkedSource V282.BulkMarkedTarget V282.CrossoverBulkAtoms
open V282.InfiniteMassCoupling V282.ConditionedCountableLaw V282.FiniteFieldTotalVariation
open ConditionalStartProbability MicroscopicConditionalSpatial ArithmeticPalmMass PalmDeficit
noncomputable section
local instance : MeasurableSpace F₂ := ⊤
local instance : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- The genuine source mass after the specified small-prime conditioning. -/
def sourceMass {C Y : ℕ} (sites : Finset ℕ) (L : ℕ) (A : SmallSample C Y → Prop) :=
  conditionalObservableLaw infiniteRademacherMeasure (traceEvent C Y A) (spatialMarkedSource sites L)

def targetMass (sites : Finset ℕ) (L : ℕ) (z : SpatialMarkedConfig sites) :=
  (spatialTargetMeasure sites L).real {z}

def palmVoid {C Y : ℕ} (sites : Finset ℕ) (L : ℕ) (A : SmallSample C Y → Prop)
    (z : SpatialMarkedConfig sites) :=
  (cond (cond infiniteRademacherMeasure (traceEvent C Y A)) (presence sites L z)).real
    {w | spatialMarkedSource sites L w=z}

def fullDeficit {C Y : ℕ} (sites : Finset ℕ) (L E : ℕ) (A : SmallSample C Y → Prop) :=
  PalmVoidAverage.voidDeficit (targetMass sites L) (RegularPlant sites C L E Y)
    (fun z ↦ Real.exp (totalRate sites L:ℝ)*palmVoid sites L A z)

theorem hasSum_sourceMass {C Y : ℕ} (sites : Finset ℕ) (L : ℕ)
    (A : SmallSample C Y → Prop) (hA : 0 < infiniteRademacherMeasure.real (traceEvent C Y A)) :
    HasSum (sourceMass sites L A) 1 :=
  hasSum_conditionalObservableLaw _ _ hA (measurable_spatialMarkedSource sites L)

theorem hasSum_targetMass (sites : Finset ℕ) (L : ℕ) : HasSum (targetMass sites L) 1 := by
  exact hasSum_observableLaw (spatialTargetMeasure sites L) measurable_id

/-- The complete G.4 full-target identity uses proved arithmetic masses. -/
theorem fullDeficit_eq {C L E Y : ℕ} (sites : Finset ℕ) (hL : 1≤L)
    (A : SmallSample C Y → Prop) (hA : 0 < infiniteRademacherMeasure.real (traceEvent C Y A)) :
    fullDeficit sites L E A=deficit (sourceMass sites L A) (targetMass sites L)
      (RegularPlant sites C L E Y) := by
  symm
  exact deficit_eq_void_average _ _ (fun _ ↦ ENNReal.toReal_nonneg)
    (fun z hz ↦ source_target_palm_mass sites hL A hA z hz)

/-- The error is only the target exceptional probability; no exp(rate) error is paid. -/
theorem fullDeficit_comparison {C L E Y : ℕ} (sites : Finset ℕ) (hL : 1≤L)
    (A : SmallSample C Y → Prop) (hA : 0 < infiniteRademacherMeasure.real (traceEvent C Y A)) :
    0 ≤ massTotalVariation (sourceMass sites L A) (targetMass sites L)-fullDeficit sites L E A ∧
    massTotalVariation (sourceMass sites L A) (targetMass sites L)-fullDeficit sites L E A ≤
      (spatialTargetMeasure sites L).real {z | ¬RegularPlant sites C L E Y z} := by
  rw [fullDeficit_eq sites hL A hA]
  have h := deficit_restriction (hasSum_sourceMass sites L A hA) (hasSum_targetMass sites L)
    (fun _ ↦ ENNReal.toReal_nonneg) (fun _ ↦ ENNReal.toReal_nonneg) (RegularPlant sites C L E Y)
  have he : exceptionalMass (targetMass sites L) (RegularPlant sites C L E Y)=
      (spatialTargetMeasure sites L).real {z | ¬RegularPlant sites C L E Y z} := by
    have hh := restricted_observableLaw_eq_event (spatialTargetMeasure sites L)
      measurable_id {z | ¬RegularPlant sites C L E Y z}
    simp only [Set.preimage_id] at hh
    rw [← hh]
    apply tsum_congr
    intro z
    by_cases hz : RegularPlant sites C L E Y z <;>
      simp [exceptionalMass,observableLaw,targetMass,hz]
  rwa [← he]

/-- Actual conditional ordinary deletion, after cancellation inside the target average. -/
theorem ordinary_deletion {C L E Y : ℕ} (sites : Finset ℕ) (hL : 1≤L)
    (A : SmallSample C Y → Prop) (hA : 0 < infiniteRademacherMeasure.real (traceEvent C Y A))
    (outside : Set InfiniteSample) (houtside : MeasurableSet outside) :
    (∑' z, if RegularPlant sites C L E Y z then targetMass sites L z*Real.exp (totalRate sites L:ℝ)*
      (palmVoid sites L A z-
        (cond (cond infiniteRademacherMeasure (traceEvent C Y A)) (presence sites L z)).real
          ({w | spatialMarkedSource sites L w=z} \ outside)) else 0) =
      (cond infiniteRademacherMeasure (traceEvent C Y A)).real
        ({w | RegularPlant sites C L E Y (spatialMarkedSource sites L w)} ∩ outside) :=
  InfinitePalmDeletion.weighted_deleted_average _ _ (measurable_spatialMarkedSource sites L)
    _ outside houtside (presence sites L) (measurableSet_presence sites L)
    (presence_pos sites hL A hA) (equality_subset_presence sites L) _ _
    (target_presence sites hL A hA)

/-- The arithmetic full-target deficit is bounded above by the genuine TV distance. -/
theorem fullDeficit_bounds {C L E Y : ℕ} (sites : Finset ℕ) (hL : 1≤L)
    (A : SmallSample C Y → Prop) (hA : 0 < infiniteRademacherMeasure.real (traceEvent C Y A)) :
    0 ≤ fullDeficit sites L E A ∧
      fullDeficit sites L E A ≤ massTotalVariation (sourceMass sites L A) (targetMass sites L) := by
  constructor
  · rw [fullDeficit_eq sites hL A hA]; exact deficit_nonneg _ _ _
  · linarith [(fullDeficit_comparison (E := E) sites hL A hA).1]

end
end PaperC.Prel8.ArithmeticPalmDeficit
