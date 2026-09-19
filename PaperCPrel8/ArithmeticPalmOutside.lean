import PaperCPrel8.ArithmeticPalmAvoidance
import PaperCPrel8.ArithmeticPalmCompletion

/-! # The full arithmetic Palm void in the ordinary outside-start identity -/
namespace PaperC.Prel8.ArithmeticPalmOutside
open MeasureTheory ProbabilityTheory InfiniteRademacher
open V282.BulkMarkedTypes V282.BulkMarkedSource V282.BulkMarkedTarget V282.RunFiniteness
open V282.CrossoverBulkAtoms V282.MacroTransportRestriction
open V282.ConditionedCountableLaw V282.SharpConditioning
open ConditionalStartProbability MicroscopicConditionalSpatial IndependentScalarTail
open ArithmeticPalmMass ArithmeticPalmDeficit ArithmeticPalmNormalization
noncomputable section
local instance : MeasurableSpace F₂ := ⊤
local instance : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- With actual run termination, a full field equals the zero-extended retained
configuration exactly when its retained field agrees and no outside base start occurs. -/
theorem full_eq_iff {s t : Finset ℕ} (hst : s⊆t) {L : ℕ} (hL : 1≤L)
    (z : SpatialMarkedConfig s) (w : InfiniteSample)
    (hchange : ∀ x∈t, ExactLengthDecomposition.TailChangesAt (infiniteValueBit w) x) :
    spatialMarkedSource t L w=embedSites hst z ↔
      spatialMarkedSource s L w=z ∧ w∉hitEvent L (t\s) := by
  constructor
  · intro hf
    constructor
    · have hh := congrArg (restrictSites hst) hf
      simpa only [restrict_spatialMarkedSource,restrict_embed_sites] using hh
    · intro hw
      obtain ⟨x,hx,hs⟩ := (hitEvent_iff L (t\s) w).mp hw
      obtain ⟨a,ha,hu⟩ := (start_iff_unique_signed_exact hL (hchange x (Finset.mem_sdiff.mp hx).1)).mp hs
      let j : SpatialMarkedIndex t := (⟨x,(Finset.mem_sdiff.mp hx).1⟩,a)
      have hnon := (spatialMarkedValue_ne_zero_iff t L w j).mpr ha
      change spatialMarkedSource t L w j≠0 at hnon
      rw [hf,embedSites_apply_outside hst z j (Finset.mem_sdiff.mp hx).2] at hnon
      exact hnon rfl
  · rintro ⟨hz,ho⟩
    rw [← hz]
    symm
    apply source_eq_embedded_off_removed_starts hst L w
    intro x hx he
    exact ho ((hitEvent_iff L (t\s) w).mpr ⟨x,hx,he⟩)

/-- Both conditional measures preserve the almost-sure full-field equivalence. -/
theorem ae_full_eq_iff {C Y L : ℕ} {s t : Finset ℕ} (hst : s⊆t) (hL : 1≤L)
    (ht : ∀ x∈t, 2≤x) (A : SmallSample C Y → Prop) (z : SpatialMarkedConfig s) :
    ∀ᵐ w ∂cond (cond infiniteRademacherMeasure (traceEvent C Y A)) (presence s L z),
      spatialMarkedSource t L w=embedSites hst z ↔
        spatialMarkedSource s L w=z ∧ w∉hitEvent L (t\s) := by
  have hc : ∀ᵐ w ∂cond (cond infiniteRademacherMeasure (traceEvent C Y A)) (presence s L z),
      ∀ x : ℕ, 2≤x → ExactLengthDecomposition.TailChangesAt (infiniteValueBit w) x :=
    (cond_absolutelyContinuous.trans cond_absolutelyContinuous).ae_le ae_all_runs_end
  filter_upwards [hc] with w hw
  exact full_eq_iff hst hL z w (fun x hx ↦ hw x (ht x hx))

/-- This identifies v(z), not a surrogate event, in the paper's deletion formula. -/
theorem full_void_eq {C Y L : ℕ} {s t : Finset ℕ} (hst : s⊆t) (hL : 1≤L)
    (ht : ∀ x∈t, 2≤x) (A : SmallSample C Y → Prop) (z : SpatialMarkedConfig s) :
    (cond (cond infiniteRademacherMeasure (traceEvent C Y A)) (presence s L z)).real
      {w | spatialMarkedSource t L w=embedSites hst z}=
    (cond (cond infiniteRademacherMeasure (traceEvent C Y A)) (presence s L z)).real
      ({w | spatialMarkedSource s L w=z} \ hitEvent L (t\s)) := by
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [ae_full_eq_iff hst hL ht A z] with w hw
  exact propext hw

/-- G.4's exact averaged identity with the actual retained and full arithmetic Palm voids. -/
theorem ordinary_full_deletion {C Y L E K : ℕ} {s t : Finset ℕ} (hst : s⊆t) (hL : 1≤L)
    (ht : ∀ x∈t, 2≤x) (A : SmallSample C Y → Prop)
    (hA : 0 < infiniteRademacherMeasure.real (traceEvent C Y A)) :
    (∑' z, if boundedRegular s C L E Y K z then targetMass s L z*Real.exp (totalRate s L:ℝ)*
      (palmVoid s L A z-
        (cond (cond infiniteRademacherMeasure (traceEvent C Y A)) (presence s L z)).real
          {w | spatialMarkedSource t L w=embedSites hst z}) else 0)=
    (cond infiniteRademacherMeasure (traceEvent C Y A)).real
      ({w | boundedRegular s C L E Y K (spatialMarkedSource s L w)} ∩ hitEvent L (t\s)) := by
  simp_rw [full_void_eq hst hL ht A]
  exact InfinitePalmDeletion.weighted_deleted_average _ _ (measurable_spatialMarkedSource s L)
    _ _ (measurableSet_hitEvent _ _) (presence s L) (measurableSet_presence s L)
    (fun z hz ↦ presence_pos s hL A hA z hz.1) (equality_subset_presence s L) _ _
    (fun z hz ↦ target_presence s hL A hA z hz.1)

end
end PaperC.Prel8.ArithmeticPalmOutside
