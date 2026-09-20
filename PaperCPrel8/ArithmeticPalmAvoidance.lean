import PaperCPrel8.ArithmeticPalmDeficit

/-! # Exact Palm voids are absence of all additional base starts -/
namespace PaperC.Prel8.ArithmeticPalmAvoidance
open Finset MeasureTheory ProbabilityTheory InfiniteRademacher
open V282.BulkMarkedTypes V282.BulkMarkedSource V282.ExactMarkedModel V282.RunFiniteness
open V282.SpatialMarkedSource (signed_exact_unique_all_lengths)
open ExactLengthDecomposition MixedLengthAffine
open InfinitePlantMass ArithmeticPalmMass ArithmeticPalmDeficit
noncomputable section
local instance : MeasurableSpace F₂ := ⊤
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

variable {k : ℕ} {sites : Finset ℕ}

/-- A coefficient in the enumerated plant is nonzero exactly at one of its labels. -/
theorem enumerated_ne_zero (labels : Fin k → SpatialMarkedIndex sites) (a : SpatialMarkedIndex sites) :
    enumeratedConfiguration sites labels a≠0 ↔ ∃ i, labels i=a := by
  constructor
  · intro ha
    by_contra hn
    push Not at hn
    apply ha
    simp [enumeratedConfiguration,Finsupp.finsetSum_apply,hn]
  · rintro ⟨i,rfl⟩
    apply Nat.ne_of_gt
    simp only [enumeratedConfiguration,Finsupp.finsetSum_apply]
    exact sum_pos' (fun _ _ ↦ Nat.zero_le _) ⟨i,mem_univ _,by simp⟩

theorem enumerated_at (labels : Fin k → SpatialMarkedIndex sites)
    (hinj : Function.Injective labels) (i : Fin k) :
    enumeratedConfiguration sites labels (labels i)=1 := by
  simp only [enumeratedConfiguration,Finsupp.finsetSum_apply]
  rw [sum_eq_single i]
  · simp
  · intro j hj hji
    exact Finsupp.single_eq_of_ne (fun h ↦ hji (hinj h.symm))
  · simp

/-- Remaining sites exclude whole planted sites, not just the prescribed excess. -/
def avoidance (L : ℕ) (labels : Fin k → SpatialMarkedIndex sites) : Set InfiniteSample :=
  {w | ∀ x : sites, (∀ i, (labels i).1≠x) → ¬StartEvent (infiniteValueBit w) x.val L}

/-- Deterministic equivalence, with the necessary run-termination hypothesis explicit. -/
theorem equality_iff_avoidance (L : ℕ) (hL : 1≤L)
    (labels : Fin k → SpatialMarkedIndex sites)
    (hinj : Function.Injective (fun i ↦ (labels i).1)) (w : InfiniteSample)
    (hchange : ∀ x : sites, TailChangesAt (infiniteValueBit w) x.val)
    (hp : w∈presence sites L (enumeratedConfiguration sites labels)) :
    spatialMarkedSource sites L w=enumeratedConfiguration sites labels ↔ w∈avoidance L labels := by
  have hlabels : Function.Injective labels := fun i j h ↦ hinj (congrArg Prod.fst h)
  constructor
  · intro heq x hx hs
    obtain ⟨a,ha,hu⟩ := (start_iff_unique_signed_exact hL (hchange x)).mp hs
    have hv := (spatialMarkedValue_ne_zero_iff sites L w (x,a)).mpr ha
    change spatialMarkedSource sites L w (x,a)≠0 at hv
    rw [heq] at hv
    obtain ⟨i,hi⟩ := (enumerated_ne_zero labels (x,a)).mp hv
    exact hx i (congrArg Prod.fst hi)
  · intro hav
    ext a
    by_cases ha : ∃ i, labels i=a
    · obtain ⟨i,rfl⟩ := ha
      rw [enumerated_at labels hlabels]
      have hpresent := hp (labels i) ((enumerated_ne_zero labels _).mpr ⟨i,rfl⟩)
      simp [spatialMarkedSource_apply,spatialMarkedValue,signedMarkValue,hpresent]
    · have hz := not_iff_not.mpr (enumerated_ne_zero labels a) |>.mpr ha
      simp only [ne_eq,not_not] at hz
      rw [hz]
      by_contra hn
      have hmark := (spatialMarkedValue_ne_zero_iff sites L w a).mp hn
      by_cases hs : ∃ i, (labels i).1=a.1
      · obtain ⟨i,hi⟩ := hs
        have hm := hp (labels i) ((enumerated_ne_zero labels _).mpr ⟨i,rfl⟩)
        rw [hi] at hm
        obtain ⟨he,ht⟩ := signed_exact_unique_all_lengths hm hmark
        exact ha ⟨i,Prod.ext hi (Prod.ext he ht)⟩
      · push Not at hs
        exact hav a.1 hs (exactLengthEvent_start hmark.1)

/-- Conditioning on the environment and on the plant preserves almost-sure termination. -/
theorem ae_palm_equality_iff {C Y : ℕ} (L : ℕ) (hL : 1≤L)
    (labels : Fin k → SpatialMarkedIndex sites)
    (hinj : Function.Injective (fun i ↦ (labels i).1)) (hsites : ∀ x∈sites, 2≤x)
    (A : ConditionalStartProbability.SmallSample C Y → Prop) :
    ∀ᵐ w ∂cond (cond infiniteRademacherMeasure (MicroscopicConditionalSpatial.traceEvent C Y A))
      (presence sites L (enumeratedConfiguration sites labels)),
      spatialMarkedSource sites L w=enumeratedConfiguration sites labels ↔ w∈avoidance L labels := by
  have hc : ∀ᵐ w ∂cond (cond infiniteRademacherMeasure (MicroscopicConditionalSpatial.traceEvent C Y A))
      (presence sites L (enumeratedConfiguration sites labels)),
      ∀ x : ℕ, 2≤x → TailChangesAt (infiniteValueBit w) x :=
    (cond_absolutelyContinuous.trans cond_absolutelyContinuous).ae_le ae_all_runs_end
  filter_upwards [hc,ae_cond_mem (measurableSet_presence sites L (enumeratedConfiguration sites labels))]
    with w hw hp
  exact equality_iff_avoidance L hL labels hinj w (fun x ↦ hw x.val (hsites x.val x.property)) hp

/-- The actual Palm void is the probability of the remaining base indicators all being zero. -/
theorem palmVoid_eq_avoidance {C Y : ℕ} (L : ℕ) (hL : 1≤L)
    (labels : Fin k → SpatialMarkedIndex sites)
    (hinj : Function.Injective (fun i ↦ (labels i).1)) (hsites : ∀ x∈sites, 2≤x)
    (A : ConditionalStartProbability.SmallSample C Y → Prop) :
    palmVoid sites L A (enumeratedConfiguration sites labels)=
      (cond (cond infiniteRademacherMeasure (MicroscopicConditionalSpatial.traceEvent C Y A))
        (presence sites L (enumeratedConfiguration sites labels))).real (avoidance L labels) := by
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [ae_palm_equality_iff L hL labels hinj hsites A] with w hw
  exact propext hw

end
end PaperC.Prel8.ArithmeticPalmAvoidance
