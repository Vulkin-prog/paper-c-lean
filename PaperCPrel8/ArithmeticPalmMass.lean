import PaperCPrel8.EnumeratedTargetAtoms
import PaperCPrel8.InfinitePalmDeletion
import PaperCPrel8.PalmVoidAverage

/-! # The Palm mass identity on the actual conditional arithmetic field

Regularity is an explicit private-prime predicate. Presence, the source mass,
the target mass and the Palm void all live on their original probability spaces.
-/
namespace PaperC.Prel8.ArithmeticPalmMass
open Finset MeasureTheory ProbabilityTheory InfiniteRademacher
open V282.BulkMarkedTypes V282.BulkMarkedSource V282.BulkMarkedTarget
open V282.CrossoverBulkAtoms V282.ExactMarkedModel V282.SharpConditioning
open ConditionalStartProbability MicroscopicConditionalSpatial RoughKernelRegularity
open InfinitePlantMass InfinitePlantPresence EnumeratedTargetAtoms
noncomputable section
local instance : MeasurableSpace F₂ := ⊤
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Presence prescribes every supported exact mark, with no absence constraint. -/
def presence (sites : Finset ℕ) (L : ℕ) (z : SpatialMarkedConfig sites) : Set InfiniteSample :=
  {w | ∀ a, z a≠0 → SignedExactMark (infiniteValueBit w) a.1.val L a.2.1 a.2.2}

/-- An enumerated private-prime plant, with all its finite-cylinder bounds explicit. -/
def RegularPlant (sites : Finset ℕ) (C L E Y : ℕ) (z : SpatialMarkedConfig sites) : Prop :=
  ∃ k, ∃ labels : Fin k → SpatialMarkedIndex sites,
    z=enumeratedConfiguration sites labels ∧
    (∀ i, 2≤(labels i).1.val) ∧ (∀ i, (labels i).2.1≤E) ∧
    (∀ i, (labels i).1.val-1+(L+E+1)≤C) ∧
    Regular (L+E+1) Y (fun i ↦ (labels i).1.val-1)

theorem measurableSet_presence (sites : Finset ℕ) (L : ℕ) (z : SpatialMarkedConfig sites) :
    MeasurableSet (presence sites L z) := by
  have he : presence sites L z=⋂ a, {w | z a≠0 →
      SignedExactMark (infiniteValueBit w) a.1.val L a.2.1 a.2.2} := by ext w; simp [presence]
  rw [he]
  apply MeasurableSet.iInter
  intro a
  by_cases h : z a=0
  · simp [h]
  · simp only [h,ne_eq,not_false_eq_true,true_implies]
    exact V282.SpatialMarkedSource.measurableSet_signed_exact _ _ _ _

theorem equality_subset_presence (sites : Finset ℕ) (L : ℕ) (z : SpatialMarkedConfig sites) :
    {w | spatialMarkedSource sites L w=z} ⊆ presence sites L z := by
  intro w hw a ha
  apply (spatialMarkedValue_ne_zero_iff sites L w a).mp
  change spatialMarkedSource sites L w a≠0
  rwa [hw]

theorem presence_enumerated {k : ℕ} (sites : Finset ℕ) (L : ℕ)
    (labels : Fin k → SpatialMarkedIndex sites) (hj : ∀ i, 2≤(labels i).1.val) :
    presence sites L (enumeratedConfiguration sites labels)=
      occurrence L (fun i ↦ (labels i).1.val-1) (fun i ↦ (labels i).2.1) (fun i ↦ (labels i).2.2) := by
  ext w
  constructor
  · intro hw i
    have hcoef : enumeratedConfiguration sites labels (labels i)≠0 := by
      apply Nat.ne_of_gt
      simp only [enumeratedConfiguration,Finsupp.finsetSum_apply]
      exact sum_pos' (fun _ _ ↦ Nat.zero_le _) ⟨i,mem_univ _,by simp⟩
    have hx := hw (labels i) hcoef
    have heq : (labels i).1.val-1+1=(labels i).1.val := by have := hj i; omega
    simpa only [heq] using hx
  · intro hw a ha
    have hex : ∃ i, labels i=a := by
      by_contra hn
      push_neg at hn
      apply ha
      simp [enumeratedConfiguration,Finsupp.finsetSum_apply,Finsupp.single_apply,hn]
    obtain ⟨i,rfl⟩ := hex
    have heq : (labels i).1.val-1+1=(labels i).1.val := by have := hj i; omega
    simpa only [heq] using hw i

/-- The actual Poisson mass is exp(-total rate) times actual arithmetic presence. -/
theorem target_presence {C L E Y : ℕ} (sites : Finset ℕ) (hL : 1≤L)
    (A : SmallSample C Y → Prop) (hA : 0 < infiniteRademacherMeasure.real (traceEvent C Y A))
    (z : SpatialMarkedConfig sites) (hz : RegularPlant sites C L E Y z) :
    (spatialTargetMeasure sites L).real {z}=Real.exp (-(totalRate sites L:ℝ))*
      (cond infiniteRademacherMeasure (traceEvent C Y A)).real (presence sites L z) := by
  obtain ⟨k,labels,rfl,hj,he,hC,hr⟩ := hz
  have hinj := regular_sites_injective _ hr
  have hs : Function.Injective (fun i ↦ (labels i).1) := by
    intro i j hij
    apply hinj
    exact congrArg (fun x : sites ↦ x.val-1) hij
  rw [enumerated_target_mass sites L labels hs,presence_enumerated sites L labels hj]
  rw [conditional_presence hL _ _ _ (fun i ↦ by have := hj i; omega) he hC hr A hA]

theorem presence_pos {C L E Y : ℕ} (sites : Finset ℕ) (hL : 1≤L)
    (A : SmallSample C Y → Prop) (hA : 0 < infiniteRademacherMeasure.real (traceEvent C Y A))
    (z : SpatialMarkedConfig sites) (hz : RegularPlant sites C L E Y z) :
    0 < (cond infiniteRademacherMeasure (traceEvent C Y A)).real (presence sites L z) := by
  obtain ⟨k,labels,rfl,hj,he,hC,hr⟩ := hz
  rw [presence_enumerated sites L labels hj,
    conditional_presence hL _ _ _ (fun i ↦ by have := hj i; omega) he hC hr A hA]
  apply prod_pos
  intro i hi
  change 0<1/(2:ℝ)^_
  positivity

/-- Exact mass identity with no configuration-mass premise. -/
theorem source_target_palm_mass {C L E Y : ℕ} (sites : Finset ℕ) (hL : 1≤L)
    (A : SmallSample C Y → Prop) (hA : 0 < infiniteRademacherMeasure.real (traceEvent C Y A))
    (z : SpatialMarkedConfig sites) (hz : RegularPlant sites C L E Y z) :
    (cond infiniteRademacherMeasure (traceEvent C Y A)).real {w | spatialMarkedSource sites L w=z} =
    (spatialTargetMeasure sites L).real {z} * (Real.exp (totalRate sites L:ℝ)*
      (cond (cond infiniteRademacherMeasure (traceEvent C Y A)) (presence sites L z)).real
        {w | spatialMarkedSource sites L w=z}) := by
  rw [target_presence sites hL A hA z hz,
    cond_real_apply _ _ (measurableSet_presence sites L z),
    Set.inter_eq_right.mpr (equality_subset_presence sites L z)]
  have hpos := presence_pos sites hL A hA z hz
  have he : Real.exp (-(totalRate sites L:ℝ))*Real.exp (totalRate sites L:ℝ)=1 := by
    rw [← Real.exp_add]; simp
  field_simp
  rw [mul_assoc,he,mul_one]

end
end PaperC.Prel8.ArithmeticPalmMass
