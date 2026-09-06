import PaperCV282.SpatialMarkedTypes
import PaperCV282.RunFiniteness
import PaperCV282.ExactMarkedInfinite
import PaperCV282.ExactMarkedSourceTail

/-!
# The genuine spatial exact-mark source with all excesses and both signs

Each sample has at most one active exact mark at each of the N positions,
so the configuration has finite support pointwise. Run termination is used
only to identify its total count with the count of threshold starts.
-/
namespace PaperC.V282.SpatialMarkedSource

open MeasureTheory Set InfiniteRademacher InfiniteCylinderTransfer InfiniteStartProbabilityTransfer
open InfiniteExactLengthProbabilityTransfer ExactLengthDecomposition MixedLengthAffine
open ExactMarkedModel ExactMarkedInfinite SpatialMarkedTypes RunFiniteness
open MarkedDetruncation ExactMarkedSourceTail InfiniteMassCoupling ConditionalStartProbability
open FiniteFieldTotalVariation
open scoped BigOperators

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

local instance instIsProbabilityMeasureInfiniteRademacher :
    IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

noncomputable section

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- An exact run cannot have zero length, even if the requested base is zero. -/
theorem exact_mark_length_pos {g : ℕ → F₂} {x L e : ℕ}
    (h : ExactLengthEvent g x (excessRowCount L e)) : 0 < L+e := by
  by_contra hn
  have hz : L+e=0 := by omega
  have ht := h.2.2
  have heq : excessRowCount L e-1=0 := by simp [excessRowCount,hz]
  rw [heq,Nat.add_zero] at ht
  have hbits : ∀ a : F₂, a+a ≠ 1 := by decide
  exact hbits (g x) ht

/-- Uniqueness includes base length zero, allowing a literal source definition for every parameter. -/
theorem signed_exact_unique_all_lengths {g : ℕ → F₂} {x L e f : ℕ} {s t : F₂}
    (he : SignedExactMark g x L e s) (hf : SignedExactMark g x L f t) : e=f ∧ s=t := by
  refine ⟨?_,he.2.symm.trans hf.2⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hh := hf.1.2.1 (L+e) (exact_mark_length_pos he.1) (by simp only [excessRowCount];omega)
    have hn := (add_eq_one_iff_ne _ _).mp he.1.2.2
    exact hn (by simpa only [excessRowCount,Nat.add_sub_cancel] using hh)
  · have hh := he.1.2.1 (L+f) (exact_mark_length_pos hf.1) (by simp only [excessRowCount];omega)
    have hn := (add_eq_one_iff_ne _ _).mp hf.1.2.2
    exact hn (by simpa only [excessRowCount,Nat.add_sub_cancel] using hh)

def spatialMarkedValue (N L : ℕ) (omega : InfiniteSample) (j : SpatialMarkedIndex N) : ℕ :=
  signedMarkValue (infiniteValueBit omega) (N+j.1.val) L j.2.1 j.2.2

theorem spatialMarkedValue_ne_zero_iff (N L : ℕ) (omega : InfiniteSample) (j : SpatialMarkedIndex N) :
    spatialMarkedValue N L omega j ≠ 0 ↔
      SignedExactMark (infiniteValueBit omega) (N+j.1.val) L j.2.1 j.2.2 := by
  simp [spatialMarkedValue,signedMarkValue]

/-- At most one coefficient is active per site, without any probabilistic qualification. -/
theorem finite_support_spatialMarkedValue (N L : ℕ) (omega : InfiniteSample) :
    (Function.support (spatialMarkedValue N L omega)).Finite := by
  apply Set.Finite.of_finite_image (f := fun j : SpatialMarkedIndex N => j.1) (Set.toFinite _)
  intro a ha b hb hab
  have ha' := (spatialMarkedValue_ne_zero_iff N L omega a).mp ha
  have hb' := (spatialMarkedValue_ne_zero_iff N L omega b).mp hb
  change a.1=b.1 at hab
  rw [← hab] at hb'
  obtain ⟨he,hs⟩ := signed_exact_unique_all_lengths ha' hb'
  exact Prod.ext hab (Prod.ext he hs)

/-- The actual source configuration, with every excess and sign retained. -/
def spatialMarkedSource (N L : ℕ) (omega : InfiniteSample) : SpatialMarkedConfig N :=
  Finsupp.ofSupportFinite (spatialMarkedValue N L omega) (finite_support_spatialMarkedValue N L omega)

theorem spatialMarkedSource_apply (N L : ℕ) (omega : InfiniteSample) (j : SpatialMarkedIndex N) :
    spatialMarkedSource N L omega j=spatialMarkedValue N L omega j := rfl

theorem measurableSet_signed_exact (x L e : ℕ) (s : F₂) :
    MeasurableSet {omega : InfiniteSample | SignedExactMark (infiniteValueBit omega) x L e s} := by
  have he : {omega : InfiniteSample | SignedExactMark (infiniteValueBit omega) x L e s} =
      restrictToFinite (x+(L+e)) ⁻¹'
        {omega : SampleSpace (x+(L+e)) | SignedExactMark (valueBit omega) x L e s} := by
    ext omega
    exact (signedExactMark_restrictToFinite_iff (le_refl (x+(L+e))) s omega).symm
  rw [he]
  exact (measurable_restrictToFinite _) (Set.toFinite _ |>.measurableSet)

theorem measurable_spatialMarkedValue (N L : ℕ) (j : SpatialMarkedIndex N) :
    Measurable (fun omega : InfiniteSample => spatialMarkedValue N L omega j) := by
  exact measurable_const.ite (measurableSet_signed_exact _ _ _ _) measurable_const

/-- The complete finite-support configuration is measurable, despite unbounded possible excesses. -/
theorem measurable_spatialMarkedSource (N L : ℕ) : Measurable (spatialMarkedSource N L) := by
  apply measurable_to_countable'
  intro config
  have he : spatialMarkedSource N L ⁻¹' {config} =
      ⋂ j : SpatialMarkedIndex N, {omega | spatialMarkedValue N L omega j=config j} := by
    ext omega
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_iInter,Set.mem_setOf_eq]
    exact Finsupp.ext_iff
  rw [he]
  exact MeasurableSet.iInter (fun j =>
    (measurable_spatialMarkedValue N L j) (measurableSet_singleton _))

/-- Every finite projection is literally the previously validated full signed field. -/
theorem project_spatialMarkedSource (N L E : ℕ) (omega : InfiniteSample) :
    projectConfiguration N E (spatialMarkedSource N L omega)=
      infiniteSignedField N L E (dyadicBlock N) omega := by
  funext i
  have hx : N+((dyadicSiteEquiv N).symm i.1).val=i.1.val :=
    congrArg Subtype.val ((dyadicSiteEquiv N).apply_symm_apply i.1)
  simp only [projectConfiguration,spatialMarkedSource_apply,spatialMarkedValue,finiteMarkedEmbedding,
    Function.Embedding.coeFn_mk,hx,infiniteSignedField,i.1.property,true_and,signedMarkValue]

def spatialSourceLaw (N L : ℕ) : SpatialMarkedConfig N → ℝ :=
  observableLaw infiniteRademacherMeasure (spatialMarkedSource N L)

theorem hasSum_spatialSourceLaw (N L : ℕ) : HasSum (spatialSourceLaw N L) 1 :=
  hasSum_observableLaw _ (measurable_spatialMarkedSource N L)

theorem spatialSourceLaw_nonneg (N L : ℕ) (config : SpatialMarkedConfig N) :
    0 ≤ spatialSourceLaw N L config := observableLaw_nonneg _ _ _

/-- The genuine discarded-label event, on the same complete spatial source. -/
def spatialSourceTail (N L E : ℕ) : Set InfiniteSample :=
  {omega | ∃ j : SpatialMarkedIndex N, E<j.2.1 ∧ spatialMarkedSource N L omega j≠0}

theorem spatialSourceTail_eq_markTail (N L E : ℕ) :
    spatialSourceTail N L E=infiniteMarkTailEvent N L E := by
  ext omega
  constructor
  · rintro ⟨j,hE,hj⟩
    have hs := (spatialMarkedValue_ne_zero_iff N L omega j).mp hj
    exact ⟨N+j.1.val,(dyadicSiteEquiv N j.1).property,j.2.1,hE,hs.1⟩
  · rintro ⟨x,hx,e,hE,he⟩
    let j : SpatialMarkedIndex N := ((dyadicSiteEquiv N).symm ⟨x,hx⟩,(e,infiniteValueBit omega x))
    have hsite : N+j.1.val=x := congrArg Subtype.val ((dyadicSiteEquiv N).apply_symm_apply ⟨x,hx⟩)
    refine ⟨j,hE,?_⟩
    apply (spatialMarkedValue_ne_zero_iff N L omega j).mpr
    simpa only [hsite] using (show SignedExactMark (infiniteValueBit omega) x L e (infiniteValueBit omega x) from ⟨he,rfl⟩)

theorem measurableSet_spatialSourceTail (N L E : ℕ) : MeasurableSet (spatialSourceTail N L E) := by
  rw [spatialSourceTail_eq_markTail]
  exact measurableSet_infiniteMarkTailEvent _ _ _

theorem spatial_source_tail_subset_long_start (N L E : ℕ) :
    spatialSourceTail N L E ⊆ infiniteDyadicStartEvent N (L+E+1) := by
  rw [spatialSourceTail_eq_markTail]
  exact infiniteMarkTailEvent_subset_longStartEvent _ _ _

/-- Equation (5.16) for the actual spatial signed source, rather than a scalar surrogate. -/
theorem ae_spatial_source_tail_iff_long_start {N L E : ℕ} (hN : 2 ≤ N) :
    ∀ᵐ omega ∂infiniteRademacherMeasure,
      (omega∈spatialSourceTail N L E ↔ omega∈infiniteDyadicStartEvent N (L+E+1)) := by
  rw [spatialSourceTail_eq_markTail]
  exact ae_mem_infiniteMarkTailEvent_iff_longStartEvent hN

theorem spatialMarkedSource_eq_truncate_off_tail (N L E : ℕ) (omega : InfiniteSample)
    (h : omega ∉ spatialSourceTail N L E) :
    spatialMarkedSource N L omega=truncateConfiguration N E (spatialMarkedSource N L omega) := by
  symm
  apply (truncate_configuration_eq_self_iff _ _ _).mpr
  intro j hj
  by_contra hn
  exact h ⟨j,hj,hn⟩

/-- Complete source and finite projection embedded in the same spatial configuration space. -/
theorem spatial_source_truncation_tv_le (N L E : ℕ) :
    massTotalVariation (spatialSourceLaw N L)
      (observableLaw infiniteRademacherMeasure
        (fun omega => embedConfiguration N E (infiniteSignedField N L E (dyadicBlock N) omega))) ≤
      infiniteMarkTailProbability N L E := by
  have hf : (fun omega => embedConfiguration N E (infiniteSignedField N L E (dyadicBlock N) omega)) =
      fun omega => truncateConfiguration N E (spatialMarkedSource N L omega) := by
    funext omega
    rw [← project_spatialMarkedSource,embed_project_configuration]
  rw [hf]
  have h := massTotalVariation_observableLaw_le_event infiniteRademacherMeasure
    (measurable_spatialMarkedSource N L)
    ((measurable_of_countable (truncateConfiguration N E)).comp (measurable_spatialMarkedSource N L))
    (spatialMarkedSource_eq_truncate_off_tail N L E)
  simpa only [spatialSourceLaw,spatialSourceTail_eq_markTail,infiniteMarkTailProbability,Measure.real,
    Function.comp_def] using h

/-- On each terminating sample, the complete spatial configuration has exactly the start count. -/
theorem spatial_source_total_eq_startCount_of_tail_changes {N L : ℕ}
    (omega : InfiniteSample)
    (hchange : ∀ x∈dyadicBlock N, TailChangesAt (infiniteValueBit omega) x) :
    (spatialMarkedSource N L omega).sum (fun _ n => n)=infiniteDyadicStartCount N L omega := by
  classical
  let active : Finset (Fin N) := Finset.univ.filter (fun i =>
    StartEvent (infiniteValueBit omega) (N+i.val) L)
  have hcard : (spatialMarkedSource N L omega).support.card=active.card := by
    apply Finset.card_bij (fun j _ => j.1)
    · intro j hj
      have hm := (spatialMarkedValue_ne_zero_iff N L omega j).mp (Finsupp.mem_support_iff.mp hj)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,exactLengthEvent_start hm.1⟩
    · intro a ha b hb hab
      have ha' := (spatialMarkedValue_ne_zero_iff N L omega a).mp (Finsupp.mem_support_iff.mp ha)
      have hb' := (spatialMarkedValue_ne_zero_iff N L omega b).mp (Finsupp.mem_support_iff.mp hb)
      rw [← hab] at hb'
      obtain ⟨he,hs⟩ := signed_exact_unique_all_lengths ha' hb'
      exact Prod.ext hab (Prod.ext he hs)
    · intro i hi
      have hs := (Finset.mem_filter.mp hi).2
      obtain ⟨e,he⟩ := exists_exactLengthEvent_of_start_of_tailChangesAt hs
        (hchange _ (dyadicSiteEquiv N i).property)
      refine ⟨(i,(e,infiniteValueBit omega (N+i.val))),?_,rfl⟩
      apply Finsupp.mem_support_iff.mpr
      apply (spatialMarkedValue_ne_zero_iff N L omega _).mpr
      exact ⟨he,rfl⟩
  have htotal : (spatialMarkedSource N L omega).sum (fun _ n => n)=
      (spatialMarkedSource N L omega).support.card := by
    change (∑ j∈(spatialMarkedSource N L omega).support, spatialMarkedSource N L omega j)=_
    calc
      _ = ∑ _j∈(spatialMarkedSource N L omega).support, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hm := (spatialMarkedValue_ne_zero_iff N L omega j).mp (Finsupp.mem_support_iff.mp hj)
        simp only [spatialMarkedSource_apply,spatialMarkedValue,signedMarkValue,if_pos hm]
      _ = _ := by simp
  rw [htotal,hcard]
  have ha : active.card=∑ i : Fin N, baseStartValue (infiniteValueBit omega) (N+i.val) L := by
    simp only [active,Finset.card_eq_sum_ones,Finset.sum_filter,baseStartValue]
  rw [ha]
  calc
    _ = ∑ x : {x : ℕ // x∈dyadicBlock N}, baseStartValue (infiniteValueBit omega) x.val L :=
      (dyadicSiteEquiv N).sum_comp (fun x => baseStartValue (infiniteValueBit omega) x.val L)
    _ = _ := by
      exact (Finset.sum_subtype (dyadicBlock N) (fun _ => Iff.rfl)
        (fun x => baseStartValue (infiniteValueBit omega) x L)).symm

/-- The source-level identity (5.11) holds simultaneously across the whole finite spatial block. -/
theorem ae_spatial_source_total_eq_startCount {N L : ℕ} (hN : 2 ≤ N) :
    ∀ᵐ omega ∂infiniteRademacherMeasure,
      (spatialMarkedSource N L omega).sum (fun _ n => n)=infiniteDyadicStartCount N L omega := by
  filter_upwards [ae_all_runs_end] with omega homega
  apply spatial_source_total_eq_startCount_of_tail_changes omega
  intro x hx
  exact homega x (by have hh := Finset.mem_Ico.mp hx;omega)

end
end PaperC.V282.SpatialMarkedSource
