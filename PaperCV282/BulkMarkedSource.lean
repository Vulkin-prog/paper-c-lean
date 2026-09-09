import PaperCV282.BulkMarkedTypes
import PaperCV282.SpatialMarkedSource
import PaperCV282.BulkMarkedDeletion

/-! # The actual exact-position source with all signed excesses -/
namespace PaperC.V282.BulkMarkedSource

open MeasureTheory Set InfiniteRademacher InfiniteCylinderTransfer InfiniteStartProbabilityTransfer
open InfiniteExactLengthProbabilityTransfer ExactLengthDecomposition MixedLengthAffine
open ExactMarkedModel BulkMarkedInfinite BulkMarkedTypes RunFiniteness
open SpatialMarkedSource (signed_exact_unique_all_lengths measurableSet_signed_exact)
open MarkedDetruncation InfiniteMassCoupling ConditionalStartProbability
open FiniteFieldTotalVariation MaskedArithmeticGeometry WindowValues
open scoped BigOperators

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instIsProbabilityMeasureInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

noncomputable section
@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

def spatialMarkedValue (sites : Finset ℕ) (L : ℕ) (omega : InfiniteSample) (j : SpatialMarkedIndex sites) : ℕ :=
  signedMarkValue (infiniteValueBit omega) j.1.val L j.2.1 j.2.2

theorem spatialMarkedValue_ne_zero_iff (sites : Finset ℕ) (L : ℕ) (omega : InfiniteSample) (j : SpatialMarkedIndex sites) :
    spatialMarkedValue sites L omega j ≠ 0 ↔
      SignedExactMark (infiniteValueBit omega) j.1.val L j.2.1 j.2.2 := by
  simp [spatialMarkedValue,signedMarkValue]

/-- At most one coefficient is active per site, without any probabilistic qualification. -/
theorem finite_support_spatialMarkedValue (sites : Finset ℕ) (L : ℕ) (omega : InfiniteSample) :
    (Function.support (spatialMarkedValue sites L omega)).Finite := by
  apply Set.Finite.of_finite_image (f := fun j : SpatialMarkedIndex sites => j.1) (Set.toFinite _)
  intro a ha b hb hab
  have ha' := (spatialMarkedValue_ne_zero_iff sites L omega a).mp ha
  have hb' := (spatialMarkedValue_ne_zero_iff sites L omega b).mp hb
  change a.1=b.1 at hab
  rw [← hab] at hb'
  obtain ⟨he,hs⟩ := signed_exact_unique_all_lengths ha' hb'
  exact Prod.ext hab (Prod.ext he hs)

/-- The actual source configuration, with every excess and sign retained. -/
def spatialMarkedSource (sites : Finset ℕ) (L : ℕ) (omega : InfiniteSample) : SpatialMarkedConfig sites :=
  Finsupp.ofSupportFinite (spatialMarkedValue sites L omega) (finite_support_spatialMarkedValue sites L omega)

theorem spatialMarkedSource_apply (sites : Finset ℕ) (L : ℕ) (omega : InfiniteSample) (j : SpatialMarkedIndex sites) :
    spatialMarkedSource sites L omega j=spatialMarkedValue sites L omega j := rfl

theorem measurable_spatialMarkedValue (sites : Finset ℕ) (L : ℕ) (j : SpatialMarkedIndex sites) :
    Measurable (fun omega : InfiniteSample => spatialMarkedValue sites L omega j) := by
  exact measurable_const.ite (measurableSet_signed_exact _ _ _ _) measurable_const

/-- The complete finite-support configuration is measurable, despite unbounded possible excesses. -/
theorem measurable_spatialMarkedSource (sites : Finset ℕ) (L : ℕ) : Measurable (spatialMarkedSource sites L) := by
  apply measurable_to_countable'
  intro config
  have he : spatialMarkedSource sites L ⁻¹' {config} =
      ⋂ j : SpatialMarkedIndex sites, {omega | spatialMarkedValue sites L omega j=config j} := by
    ext omega
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_iInter,Set.mem_setOf_eq]
    exact Finsupp.ext_iff
  rw [he]
  exact MeasurableSet.iInter (fun j =>
    (measurable_spatialMarkedValue sites L j) (measurableSet_singleton _))

/-- Every finite projection is literally the previously validated full signed field. -/
theorem project_spatialMarkedSource (sites : Finset ℕ) (L E : ℕ) (omega : InfiniteSample) :
    projectConfiguration sites E (spatialMarkedSource sites L omega)=
      infiniteSignedField sites L E (sites) omega := by
  funext i
  change signedMarkValue (infiniteValueBit omega) i.1.val L i.2.1.val i.2.2 =
    infiniteSignedField sites L E sites omega i
  simp only [infiniteSignedField,i.1.property,true_and,signedMarkValue]

def spatialSourceLaw (sites : Finset ℕ) (L : ℕ) : SpatialMarkedConfig sites → ℝ :=
  observableLaw infiniteRademacherMeasure (spatialMarkedSource sites L)

theorem hasSum_spatialSourceLaw (sites : Finset ℕ) (L : ℕ) : HasSum (spatialSourceLaw sites L) 1 :=
  hasSum_observableLaw _ (measurable_spatialMarkedSource sites L)

theorem spatialSourceLaw_nonneg (sites : Finset ℕ) (L : ℕ) (config : SpatialMarkedConfig sites) :
    0 ≤ spatialSourceLaw sites L config := observableLaw_nonneg _ _ _

/-- The actual discarded coordinates on the full source configuration. -/
def spatialSourceTail (sites : Finset ℕ) (L E : ℕ) : Set InfiniteSample :=
  {omega | ∃ j : SpatialMarkedIndex sites, E<j.2.1 ∧ spatialMarkedSource sites L omega j≠0}

theorem measurableSet_spatialSourceTail (sites : Finset ℕ) (L E : ℕ) :
    MeasurableSet (spatialSourceTail sites L E) := by
  have he : spatialSourceTail sites L E =
      ⋃ j : SpatialMarkedIndex sites, {omega | E<j.2.1 ∧ spatialMarkedSource sites L omega j≠0} := by
    ext omega
    simp [spatialSourceTail]
  rw [he]
  apply MeasurableSet.iUnion
  intro j
  by_cases hj : E<j.2.1
  · simp only [hj,true_and,spatialMarkedSource_apply]
    convert ((measurable_spatialMarkedValue sites L j) (measurableSet_singleton 0)).compl using 1
    ext omega
    simp
  · simp only [hj,false_and,Set.setOf_false]
    exact MeasurableSet.empty

theorem spatial_source_tail_subset_long_start (sites : Finset ℕ) (L E : ℕ) :
    spatialSourceTail sites L E ⊆ ⋃ x∈sites, infiniteStartEvent x (L+E+1) := by
  rintro omega ⟨j,hE,hj⟩
  have hs := (spatialMarkedValue_ne_zero_iff sites L omega j).mp hj
  exact Set.mem_iUnion.mpr ⟨j.1.val,Set.mem_iUnion.mpr ⟨j.1.property,
    exactLengthEvent_start_longer_of_excess_gt hE hs.1⟩⟩

theorem spatial_source_tail_probability_le (sites : Finset ℕ) (L E : ℕ) :
    infiniteRademacherMeasure.real (spatialSourceTail sites L E) ≤
      ∑ x∈sites, infiniteStartProbability x (L+E+1) := by
  apply (measureReal_mono (spatial_source_tail_subset_long_start sites L E) (measure_ne_top _ _)).trans
  exact measureReal_biUnion_finset_le sites (fun x => infiniteStartEvent x (L+E+1))

/-- A finite full-defect envelope controls the entire actual source tail. -/
theorem spatial_source_tail_le_full_defects {sites : Finset ℕ} (L E : ℕ)
    (hsite : ∀x∈sites,2≤x) :
    infiniteRademacherMeasure.real (spatialSourceTail sites L E) ≤
      ((fullDefectMass (L+E+1) sites : ℝ)+sites.card)/(2 : ℝ)^(L+E+1) := by
  apply (spatial_source_tail_probability_le sites L E).trans
  calc
    _ ≤ ∑ x∈sites,
        (1+((2^(defectIndices (L+E+2) x (L+E+2)).card-1 : ℕ) : ℝ))/(2 : ℝ)^(L+E+1) := by
      apply Finset.sum_le_sum
      intro x hx
      have h := (PointwiseStartBounds.corollary_two_five_start_bounds (hsite x hx)
        (by omega : 0<L+E+1)).2
      have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤2)
        (Nat.sub_le (defectIndices (L+E+2) x (L+E+2)).card 1)
      apply h.trans
      apply div_le_div_of_nonneg_right _ (by positivity)
      rw [Nat.cast_sub Nat.one_le_two_pow]
      push_cast
      have he : L+E+1+1=L+E+2 := by omega
      simp only [he]
      linarith
    _ = _ := by
      rw [← Finset.sum_div,Finset.sum_add_distrib]
      simp [fullDefectMass,Nat.add_assoc]

theorem spatialMarkedSource_eq_truncate_off_tail (sites : Finset ℕ) (L E : ℕ)
    (omega : InfiniteSample) (h : omega ∉ spatialSourceTail sites L E) :
    spatialMarkedSource sites L omega=truncateConfiguration sites E (spatialMarkedSource sites L omega) := by
  symm
  apply (truncate_configuration_eq_self_iff _ _ _).mpr
  intro j hj
  by_contra hn
  exact h ⟨j,hj,hn⟩

end
end PaperC.V282.BulkMarkedSource
