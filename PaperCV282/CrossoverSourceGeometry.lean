import PaperCV282.CrossoverMarkedCandidate
import PaperCV282.RarePrefixEvents
import PaperCV282.RarePrefixPoisson

/-! # The actual least departure and the border-or-one-point source observable -/
namespace PaperC.V282.CrossoverSourceGeometry

open MeasureTheory Set InfiniteRademacher InfiniteStartProbabilityTransfer
open CrossoverMarkedModel CrossoverMarkedCandidate CrossoverBulkAtoms CrossoverBulkOnePoint
open CrossoverPrimeClockStable BulkMarkedTypes BulkMarkedSource BulkMarkedAggregation BulkMarkedGeometry
open RarePrefixGeometry RarePrefixEvents MicroscopicBorderEvents MicroscopicNonvacancy ExactMarkedModel

noncomputable section
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

/-- Positivity of the total number is equivalent to a genuinely nonempty configuration. -/
theorem totalSize_eq_zero_iff (sites : Finset ℕ) (c : SpatialMarkedConfig sites) :
    totalSize sites c=0 ↔ c=0 := by
  constructor
  · intro h
    ext j
    have hj : c j ≤ totalSize sites c := by
      by_cases hm : j∈c.support
      · exact Finset.single_le_sum (fun i hi => Nat.zero_le _) hm
      · simp only [Finsupp.mem_support_iff,ne_eq,not_not] at hm
        rw [hm]
        exact Nat.zero_le _
    simp only [Finsupp.zero_apply]
    omega
  · rintro rfl
    simp [totalSize]

theorem siteCounts_single (sites : Finset ℕ) (j : SpatialMarkedIndex sites) (x : sites) :
    siteCounts sites (Finsupp.single j 1) x = if j.1=x then 1 else 0 := by
  simp [siteCounts]

theorem contained_start_mem_bulk_of_no_exceptions {M L x : ℕ} {delta : ℝ} {omega : InfiniteSample}
    (hx : x∈containedStarts M L omega) (hb : omega∉borderEvent L)
    (hi : omega∉interiorEvent L) (hm : omega∉middleEvent M L delta) :
    x∈bulkStarts M L delta ∧ omega∈infiniteStartEvent x L := by
  obtain ⟨hx1,hxu,_,he⟩ := (mem_containedStarts M L x omega).mp hx
  have hne : x≠1 := by intro h; subst x; exact hb (by simpa [siteStartEvent] using he)
  have hx2 : 2≤x := by omega
  have hs : omega∈infiniteStartEvent x L := by simpa [siteStartEvent,hne,hx2] using he
  have hxlo : 2*L^2<x := by
    by_contra hn
    exact hi (mem_iUnion.mpr ⟨x,mem_iUnion.mpr ⟨Finset.mem_Icc.mpr ⟨hx2,by omega⟩,hs⟩⟩)
  have hmacro : (M : ℝ)^delta≤x := by
    by_contra hn
    exact hm ⟨x,hxlo,by linarith,hs⟩
  exact ⟨(mem_bulkStarts_iff_real M L x delta).mpr ⟨hmacro,hxu⟩,hs⟩

theorem source_single_start {sites : Finset ℕ} {L : ℕ} {omega : InfiniteSample}
    (j : SpatialMarkedIndex sites)
    (heq : siteCounts sites (spatialMarkedSource sites L omega)=startField sites L omega)
    (hc : spatialMarkedSource sites L omega=Finsupp.single j 1) :
    omega∈infiniteStartEvent j.1.val L := by
  have hh := congrFun heq j.1
  rw [hc,siteCounts_single,if_pos rfl] at hh
  by_contra hs
  have hz : startField sites L omega j.1=0 := by
    simp only [startField,baseStartValue]
    exact if_neg hs
  omega

theorem firstStart_eq_of_source_single {M L : ℕ} {delta : ℝ} {omega : InfiniteSample}
    (hM : 2≤M) (hL : 1≤L) (hLM : L≤M) (hdelta : 0<delta)
    (j : SpatialMarkedIndex (bulkStarts M L delta))
    (heq : siteCounts _ (spatialMarkedSource (bulkStarts M L delta) L omega)=startField _ L omega)
    (hc : spatialMarkedSource (bulkStarts M L delta) L omega=Finsupp.single j 1)
    (hb : omega∉borderEvent L) (hi : omega∉interiorEvent L) (hm : omega∉middleEvent M L delta) :
    firstStart M L omega=j.1.val := by
  have hj2 : 2≤j.1.val := (Finset.mem_Icc.mp (bulkStarts_subset_Icc hM hL hdelta j.1.property)).1
  have hjstart := source_single_start j heq hc
  have hjmem : j.1.val∈containedStarts M L omega := (mem_containedStarts M L j.1.val omega).mpr
    ⟨by omega,((mem_bulkStarts M L j.1.val delta).mp j.1.property).2,hLM,
      by simpa [siteStartEvent,show j.1.val≠1 by omega,hj2] using hjstart⟩
  have hhit := (containedStarts_nonempty_iff M L omega).mp ⟨j.1.val,hjmem⟩
  obtain ⟨hfirst,hstart⟩ := contained_start_mem_bulk_of_no_exceptions (firstStart_mem hhit) hb hi hm
  let x : bulkStarts M L delta := ⟨firstStart M L omega,hfirst⟩
  have hx : startField (bulkStarts M L delta) L omega x=1 := by
    simp only [startField,baseStartValue]
    exact if_pos hstart
  have hh := congrFun heq x
  rw [hc,siteCounts_single,hx] at hh
  have he : j.1=x := by by_contra hn; simp [hn] at hh
  exact (congrArg Subtype.val he).symm

/-- Border-or-bulk non-vacancy agrees with the true contained hit off the two spatial exceptions. -/
theorem hit_iff_rareEvent {M L K : ℕ} {delta : ℝ} {omega : InfiniteSample}
    (hM : 2≤M) (hL : 1≤L) (hLM : L≤M) (hdelta : 0<delta)
    (heq : siteCounts _ (spatialMarkedSource (bulkStarts M L delta) L omega)=startField _ L omega)
    (hi : omega∉interiorEvent L) (hm : omega∉middleEvent M L delta) :
    omega∈hitEvent M L ↔
      (actualClockRecord L K omega,spatialMarkedSource (bulkStarts M L delta) L omega)∈rareEvent _ := by
  have hz : spatialMarkedSource (bulkStarts M L delta) L omega=0 ↔
      omega∉bulkHitEvent M L delta := by
    constructor
    · intro hc hb
      obtain ⟨x,hx,hs⟩ := by simpa only [bulkHitEvent,mem_iUnion] using hb
      have hh := congrFun heq ⟨x,hx⟩
      have hv : startField (bulkStarts M L delta) L omega ⟨x,hx⟩=1 := by
        simp only [startField,baseStartValue]; exact if_pos hs
      simp [hc,siteCounts,hv] at hh
    · intro hn
      ext j
      by_contra hj
      have hs := (spatialMarkedValue_ne_zero_iff _ _ _ j).mp hj
      have hstart := ExactLengthDecomposition.exactLengthEvent_start hs.1
      exact hn (mem_iUnion.mpr ⟨j.1.val,mem_iUnion.mpr ⟨j.1.property,hstart⟩⟩)
  have hh : omega∈hitEvent M L ↔ omega∈borderEvent L ∪ bulkHitEvent M L delta := by
    constructor
    · intro h
      rcases hit_subset_border_bulk_middle hLM h with hh | hh
      · exact hh
      · exact (hh.elim hi hm).elim
    · intro hx
      exact border_union_bulk_subset_hit hM hL hLM hdelta hx
  rw [hh]
  have hzero : totalSize (bulkStarts M L delta) (spatialMarkedSource _ L omega)=0 ↔
      omega∉bulkHitEvent M L delta := (totalSize_eq_zero_iff _ _).trans hz
  simp only [rareEvent,actualClockRecord,mem_setOf_eq,mem_union]
  by_cases hb : omega∈borderEvent L <;> simp [hb,hzero]

/-- No single-point conclusion is assumed: the source configuration itself supplies the mark and minimum. -/
theorem capGamma_eq_candidate {M L K : ℕ} {delta : ℝ} {omega : InfiniteSample}
    (hM : 2≤M) (hL : 1≤L) (hLM : L≤M) (hdelta : 0<delta)
    (heq : siteCounts _ (spatialMarkedSource (bulkStarts M L delta) L omega)=startField _ L omega)
    (hi : omega∉interiorEvent L) (hm : omega∉middleEvent M L delta)
    (hsmall : totalSize (bulkStarts M L delta) (spatialMarkedSource _ L omega)≤1) :
    capBorder K (gamma M L delta omega)=candidate (bulkStarts M L delta)
      (actualClockRecord L K omega,spatialMarkedSource (bulkStarts M L delta) L omega) := by
  by_cases hb : omega∈borderEvent L
  · rw [gamma_on_border hLM hb]
    simp [capBorder,borderLabel,candidate,actualClockRecord,hb]
  · have hfirst : firstStart M L omega≠1 := by
      intro hh
      exact hb ((firstStart_eq_one_iff hLM omega).mp hh)
    by_cases hz : totalSize (bulkStarts M L delta) (spatialMarkedSource _ L omega)=0
    · have hc := (totalSize_eq_zero_iff _ _).mp hz
      have hs : selectPoint (bulkStarts M L delta) (0 : SpatialMarkedConfig _)=none :=
        (selectPoint_eq_none _ _).mpr (by simp [totalSize])
      simp [gamma,recordFromValues,hfirst,hc,pointAtSite,capBorder,candidate,actualClockRecord,hb,hs]
    · have hsize : totalSize (bulkStarts M L delta) (spatialMarkedSource _ L omega)=1 := by omega
      obtain ⟨j,hc⟩ := (Finsupp.sum_eq_one_iff (spatialMarkedSource (bulkStarts M L delta) L omega)).mp hsize
      have hj2 : 2≤j.1.val := (Finset.mem_Icc.mp (bulkStarts_subset_Icc hM hL hdelta j.1.property)).1
      have hx := firstStart_eq_of_source_single hM hL hLM hdelta j heq hc hb hi hm
      rw [gamma_of_unique j (by omega) hx hc,hc]
      rw [candidate_on_single _ _ _ (by simp [actualClockRecord,hb])]
      rfl

/-- Every nonempty source mark already certifies a real contained start. -/
theorem rareEvent_source_subset_hit {M L K : ℕ} {delta : ℝ}
    (hM : 2≤M) (hL : 1≤L) (hLM : L≤M) (hdelta : 0<delta) :
    {omega | (actualClockRecord L K omega,spatialMarkedSource (bulkStarts M L delta) L omega)∈rareEvent _}
      ⊆ hitEvent M L := by
  intro omega ho
  have hh : omega∈borderEvent L ∨
      totalSize (bulkStarts M L delta) (spatialMarkedSource (bulkStarts M L delta) L omega)≠0 := by
    simpa [rareEvent,actualClockRecord] using ho
  apply border_union_bulk_subset_hit hM hL hLM hdelta
  rcases hh with hb | hn
  · exact Or.inl hb
  · have hc : spatialMarkedSource (bulkStarts M L delta) L omega≠0 := by
      intro h; exact hn ((totalSize_eq_zero_iff _ _).mpr h)
    obtain ⟨j,hj⟩ : ∃j : SpatialMarkedIndex (bulkStarts M L delta),
        spatialMarkedSource (bulkStarts M L delta) L omega j≠0 := by
      by_contra h
      push Not at h
      exact hc (Finsupp.ext h)
    have hs := (spatialMarkedValue_ne_zero_iff _ _ _ j).mp hj
    exact Or.inr (mem_iUnion.mpr ⟨j.1.val,mem_iUnion.mpr
      ⟨j.1.property,ExactLengthDecomposition.exactLengthEvent_start hs.1⟩⟩)

/-- Only the already proved almost-sure termination of source runs is used. -/
theorem ae_hit_iff_rareEvent {M L K : ℕ} {delta : ℝ}
    (hM : 2≤M) (hL : 1≤L) (hLM : L≤M) (hdelta : 0<delta) :
    ∀ᵐ omega ∂infiniteRademacherMeasure,
      omega∉interiorEvent L → omega∉middleEvent M L delta →
      (omega∈hitEvent M L ↔
        (actualClockRecord L K omega,spatialMarkedSource (bulkStarts M L delta) L omega)∈rareEvent _) := by
  filter_upwards [ae_siteCounts_source_eq (bulkStarts M L delta) L
    (fun x hx => (Finset.mem_Icc.mp (bulkStarts_subset_Icc hM hL hdelta hx)).1)] with omega heq
  exact hit_iff_rareEvent hM hL hLM hdelta heq

theorem ae_capGamma_eq_candidate {M L K : ℕ} {delta : ℝ}
    (hM : 2≤M) (hL : 1≤L) (hLM : L≤M) (hdelta : 0<delta) :
    ∀ᵐ omega ∂infiniteRademacherMeasure,
      omega∉interiorEvent L → omega∉middleEvent M L delta →
      totalSize (bulkStarts M L delta) (spatialMarkedSource (bulkStarts M L delta) L omega)≤1 →
      capBorder K (gamma M L delta omega)=candidate (bulkStarts M L delta)
        (actualClockRecord L K omega,spatialMarkedSource (bulkStarts M L delta) L omega) := by
  filter_upwards [ae_siteCounts_source_eq (bulkStarts M L delta) L
    (fun x hx => (Finset.mem_Icc.mp (bulkStarts_subset_Icc hM hL hdelta hx)).1)] with omega heq
  exact capGamma_eq_candidate hM hL hLM hdelta heq

end
end PaperC.V282.CrossoverSourceGeometry
