import PaperCV282.PrefixLongestGeometry
import PaperCV282.BulkMarkedGeometry
import PaperCV282.MicroscopicNonvacancy

/-! # The real contained first departure for the rare prefix crossover -/
namespace PaperC.V282.RarePrefixGeometry

open MeasureTheory Set InfiniteRademacher InfiniteStartProbabilityTransfer
open CorollaryPrefixLaw PrefixLongestGeometry MicroscopicBorderEvents MicroscopicNonvacancy
open BulkMarkedGeometry

noncomputable section
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

/-- The hit event uses the already defined longest run of the finite prefix. -/
def hitEvent (M L : ℕ) : Set InfiniteSample :=
  {omega | L ≤ infinitePrefixLongestConstantStretch M omega}

/-- The border and the ordinary left-maximal start have their original distinct definitions. -/
def siteStartEvent (L x : ℕ) : Set InfiniteSample :=
  if x=1 then borderEvent L else if 2≤x then infiniteStartEvent x L else ∅

def containedStarts (M L : ℕ) (omega : InfiniteSample) : Finset ℕ :=
  (Finset.Icc 1 (M-L+1)).filter (fun x => L≤M ∧ omega∈siteStartEvent L x)

/-- Default zero occurs only when there is no contained start. -/
def firstStart (M L : ℕ) (omega : InfiniteSample) : ℕ :=
  if h : (containedStarts M L omega).Nonempty then Nat.find h else 0

theorem mem_containedStarts (M L x : ℕ) (omega : InfiniteSample) :
    x∈containedStarts M L omega ↔ 1≤x ∧ x≤M-L+1 ∧ L≤M ∧ omega∈siteStartEvent L x := by
  simp only [containedStarts,Finset.mem_filter,Finset.mem_Icc]
  tauto

theorem measurableSet_siteStartEvent (L x : ℕ) : MeasurableSet (siteStartEvent L x) := by
  unfold siteStartEvent
  split_ifs
  · exact measurableSet_borderEvent L
  · exact measurableSet_infiniteStartEvent x L
  · exact MeasurableSet.empty

theorem measurableSet_mem_containedStarts (M L x : ℕ) :
    MeasurableSet {omega | x∈containedStarts M L omega} := by
  simp only [mem_containedStarts]
  by_cases h : 1≤x ∧ x≤M-L+1 ∧ L≤M
  · have he : {omega | 1≤x ∧ x≤M-L+1 ∧ L≤M ∧ omega∈siteStartEvent L x}=siteStartEvent L x := by
      ext omega;simp only [Set.mem_setOf_eq];tauto
    rw [he]
    exact measurableSet_siteStartEvent L x
  · have he : {omega | 1≤x ∧ x≤M-L+1 ∧ L≤M ∧ omega∈siteStartEvent L x}=∅ := by
      ext omega;simp only [Set.mem_setOf_eq,Set.mem_empty_iff_false];tauto
    rw [he]
    exact MeasurableSet.empty

theorem measurableSet_hitEvent (M L : ℕ) : MeasurableSet (hitEvent M L) := by
  have he : hitEvent M L={omega | infinitePrefixLongestConstantStretch M omega<L}ᶜ := by
    ext omega;simp only [hitEvent,Set.mem_setOf_eq,Set.mem_compl_iff,not_lt]
  rw [he]
  exact (measurableSet_longest_lt M L).compl

theorem hitEvent_eq_union {M L : ℕ} (hLM : L≤M) :
    hitEvent M L=borderEvent L ∪ ⋃x∈Finset.Icc 2 (M-L+1),infiniteStartEvent x L :=
  longest_ge_event hLM

theorem containedStarts_nonempty_iff (M L : ℕ) (omega : InfiniteSample) :
    (containedStarts M L omega).Nonempty ↔ omega∈hitEvent M L := by
  by_cases hLM : L≤M
  · rw [hitEvent_eq_union hLM]
    simp only [Set.mem_union,Set.mem_iUnion]
    constructor
    · rintro ⟨x,hx⟩
      obtain ⟨hx1,hxu,_,hs⟩ := (mem_containedStarts M L x omega).mp hx
      by_cases he : x=1
      · exact Or.inl (by simpa [siteStartEvent,he] using hs)
      · exact Or.inr ⟨x,Finset.mem_Icc.mpr ⟨by omega,hxu⟩,
          by simpa [siteStartEvent,he,show 2≤x by omega] using hs⟩
    · rintro (hb|⟨x,hx,hs⟩)
      · exact ⟨1,(mem_containedStarts M L 1 omega).mpr ⟨by omega,by omega,hLM,by simpa [siteStartEvent] using hb⟩⟩
      · obtain ⟨hx1,hxu⟩ := Finset.mem_Icc.mp hx
        exact ⟨x,(mem_containedStarts M L x omega).mpr ⟨by omega,hxu,hLM,
          by simpa [siteStartEvent,show x≠1 by omega,hx1] using hs⟩⟩
  · have he : containedStarts M L omega=∅ := by simp [containedStarts,hLM]
    rw [he]
    simp only [Finset.not_nonempty_empty,hitEvent,Set.mem_setOf_eq,false_iff,not_le]
    exact (prefixLongestConstantStretch_le (infiniteValueBit omega) M).trans_lt (by omega)

theorem firstStart_eq_iff_of_hit {M L : ℕ} {omega : InfiniteSample}
    (h : omega∈hitEvent M L) (x : ℕ) :
    firstStart M L omega=x ↔ x∈containedStarts M L omega ∧ ∀j<x,j∉containedStarts M L omega := by
  rw [firstStart,dif_pos ((containedStarts_nonempty_iff M L omega).mpr h)]
  exact Nat.find_eq_iff (p := fun n => n ∈ containedStarts M L omega)
    ((containedStarts_nonempty_iff M L omega).mpr h)

theorem firstStart_mem {M L : ℕ} {omega : InfiniteSample} (h : omega∈hitEvent M L) :
    firstStart M L omega∈containedStarts M L omega :=
  ((firstStart_eq_iff_of_hit h _).mp rfl).1

theorem firstStart_le {M L x : ℕ} {omega : InfiniteSample} (hx : x∈containedStarts M L omega) :
    firstStart M L omega≤x := by
  have hs : (containedStarts M L omega).Nonempty := ⟨x,hx⟩
  rw [firstStart,dif_pos hs]
  exact Nat.find_min' hs hx

theorem firstStart_eq_zero_iff (M L : ℕ) (omega : InfiniteSample) :
    firstStart M L omega=0 ↔ omega∉hitEvent M L := by
  by_cases h : omega∈hitEvent M L
  · have hm := (mem_containedStarts M L _ omega).mp (firstStart_mem h)
    simp only [h,not_true_eq_false,iff_false]
    omega
  · have hs : ¬(containedStarts M L omega).Nonempty := by rwa [containedStarts_nonempty_iff]
    simp [firstStart,hs,h]

theorem firstStart_eq_one_iff {M L : ℕ} (hLM : L≤M) (omega : InfiniteSample) :
    firstStart M L omega=1 ↔ omega∈borderEvent L := by
  constructor
  · intro h
    have hh : omega∈hitEvent M L := by
      by_contra hn
      have hz := (firstStart_eq_zero_iff M L omega).mpr hn
      omega
    have hm := (mem_containedStarts M L _ omega).mp (firstStart_mem hh)
    simpa [h,siteStartEvent] using hm.2.2.2
  · intro hb
    have hm : 1∈containedStarts M L omega := (mem_containedStarts M L 1 omega).mpr
      ⟨by omega,by omega,hLM,by simpa [siteStartEvent] using hb⟩
    have hlo := (mem_containedStarts M L _ omega).mp (firstStart_mem ((containedStarts_nonempty_iff M L omega).mp ⟨1,hm⟩))
    have hhi := firstStart_le hm
    omega

/-- The minimum is measurable, including its default on the no-hit event. -/
theorem measurable_firstStart (M L : ℕ) : Measurable (firstStart M L) := by
  apply measurable_to_countable'
  intro x
  have he : {omega | firstStart M L omega=x}=
      ({omega | x∈containedStarts M L omega} ∩ ⋂j,⋂(_ : j<x),{omega | j∈containedStarts M L omega}ᶜ) ∪
      (if x=0 then (hitEvent M L)ᶜ else ∅) := by
    ext omega
    by_cases hh : omega∈hitEvent M L
    · simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_iInter]
      rw [firstStart_eq_iff_of_hit hh x]
      by_cases hx : x = 0 <;> simp [hx, hh]
    · have hnone : ∀j,j∉containedStarts M L omega := by
        intro j hj
        exact hh ((containedStarts_nonempty_iff M L omega).mp ⟨j,hj⟩)
      have hz := (firstStart_eq_zero_iff M L omega).mpr hh
      by_cases hx : x=0 <;> simp [hz,hnone,hh,hx,eq_comm]
  change MeasurableSet {omega | firstStart M L omega=x}
  rw [he]
  apply ((measurableSet_mem_containedStarts M L x).inter
    (MeasurableSet.iInter fun j => MeasurableSet.iInter fun (_ : j<x) =>
      (measurableSet_mem_containedStarts M L j).compl)).union
  split_ifs
  · exact (measurableSet_hitEvent M L).compl
  · exact MeasurableSet.empty

end
end PaperC.V282.RarePrefixGeometry
