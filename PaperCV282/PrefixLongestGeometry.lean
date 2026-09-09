import PaperCV282.MicroscopicBorderEvents

/-! # The exact finite-prefix longest run on the original infinite source

This module reuses the historical observable, including its boundary at one.
No new choice of a longest-run variable or source law is made.
-/
namespace PaperC.V282.PrefixLongestGeometry

open MeasureTheory Set CorollaryPrefixLaw InfiniteRademacher InfiniteCylinderTransfer
open InfiniteStartProbabilityTransfer MicroscopicBorderEvents

noncomputable section

local instance instDecidableProp (P : Prop) : Decidable P := Classical.propDecidable P

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

/-- A contained run remains contained when the right endpoint increases. -/
theorem prefixHasConstantStretch_mono_endpoint {g : ℕ → F₂} {M N L : ℕ}
    (hMN : M ≤ N) (h : prefixHasConstantStretch g M L) :
    prefixHasConstantStretch g N L := by
  obtain ⟨x,hx,hcut,hconst⟩ := h
  exact ⟨x,hx,by omega,hconst⟩

/-- The historical longest-run observable is monotone in the actual prefix length. -/
theorem prefixLongestConstantStretch_mono (g : ℕ → F₂) :
    Monotone (prefixLongestConstantStretch g) := by
  intro M N hMN
  by_contra h
  have hlt : prefixLongestConstantStretch g N < prefixLongestConstantStretch g M := by omega
  have hn := prefixLongestConstantStretch_lt_iff.mp hlt
  have hm : prefixHasConstantStretch g M (prefixLongestConstantStretch g M) := by
    by_contra hh
    exact (Nat.lt_irrefl _) (prefixLongestConstantStretch_lt_iff.mpr hh)
  exact hn (prefixHasConstantStretch_mono_endpoint hMN hm)

/-- Every realized longest run has length at most the prefix length. -/
theorem prefixLongestConstantStretch_le (g : ℕ → F₂) (M : ℕ) :
    prefixLongestConstantStretch g M ≤ M := by
  have hm : prefixHasConstantStretch g M (prefixLongestConstantStretch g M) := by
    by_contra hh
    exact (Nat.lt_irrefl _) (prefixLongestConstantStretch_lt_iff.mpr hh)
  obtain ⟨x,hx⟩ := hm
  exact prefixConstantStretch_length_le hx

/-- The same deterministic monotonicity holds sample by sample in the infinite model. -/
theorem infinitePrefixLongestConstantStretch_mono (omega : InfiniteSample) :
    Monotone (fun M => infinitePrefixLongestConstantStretch M omega) :=
  prefixLongestConstantStretch_mono (infiniteValueBit omega)

/-- Exact convention of the contained interior sites: both endpoints are included. -/
theorem prefixInteriorStartIndices_eq_Icc (M L : ℕ) :
    prefixInteriorStartIndices M L = Finset.Icc 2 (M-L+1) := by
  ext x
  simp only [prefixInteriorStartIndices,Finset.mem_Ico,Finset.mem_Icc]
  omega

/-- The prefix count is precisely the border indicator plus the contained starts. -/
theorem infinitePrefixStartCount_eq_border_add (M L : ℕ) (omega : InfiniteSample) :
    infinitePrefixStartCount M L omega =
      (if omega ∈ borderEvent L then 1 else 0) +
      ∑ x ∈ Finset.Icc 2 (M-L+1), if omega ∈ infiniteStartEvent x L then 1 else 0 := by
  classical
  rw [infinitePrefixStartCount,prefixStartCount,prefixInteriorStartIndices_eq_Icc]
  have hb : prefixBoundaryEvent (infiniteValueBit omega) L ↔ omega ∈ borderEvent L := by
    rw [borderEvent_eq_prefix]
    rfl
  simp only [hb,infiniteStartEvent,Set.mem_setOf_eq]

/-- The actual longest-run void event is exactly the absence of border and contained starts. -/
theorem longest_lt_iff_border_and_no_start {M L : ℕ} (hLM : L ≤ M)
    (omega : InfiniteSample) :
    infinitePrefixLongestConstantStretch M omega < L ↔
      omega ∉ borderEvent L ∧ ∀ x ∈ Finset.Icc 2 (M-L+1),
        omega ∉ infiniteStartEvent x L := by
  rw [← infinitePrefixStartCount_eq_zero_iff_longest_lt hLM,
    infinitePrefixStartCount_eq_border_add]
  simp only [Nat.add_eq_zero_iff,ite_eq_right_iff,one_ne_zero,imp_false,
    Finset.sum_eq_zero_iff]

/-- Threshold events of the genuine longest-run variable are measurable. -/
theorem measurableSet_longest_lt (M L : ℕ) :
    MeasurableSet {omega | infinitePrefixLongestConstantStretch M omega < L} := by
  by_cases hLM : L ≤ M
  · have he : {omega | infinitePrefixLongestConstantStretch M omega < L} =
        infinitePrefixStartCountEvent M L 0 := by
      ext omega
      exact (infinitePrefixStartCount_eq_zero_iff_longest_lt hLM omega).symm
    rw [he]
    exact measurableSet_infinitePrefixStartCountEvent M L 0
  · have he : {omega | infinitePrefixLongestConstantStretch M omega < L} = Set.univ := by
      ext omega
      simp only [Set.mem_setOf_eq,Set.mem_univ,iff_true]
      exact lt_of_le_of_lt (prefixLongestConstantStretch_le _ M) (by omega)
    rw [he]
    exact MeasurableSet.univ

/-- The historical natural-valued longest run is a measurable random variable. -/
theorem measurable_infinitePrefixLongestConstantStretch (M : ℕ) :
    Measurable (infinitePrefixLongestConstantStretch M) := by
  apply measurable_to_countable'
  intro r
  have he : (infinitePrefixLongestConstantStretch M) ⁻¹' {r} =
      {omega | infinitePrefixLongestConstantStretch M omega < r+1} \
      {omega | infinitePrefixLongestConstantStretch M omega < r} := by
    ext omega
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_sdiff,Set.mem_setOf_eq]
    omega
  rw [he]
  exact (measurableSet_longest_lt M (r+1)).diff (measurableSet_longest_lt M r)

/-- A threshold exceedance uses the true source events and the precise containment endpoint. -/
theorem longest_ge_event {M L : ℕ} (hLM : L ≤ M) :
    {omega | L ≤ infinitePrefixLongestConstantStretch M omega} =
      borderEvent L ∪ ⋃ x ∈ Finset.Icc 2 (M-L+1), infiniteStartEvent x L := by
  ext omega
  simp only [Set.mem_setOf_eq,Set.mem_union,Set.mem_iUnion]
  rw [← not_lt, longest_lt_iff_border_and_no_start hLM omega]
  push Not
  tauto

end
end PaperC.V282.PrefixLongestGeometry
