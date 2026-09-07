import PaperCV282.RarePrefixGeometry
import PaperCV282.MesoscopicRareLimit

/-! # Exact event decomposition into border, mesoscopic and contained bulk starts -/
namespace PaperC.V282.RarePrefixEvents

open MeasureTheory Set InfiniteRademacher InfiniteStartProbabilityTransfer
open RarePrefixGeometry BulkMarkedGeometry MicroscopicBorderEvents MicroscopicNonvacancy

noncomputable section
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

def bulkHitEvent (M L : ℕ) (delta : ℝ) : Set InfiniteSample :=
  ⋃ x ∈ bulkStarts M L delta, infiniteStartEvent x L

def middleEvent (M L : ℕ) (delta : ℝ) : Set InfiniteSample :=
  {omega | ∃ x : ℕ, 2*L^2 < x ∧ (x : ℝ) < (M : ℝ)^delta ∧ omega∈infiniteStartEvent x L}

theorem measurableSet_bulkHitEvent (M L : ℕ) (delta : ℝ) :
    MeasurableSet (bulkHitEvent M L delta) :=
  MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun _ => measurableSet_infiniteStartEvent x L

theorem measurableSet_middleEvent (M L : ℕ) (delta : ℝ) :
    MeasurableSet (middleEvent M L delta) := by
  have he : middleEvent M L delta = ⋃ x : ℕ, ⋃ (_ : 2*L^2 < x),
      ⋃ (_ : (x : ℝ) < (M : ℝ)^delta), infiniteStartEvent x L := by
    ext omega
    simp [middleEvent, and_left_comm]
  rw [he]
  exact MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun _ =>
    MeasurableSet.iUnion fun _ => measurableSet_infiniteStartEvent x L

theorem border_union_bulk_subset_hit {M L : ℕ} {delta : ℝ}
    (hM : 2 ≤ M) (hL : 1 ≤ L) (hLM : L ≤ M) (hdelta : 0 < delta) :
    borderEvent L ∪ bulkHitEvent M L delta ⊆ hitEvent M L := by
  rw [hitEvent_eq_union hLM]
  intro omega homega
  rcases homega with hb | hb
  · exact Or.inl hb
  · rcases mem_iUnion.mp hb with ⟨x, hx⟩
    rcases mem_iUnion.mp hx with ⟨hx, he⟩
    exact Or.inr (mem_iUnion.mpr ⟨x, mem_iUnion.mpr ⟨Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp (bulkStarts_subset_Icc hM hL hdelta hx)).1,
        ((mem_bulkStarts M L x delta).mp hx).2⟩, he⟩⟩)

theorem hit_subset_border_bulk_middle {M L : ℕ} {delta : ℝ} (hLM : L ≤ M) :
    hitEvent M L ⊆ (borderEvent L ∪ bulkHitEvent M L delta) ∪
      (interiorEvent L ∪ middleEvent M L delta) := by
  rw [hitEvent_eq_union hLM]
  intro omega homega
  rcases homega with hb | hb
  · exact Or.inl (Or.inl hb)
  · rcases mem_iUnion.mp hb with ⟨x, hx⟩
    rcases mem_iUnion.mp hx with ⟨hx, he⟩
    obtain ⟨hxlo, hxhi⟩ := Finset.mem_Icc.mp hx
    by_cases hsmall : x ≤ 2*L^2
    · exact Or.inr (Or.inl (mem_iUnion.mpr ⟨x, mem_iUnion.mpr ⟨Finset.mem_Icc.mpr ⟨hxlo,hsmall⟩,he⟩⟩))
    · by_cases hmacro : (M : ℝ)^delta ≤ x
      · exact Or.inl (Or.inr (mem_iUnion.mpr ⟨x, mem_iUnion.mpr
          ⟨(mem_bulkStarts_iff_real M L x delta).mpr ⟨hmacro,hxhi⟩,he⟩⟩))
      · exact Or.inr (Or.inr ⟨x,by omega,by linarith,he⟩)

/-- The real rare-event mass differs from border-or-bulk by at most the two genuine exceptional events. -/
theorem hit_mass_difference_le {M L : ℕ} {delta : ℝ}
    (hM : 2 ≤ M) (hL : 1 ≤ L) (hLM : L ≤ M) (hdelta : 0 < delta) :
    |infiniteRademacherMeasure.real (hitEvent M L) -
      infiniteRademacherMeasure.real (borderEvent L ∪ bulkHitEvent M L delta)| ≤
        infiniteRademacherMeasure.real (interiorEvent L) +
          infiniteRademacherMeasure.real (middleEvent M L delta) := by
  have hlo := measureReal_mono (μ := infiniteRademacherMeasure)
    (border_union_bulk_subset_hit hM hL hLM hdelta)
  have hhi := (measureReal_mono (μ := infiniteRademacherMeasure)
    (hit_subset_border_bulk_middle (delta := delta) hLM)).trans
      (measureReal_union_le _ _)
  have he := measureReal_union_le (μ := infiniteRademacherMeasure) (interiorEvent L) (middleEvent M L delta)
  rw [abs_of_nonneg (by linarith)]
  linarith

end
end PaperC.V282.RarePrefixEvents
