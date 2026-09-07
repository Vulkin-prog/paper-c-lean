import PaperCV282.MaskedScalarFullConditioning

/-!
# Conditioning events in the actual small-prime sigma-algebra

An event is selected by a finite set of small-prime assignments. Its
source probability is exactly its fraction of the equiprobable atoms.
Every event measurable in the represented sigma-algebra has this form.
The identities below use that exact source mass as denominator.
-/

namespace PaperC.V282.PrimeFieldEventConditioning

open MeasureTheory Set
open InfiniteRademacher InfiniteCylinderTransfer InfiniteConditionalWords
open MaskedScalarFullConditioning ConditionalStartProbability
open scoped BigOperators ENNReal

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

/-- A genuine environment event selected solely by small-prime coordinates. -/
def primeFieldEvent (C Y : ℕ) (S : Finset (SmallSample C Y)) : Set InfiniteSample :=
  {omega | smallPrimeRestriction C Y omega ∈ S}

theorem primeFieldEvent_eq_preimage (C Y : ℕ) (S : Finset (SmallSample C Y)) :
    primeFieldEvent C Y S = smallPrimeRestriction C Y ⁻¹' (S : Set (SmallSample C Y)) := rfl

/-- The selected event is exactly the union of its source atoms. -/
theorem primeFieldEvent_eq_union (C Y : ℕ) (S : Finset (SmallSample C Y)) :
    primeFieldEvent C Y S = ⋃ sigma ∈ S, infiniteSmallPrimeAtom C Y sigma := by
  ext omega
  simp only [primeFieldEvent, infiniteSmallPrimeAtom, mem_setOf_eq, mem_iUnion, exists_prop]
  exact ⟨fun h => ⟨_,h,rfl⟩, fun ⟨sigma,hs,heq⟩ => heq ▸ hs⟩

theorem measurableSet_primeFieldEvent_small (C Y : ℕ) (S : Finset (SmallSample C Y)) :
    MeasurableSet[smallPrimeSigmaAlgebra C Y] (primeFieldEvent C Y S) :=
  (comap_measurable (smallPrimeRestriction C Y)) (Set.toFinite _ |>.measurableSet)

theorem measurableSet_primeFieldEvent (C Y : ℕ) (S : Finset (SmallSample C Y)) :
    MeasurableSet (primeFieldEvent C Y S) :=
  (measurable_smallPrimeRestriction C Y) (Set.toFinite _ |>.measurableSet)

/-- Distinct assignments have disjoint source atoms. -/
theorem infiniteSmallPrimeAtom_disjoint {C Y : ℕ} {sigma tau : SmallSample C Y}
    (hne : sigma ≠ tau) :
    Disjoint (infiniteSmallPrimeAtom C Y sigma) (infiniteSmallPrimeAtom C Y tau) := by
  apply Set.disjoint_left.mpr
  intro omega hs ht
  exact hne (hs.symm.trans ht)

/-- The exact real mass of an individual conditioning atom. -/
theorem real_atom_mass (C Y : ℕ) (sigma : SmallSample C Y) :
    infiniteRademacherMeasure.real (infiniteSmallPrimeAtom C Y sigma) =
      1 / (Fintype.card (SmallSample C Y) : ℝ) := by
  rw [measureReal_def, conditioningAtoms_equiprobable, ENNReal.toReal_ofReal (by positivity)]

/-- Source intersections split over the actual disjoint selected atoms. -/
theorem real_inter_primeFieldEvent (C Y : ℕ) (S : Finset (SmallSample C Y))
    (E : Set InfiniteSample) (hE : MeasurableSet E) :
    infiniteRademacherMeasure.real (E ∩ primeFieldEvent C Y S) =
      ∑ sigma ∈ S, infiniteRademacherMeasure.real (E ∩ infiniteSmallPrimeAtom C Y sigma) := by
  rw [primeFieldEvent_eq_union, inter_iUnion]
  simp_rw [inter_iUnion]
  apply measureReal_biUnion_finset
  · intro sigma hs tau ht hne
    exact (infiniteSmallPrimeAtom_disjoint hne).mono inter_subset_right inter_subset_right
  · intro sigma _
    exact hE.inter (measurableSet_infiniteSmallPrimeAtom C Y sigma)
  · intro sigma _
    exact ne_top_of_le_ne_top (infiniteSmallPrimeAtom_measure_ne_top C Y sigma)
      (measure_mono inter_subset_right)

/-- The event probability is the literal selected-atom fraction. -/
theorem real_primeFieldEvent (C Y : ℕ) (S : Finset (SmallSample C Y)) :
    infiniteRademacherMeasure.real (primeFieldEvent C Y S) =
      (S.card : ℝ) / (Fintype.card (SmallSample C Y) : ℝ) := by
  have h := real_inter_primeFieldEvent C Y S Set.univ MeasurableSet.univ
  simp only [univ_inter, real_atom_mass, Finset.sum_const, nsmul_eq_mul] at h
  simpa only [mul_one_div] using h

/-- Positive source mass is equivalent to selecting at least one assignment. -/
theorem real_primeFieldEvent_pos_iff (C Y : ℕ) (S : Finset (SmallSample C Y)) :
    0 < infiniteRademacherMeasure.real (primeFieldEvent C Y S) ↔ S.Nonempty := by
  rw [real_primeFieldEvent]
  have hcard : (0 : ℝ) < Fintype.card (SmallSample C Y) := by positivity
  rw [div_pos_iff_of_pos_right hcard]
  exact_mod_cast Finset.card_pos

/-- No measurable event of the finite small-prime sigma-algebra is omitted. -/
theorem measurableSet_eq_primeFieldEvent {C Y : ℕ} {E : Set InfiniteSample}
    (hE : MeasurableSet[smallPrimeSigmaAlgebra C Y] E) :
    ∃ S : Finset (SmallSample C Y), E = primeFieldEvent C Y S := by
  classical
  obtain ⟨T,hT,hEq⟩ := MeasurableSpace.measurableSet_comap.mp hE
  refine ⟨Finset.univ.filter (fun sigma => sigma ∈ T), ?_⟩
  rw [← hEq]
  ext omega
  simp only [primeFieldEvent, mem_preimage, mem_setOf_eq, Finset.mem_filter,
    Finset.mem_univ, true_and]

/-- Conditioning on a nonempty selected event is the normalized mixture of its atoms. -/
theorem source_event_ratio_eq_atom_average (C Y : ℕ) (S : Finset (SmallSample C Y))
    (_hS : S.Nonempty) (E : Set InfiniteSample) (hE : MeasurableSet E) :
    infiniteRademacherMeasure.real (E ∩ primeFieldEvent C Y S) /
        infiniteRademacherMeasure.real (primeFieldEvent C Y S) =
      (∑ sigma ∈ S,
        infiniteRademacherMeasure.real (E ∩ infiniteSmallPrimeAtom C Y sigma) /
          infiniteRademacherMeasure.real (infiniteSmallPrimeAtom C Y sigma)) / S.card := by
  rw [real_inter_primeFieldEvent C Y S E hE, real_primeFieldEvent]
  simp_rw [real_atom_mass]
  rw [← Finset.sum_div]
  field_simp

end
end PaperC.V282.PrimeFieldEventConditioning
