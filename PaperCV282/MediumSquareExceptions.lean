import PaperCV282.MediumSquarePacking
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # The explicit global square-exception bound in companion E.3

Square divisibilities are counted as incidences (integer, divisor), even
when one integer has several square divisors. This is the quantity needed
when converting ordinary divisibility into odd valuation incidences.
-/

namespace PaperC.V282.MediumSquareExceptions

open Finset MediumSquarePacking
open scoped BigOperators

/-- At most 854 medium square-divisor incidences occur in a quadratic window. -/
theorem square_incidence_card_le {S : Finset (ℕ × ℕ)} {lo B : ℕ}
    (hB : 1332 ≤ B)
    (hwindow : ∀ z ∈ S, 0 < z.1 ∧ lo ≤ z.1 ∧ z.1 < lo + B ∧ z.1 ≤ B ^ 2 + B)
    (hmedium : ∀ z ∈ S, B < 11 * z.2)
    (hsquare : ∀ z ∈ S, z.2 ^ 2 ∣ z.1) :
    S.card ≤ 854 := by
  let coefficient (z : ℕ × ℕ) := z.1 / z.2 ^ 2
  have heq : ∀ z ∈ S, z.1 = coefficient z * z.2 ^ 2 := by
    intro z hz
    exact (Nat.div_mul_cancel (hsquare z hz)).symm
  have hcoeff : ∀ z ∈ S, coefficient z ∈ Icc 1 122 := by
    intro z hz
    have hw := hwindow z hz
    have hm := hmedium z hz
    have hc := heq z hz
    rw [mem_Icc]
    constructor
    · by_contra h
      have hz0 : coefficient z = 0 := by omega
      rw [hz0, zero_mul] at hc
      omega
    · exact square_coefficient_le hB hm hw.2.2.2 hc
  have hfiber : ∀ a ∈ Icc 1 122, (S.filter fun z => coefficient z = a).card ≤ 7 := by
    intro a ha
    have hinj : Set.InjOn Prod.snd ((S.filter fun z => coefficient z = a) : Set (ℕ × ℕ)) := by
      intro z hz w hw hp
      obtain ⟨hzS,hza⟩ := mem_filter.mp hz
      obtain ⟨hwS,hwa⟩ := mem_filter.mp hw
      apply Prod.ext
      · rw [heq z hzS, heq w hwS, hza, hwa, hp]
      · exact hp
    rw [← Finset.card_image_iff.mpr hinj]
    apply coefficient_card_le_seven (mem_Icc.mp ha).1 (by omega : 0 < B)
    · intro p hp
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hp
      exact hmedium z (mem_filter.mp hz).1
    · intro p hp
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hp
      obtain ⟨hzS,hza⟩ := mem_filter.mp hz
      have hw := hwindow z hzS
      have hc := heq z hzS
      rw [hza] at hc
      rw [← hc]
      exact ⟨hw.2.1,hw.2.2.1⟩
  calc
    S.card = ∑ a ∈ Icc 1 122, (S.filter fun z => coefficient z = a).card :=
      card_eq_sum_card_fiberwise hcoeff
    _ ≤ ∑ _a ∈ Icc 1 122, 7 := sum_le_sum hfiber
    _ = 854 := by norm_num

/-- All positive medium square divisibilities in the actual interval. -/
def squareIncidences (lo B : ℕ) : Finset (ℕ × ℕ) :=
  ((Ico lo (lo + B)).product (Icc 1 B)).filter
    (fun z => 0 < z.1 ∧ B < 11 * z.2 ∧ z.2 ^ 2 ∣ z.1)

/-- The source's bound, uniform in the position of the quadratic window. -/
theorem squareIncidences_card_le {lo B : ℕ} (hB : 1332 ≤ B)
    (hlo : lo + B ≤ B ^ 2 + B + 1) :
    (squareIncidences lo B).card ≤ 854 := by
  apply square_incidence_card_le hB
  · intro z hz
    obtain ⟨hz,hpos,_,_⟩ := mem_filter.mp hz
    have hw := mem_Ico.mp (mem_product.mp hz).1
    exact ⟨hpos,hw.1,hw.2,by omega⟩
  · intro z hz
    exact (mem_filter.mp hz).2.2.1
  · intro z hz
    exact (mem_filter.mp hz).2.2.2

end PaperC.V282.MediumSquareExceptions
