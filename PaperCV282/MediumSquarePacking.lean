import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

/-! # Uniform packing of medium-prime square multiples

The arithmetic estimates are proved for all positive integers in the
medium interval, hence apply in particular to primes. The explicit bound
854 is a local square-exception bound, not a threshold for the PNT or the
Laishram--Shorey asymptotic input.
-/

namespace PaperC.V282.MediumSquarePacking

open Finset

/-- Seven buckets suffice for points separated by more than one seventh of a window. -/
theorem card_le_seven_of_separated {S : Finset ℕ} {a B : ℕ} (hB : 0 < B)
    (hwindow : ∀ n ∈ S, a ≤ n ∧ n < a + B)
    (hsep : ∀ m ∈ S, ∀ n ∈ S, m < n → B < 7 * (n - m)) :
    S.card ≤ 7 := by
  have hmem : ∀ n ∈ S, 7 * (n - a) / B ∈ range 7 := by
    intro n hn
    have hw := hwindow n hn
    rw [mem_range, Nat.div_lt_iff_lt_mul hB]
    omega
  have hinj : Set.InjOn (fun n => 7 * (n - a) / B) (S : Set ℕ) := by
    intro m hm n hn heq
    have hm' := hwindow m hm
    have hn' := hwindow n hn
    have hmodm := Nat.mod_lt (7 * (m - a)) hB
    have hmodn := Nat.mod_lt (7 * (n - a)) hB
    have hdm := Nat.mod_add_div (7 * (m - a)) B
    have hdn := Nat.mod_add_div (7 * (n - a)) B
    dsimp only at heq
    rw [← heq] at hdn
    rcases lt_trichotomy m n with hlt | he | hgt
    · have hs := hsep m hm n hn hlt
      omega
    · exact he
    · have hs := hsep n hn m hm hgt
      omega
  have hc := Finset.card_le_card_of_injOn (fun n => 7 * (n - a) / B) hmem hinj
  simpa only [card_range] using hc

/-- Successive square multiples in the medium interval have the required gap. -/
theorem square_multiple_separation {a B p q : ℕ} (ha : 1 ≤ a)
    (hp : B < 11 * p) (hpq : p < q) :
    B < 7 * (a * q ^ 2 - a * p ^ 2) := by
  have hsq : (p + 1) ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hbase : 2 * p + 1 ≤ q ^ 2 - p ^ 2 := by
    have hle := Nat.pow_le_pow_left hpq.le 2
    have hsub := Nat.sub_add_cancel hle
    nlinarith
  have hmul : q ^ 2 - p ^ 2 ≤ a * (q ^ 2 - p ^ 2) :=
    Nat.le_mul_of_pos_left _ ha
  rw [Nat.mul_sub_left_distrib] at hmul
  omega

/-- For each coefficient, at most seven medium square multiples fit in the window. -/
theorem coefficient_card_le_seven {S : Finset ℕ} {a lo B : ℕ}
    (ha : 1 ≤ a) (hB : 0 < B)
    (hmedium : ∀ p ∈ S, B < 11 * p)
    (hwindow : ∀ p ∈ S, lo ≤ a * p ^ 2 ∧ a * p ^ 2 < lo + B) :
    S.card ≤ 7 := by
  have hinj : Set.InjOn (fun p => a * p ^ 2) (S : Set ℕ) := by
    intro p hp q hq heq
    have hs : p ^ 2 = q ^ 2 := Nat.eq_of_mul_eq_mul_left (by omega) heq
    nlinarith
  rw [← Finset.card_image_iff.mpr hinj]
  apply card_le_seven_of_separated hB
  · intro n hn
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hn
    exact hwindow p hp
  · intro m hm n hn hmn
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hm
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hn
    have hpq : p < q := by
      by_contra h
      have hsq := Nat.pow_le_pow_left (Nat.le_of_not_gt h) 2
      have := Nat.mul_le_mul_left a hsq
      omega
    exact square_multiple_separation ha (hmedium p hp) hpq

/-- Every possible square coefficient is at most 122 once B is at least 1332. -/
theorem square_coefficient_le {B n p a : ℕ} (hB : 1332 ≤ B)
    (hp : B < 11 * p) (hn : n ≤ B ^ 2 + B) (heq : n = a * p ^ 2) :
    a ≤ 122 := by
  have hpbig : 122 ≤ p := by omega
  have hsq : B ^ 2 < (11 * p) ^ 2 := Nat.pow_lt_pow_left hp (by decide)
  have hcap : n ≤ 122 * p ^ 2 := by nlinarith
  have hpp : 0 < p ^ 2 := by positivity
  rw [heq] at hcap
  exact Nat.le_of_mul_le_mul_right hcap hpp

end PaperC.V282.MediumSquarePacking
