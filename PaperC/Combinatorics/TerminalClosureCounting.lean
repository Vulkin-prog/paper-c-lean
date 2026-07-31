import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Finite counting kernels for the terminal matching

This file isolates the elementary combinatorial steps in the proof of
Theorem 10.1.  It does not assert the Diophantine estimates used by that
theorem.  Instead it proves, with exact finite inequalities:

* a pairwise product bound leaves at most one factor above the square-root
  threshold;
* double counting an incidence relation bounds the number of first starts;
* a pointwise rank bound controls the total residual weight.

These statements are independent of asymptotic notation and can therefore
be reused verbatim when the arithmetic estimates of Sections 9--10 are
connected to the concrete terminal population.
-/

namespace PaperC
namespace TerminalClosureCounting

open scoped BigOperators

section LargeFactors

variable {ι : Type*}

/--
If every two distinct factors have product at most `T²`, at most one factor
can be strictly larger than `T`.

This is the exact finite content of Step 1 in the proof of Theorem 10.1.
-/
theorem card_filter_large_le_one
    (indices : Finset ι) (factor : ι → ℕ) (T : ℕ)
    (hpair :
      ∀ ⦃s t : ι⦄, s ∈ indices → t ∈ indices → s ≠ t →
        factor s * factor t ≤ T ^ 2) :
    (indices.filter fun t ↦ T < factor t).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro s hs t ht
  have hsData := Finset.mem_filter.mp hs
  have htData := Finset.mem_filter.mp ht
  by_contra hst
  have hbound :=
    hpair hsData.1 htData.1 hst
  have hsLower : T + 1 ≤ factor s := by omega
  have htLower : T + 1 ≤ factor t := by omega
  have hstrict :
      T ^ 2 < factor s * factor t := by
    nlinarith
  exact (Nat.not_lt_of_ge hbound) hstrict

/--
Equivalent uniqueness formulation: two indices above the threshold must be
equal.
-/
theorem eq_of_both_large
    (indices : Finset ι) (factor : ι → ℕ) (T : ℕ)
    (hpair :
      ∀ ⦃s t : ι⦄, s ∈ indices → t ∈ indices → s ≠ t →
        factor s * factor t ≤ T ^ 2)
    {s t : ι}
    (hs : s ∈ indices) (ht : t ∈ indices)
    (hsLarge : T < factor s) (htLarge : T < factor t) :
    s = t := by
  by_contra hst
  have hbound := hpair hs ht hst
  have hsLower : T + 1 ≤ factor s := by omega
  have htLower : T + 1 ≤ factor t := by omega
  have hstrict : T ^ 2 < factor s * factor t := by
    nlinarith
  exact (Nat.not_lt_of_ge hbound) hstrict

end LargeFactors

section Incidences

variable {α β : Type*}

/-- The finite incidence relation between two finite populations. -/
def incidences
    (left : Finset α) (right : Finset β)
    (related : α → β → Prop) [DecidableRel related] :
    Finset (α × β) :=
  left ×ˢ right |>.filter fun z ↦ related z.1 z.2

@[simp]
theorem mem_incidences
    {left : Finset α} {right : Finset β}
    {related : α → β → Prop} [DecidableRel related]
    {a : α} {b : β} :
    (a, b) ∈ incidences left right related ↔
      a ∈ left ∧ b ∈ right ∧ related a b := by
  simp [incidences, and_assoc]

/--
The incidence cardinality is the sum of the right fibres.
-/
theorem card_incidences_eq_sum_right_fibers
    (left : Finset α) (right : Finset β)
    (related : α → β → Prop) [DecidableRel related] :
    (incidences left right related).card =
      ∑ a ∈ left, (right.filter fun b ↦ related a b).card := by
  classical
  simp only [incidences, Finset.card_eq_sum_ones,
    Finset.sum_filter, Finset.mem_product]
  rw [Finset.sum_product]

/--
The same incidence cardinality is the sum of the left fibres.
-/
theorem card_incidences_eq_sum_left_fibers
    (left : Finset α) (right : Finset β)
    (related : α → β → Prop) [DecidableRel related] :
    (incidences left right related).card =
      ∑ b ∈ right, (left.filter fun a ↦ related a b).card := by
  classical
  rw [card_incidences_eq_sum_right_fibers]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]

/--
Double-counting bound.  If every left object has at least `m` incidences and
every right object has at most `q`, then

`m * #left ≤ q * #right`.

This is the exact form used in Step 2 of Theorem 10.1.
-/
theorem incidence_double_count
    (left : Finset α) (right : Finset β)
    (related : α → β → Prop) [DecidableRel related]
    (m q : ℕ)
    (hlower :
      ∀ a ∈ left,
        m ≤ (right.filter fun b ↦ related a b).card)
    (hupper :
      ∀ b ∈ right,
        (left.filter fun a ↦ related a b).card ≤ q) :
    m * left.card ≤ q * right.card := by
  classical
  have hleft :
      m * left.card ≤
        ∑ a ∈ left,
          (right.filter fun b ↦ related a b).card := by
    calc
      m * left.card = ∑ _a ∈ left, m := by
        simp [Nat.mul_comm]
      _ ≤ ∑ a ∈ left,
          (right.filter fun b ↦ related a b).card := by
        exact Finset.sum_le_sum hlower
  have hright :
      (∑ b ∈ right,
          (left.filter fun a ↦ related a b).card) ≤
        q * right.card := by
    calc
      (∑ b ∈ right,
          (left.filter fun a ↦ related a b).card)
          ≤ ∑ _b ∈ right, q := by
            exact Finset.sum_le_sum hupper
      _ = q * right.card := by
        simp [Nat.mul_comm]
  calc
    m * left.card ≤
        ∑ a ∈ left,
          (right.filter fun b ↦ related a b).card :=
      hleft
    _ = ∑ b ∈ right,
          (left.filter fun a ↦ related a b).card := by
      rw [← card_incidences_eq_sum_right_fibers,
        card_incidences_eq_sum_left_fibers]
    _ ≤ q * right.card := hright

/--
The manuscript's `B/2` incidence specialization, stated without rounding
ambiguity: if `B ≤ 2m`, then `B * #left ≤ 2B * #right`.
-/
theorem incidence_half_specialization
    (left : Finset α) (right : Finset β)
    (related : α → β → Prop) [DecidableRel related]
    (B m : ℕ)
    (hB : B ≤ 2 * m)
    (hlower :
      ∀ a ∈ left,
        m ≤ (right.filter fun b ↦ related a b).card)
    (hupper :
      ∀ b ∈ right,
        (left.filter fun a ↦ related a b).card ≤ B) :
    B * left.card ≤ 2 * B * right.card := by
  have hcount :=
    incidence_double_count left right related m B hlower hupper
  nlinarith

/--
After cancelling a positive `B`, the preceding estimate gives the clean
cardinality bound `#left ≤ 2 #right`.
-/
theorem card_left_le_twice_card_right
    (left : Finset α) (right : Finset β)
    (related : α → β → Prop) [DecidableRel related]
    (B m : ℕ)
    (hBPos : 0 < B)
    (hB : B ≤ 2 * m)
    (hlower :
      ∀ a ∈ left,
        m ≤ (right.filter fun b ↦ related a b).card)
    (hupper :
      ∀ b ∈ right,
        (left.filter fun a ↦ related a b).card ≤ B) :
    left.card ≤ 2 * right.card := by
  have h :=
    incidence_half_specialization
      left right related B m hB hlower hupper
  refine Nat.le_of_mul_le_mul_left ?_ hBPos
  calc
    B * left.card ≤ 2 * B * right.card := h
    _ = B * (2 * right.card) := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

end Incidences

section ResidualWeights

variable {α : Type*}

/-- Pointwise domination bounds a finite sum by cardinality times the envelope. -/
theorem sum_le_card_mul
    (population : Finset α) (weight : α → ℕ) (W : ℕ)
    (hweight : ∀ z ∈ population, weight z ≤ W) :
    (∑ z ∈ population, weight z) ≤ population.card * W := by
  calc
    (∑ z ∈ population, weight z) ≤
        ∑ _z ∈ population, W :=
      Finset.sum_le_sum hweight
    _ = population.card * W := by simp

/--
If `τ ≤ B+2`, then the residual weight `2^τ-1` is at most `4·2^B`.
-/
theorem two_pow_sub_one_le_four_mul_two_pow
    {tau B : ℕ} (htau : tau ≤ B + 2) :
    2 ^ tau - 1 ≤ 4 * 2 ^ B := by
  calc
    2 ^ tau - 1 ≤ 2 ^ tau := Nat.sub_le _ _
    _ ≤ 2 ^ (B + 2) := Nat.pow_le_pow_right (by omega) htau
    _ = 4 * 2 ^ B := by
      rw [pow_add]
      norm_num
      omega

/--
Finite weighted-summation step from the end of Theorem 10.1.
-/
theorem sum_two_pow_sub_one_le
    (population : Finset α) (tau : α → ℕ) (B : ℕ)
    (htau : ∀ z ∈ population, tau z ≤ B + 2) :
    (∑ z ∈ population, (2 ^ tau z - 1)) ≤
      population.card * (4 * 2 ^ B) := by
  exact sum_le_card_mul population
    (fun z ↦ 2 ^ tau z - 1) (4 * 2 ^ B)
    (fun z hz ↦ two_pow_sub_one_le_four_mul_two_pow (htau z hz))

end ResidualWeights

end TerminalClosureCounting
end PaperC
