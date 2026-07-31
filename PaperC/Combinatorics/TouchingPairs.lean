import PaperC.Model.FiniteRademacher
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Real.Basic

/-!
# Ordered touching pairs in a dyadic block

This file isolates the finite combinatorics used in Lemma 3.4(ii).  A touching
pair is an ordered pair of starts in `I_N = [N,2N)` whose natural-number
distance is exactly `L`.

Every such pair has one of the two orientations

`(x, x + L)` or `(x + L, x)`.

Consequently there are at most two pairs per possible lower endpoint, hence
at most `2 * N` ordered touching pairs.  The final lemmas turn a pointwise
weight bound into natural- and real-valued sum bounds.
-/

namespace PaperC
namespace TouchingPairs

open scoped BigOperators

/-- Ordered pairs `(x,y) ∈ I_N²` at distance exactly `L`. -/
def touchingPairs (N L : ℕ) : Finset (ℕ × ℕ) :=
  ((dyadicBlock N) ×ˢ (dyadicBlock N)).filter
    (fun pair ↦ Nat.dist pair.1 pair.2 = L)

@[simp]
theorem mem_touchingPairs {N L x y : ℕ} :
    (x, y) ∈ touchingPairs N L ↔
      x ∈ dyadicBlock N ∧ y ∈ dyadicBlock N ∧ Nat.dist x y = L := by
  simp only [touchingPairs, Finset.mem_filter, Finset.mem_product]
  tauto

/--
The two possible orientations of a pair at natural-number distance `L`.
This statement also covers `L = 0`, when both alternatives reduce to the
diagonal.
-/
theorem eq_add_or_eq_add_of_dist_eq
    {x y L : ℕ} (hdist : Nat.dist x y = L) :
    y = x + L ∨ x = y + L := by
  by_cases hxy : x ≤ y
  · left
    rw [Nat.dist_eq_sub_of_le hxy] at hdist
    omega
  · right
    have hyx : y ≤ x := Nat.le_of_not_ge hxy
    rw [Nat.dist_eq_sub_of_le_right hyx] at hdist
    omega

/-- Under the positive-length hypothesis of Lemma 3.4, touching pairs are
automatically off the diagonal, exactly as required by the manuscript. -/
theorem fst_ne_snd_of_mem
    {N L : ℕ} {pair : ℕ × ℕ} (hL : 0 < L)
    (hpair : pair ∈ touchingPairs N L) :
    pair.1 ≠ pair.2 := by
  intro heq
  have hdist := (mem_touchingPairs.mp hpair).2.2
  rw [heq, Nat.dist_self] at hdist
  omega

/-- Forward-oriented candidate pairs, without imposing the upper endpoint
membership condition.  This deliberate enlargement makes the cardinal bound
immediate. -/
def forwardCandidates (N L : ℕ) : Finset (ℕ × ℕ) :=
  (dyadicBlock N).image (fun x ↦ (x, x + L))

/-- Backward-oriented candidate pairs. -/
def backwardCandidates (N L : ℕ) : Finset (ℕ × ℕ) :=
  (dyadicBlock N).image (fun x ↦ (x + L, x))

theorem touchingPairs_subset_candidates (N L : ℕ) :
    touchingPairs N L ⊆
      forwardCandidates N L ∪ backwardCandidates N L := by
  intro pair hpair
  obtain ⟨hx, hy, hdist⟩ := mem_touchingPairs.mp hpair
  rcases eq_add_or_eq_add_of_dist_eq hdist with hforward | hbackward
  · apply Finset.mem_union_left
    rw [forwardCandidates, Finset.mem_image]
    exact ⟨pair.1, hx, by
      apply Prod.ext
      · rfl
      · exact hforward.symm⟩
  · apply Finset.mem_union_right
    rw [backwardCandidates, Finset.mem_image]
    exact ⟨pair.2, hy, by
      apply Prod.ext
      · exact hbackward.symm
      · rfl⟩

theorem card_forwardCandidates_le (N L : ℕ) :
    (forwardCandidates N L).card ≤ (dyadicBlock N).card := by
  exact Finset.card_image_le

theorem card_backwardCandidates_le (N L : ℕ) :
    (backwardCandidates N L).card ≤ (dyadicBlock N).card := by
  exact Finset.card_image_le

/-- At most two ordered touching pairs per element of the dyadic block. -/
theorem card_touchingPairs_le_two_mul_card (N L : ℕ) :
    (touchingPairs N L).card ≤ 2 * (dyadicBlock N).card := by
  calc
    (touchingPairs N L).card ≤
        (forwardCandidates N L ∪ backwardCandidates N L).card :=
      Finset.card_le_card (touchingPairs_subset_candidates N L)
    _ ≤ (forwardCandidates N L).card +
        (backwardCandidates N L).card :=
      Finset.card_union_le _ _
    _ ≤ (dyadicBlock N).card + (dyadicBlock N).card :=
      Nat.add_le_add
        (card_forwardCandidates_le N L)
        (card_backwardCandidates_le N L)
    _ = 2 * (dyadicBlock N).card := by omega

@[simp]
theorem card_dyadicBlock (N : ℕ) :
    (dyadicBlock N).card = N := by
  simp [dyadicBlock]
  omega

/-- Explicit form used in Lemma 3.4(ii). -/
theorem card_touchingPairs_le_two_mul (N L : ℕ) :
    (touchingPairs N L).card ≤ 2 * N := by
  simpa using card_touchingPairs_le_two_mul_card N L

/-- A pointwise natural weight bound gives a cardinality-times-weight bound. -/
theorem sum_nat_le_card_mul
    (N L W : ℕ) (weight : ℕ × ℕ → ℕ)
    (hweight : ∀ pair ∈ touchingPairs N L, weight pair ≤ W) :
    ∑ pair ∈ touchingPairs N L, weight pair ≤
      (touchingPairs N L).card * W := by
  calc
    ∑ pair ∈ touchingPairs N L, weight pair ≤
        ∑ _pair ∈ touchingPairs N L, W :=
      Finset.sum_le_sum fun pair hpair ↦ hweight pair hpair
    _ = (touchingPairs N L).card * W := by simp

/-- Natural-valued specialization using the explicit `2N` pair count. -/
theorem sum_nat_le_two_mul
    (N L W : ℕ) (weight : ℕ × ℕ → ℕ)
    (hweight : ∀ pair ∈ touchingPairs N L, weight pair ≤ W) :
    ∑ pair ∈ touchingPairs N L, weight pair ≤
      (2 * N) * W := by
  exact (sum_nat_le_card_mul N L W weight hweight).trans
    (Nat.mul_le_mul_right W (card_touchingPairs_le_two_mul N L))

/-- A pointwise real weight bound gives a cardinality-times-weight bound. -/
theorem sum_real_le_card_mul
    (N L : ℕ) (W : ℝ) (weight : ℕ × ℕ → ℝ)
    (hweight : ∀ pair ∈ touchingPairs N L, weight pair ≤ W) :
    ∑ pair ∈ touchingPairs N L, weight pair ≤
      ((touchingPairs N L).card : ℝ) * W := by
  calc
    ∑ pair ∈ touchingPairs N L, weight pair ≤
        ∑ _pair ∈ touchingPairs N L, W :=
      Finset.sum_le_sum fun pair hpair ↦ hweight pair hpair
    _ = ((touchingPairs N L).card : ℝ) * W := by simp

/-- Real-valued specialization using the explicit `2N` pair count. -/
theorem sum_real_le_two_mul
    (N L : ℕ) (W : ℝ) (weight : ℕ × ℕ → ℝ)
    (hW : 0 ≤ W)
    (hweight : ∀ pair ∈ touchingPairs N L, weight pair ≤ W) :
    ∑ pair ∈ touchingPairs N L, weight pair ≤
      (2 * N : ℝ) * W := by
  refine (sum_real_le_card_mul N L W weight hweight).trans ?_
  gcongr
  exact_mod_cast card_touchingPairs_le_two_mul N L

end TouchingPairs
end PaperC
