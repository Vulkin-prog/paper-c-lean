import PaperC.Combinatorics.LargeKernelAssignments

/-!
# Large-prime assignments for unrestricted full-value relations

The assignment mechanism only uses the valuation equation at a large prime,
together with the fact that such a prime occurs at most once in each short
block. The coefficients below need not be boundaries of start relations and
need not have even parity in either block.

The final wrappers place the opposite start in the retained CRT assignment
classes. They assume equations at all primes, so no finite-cylinder cutoff
is needed. The large-kernel support may be empty; its empty assignment is
already included in the retained assignment classes.
-/

namespace PaperC.V282.FullPrimeAssignment

open Affine
open LargeKernelAssignments
open scoped BigOperators

noncomputable section

/-- A large prime isolates its selected term in one block. -/
theorem sum_eq_selected
    {x L p : ℕ} (hx : 1 ≤ x) (hpL : L + 1 < p)
    (c : Fin (L + 1) → F₂) (v : Fin (L + 1))
    (hv : parityVec (startCompleteVertexLabel x L v) p ≠ 0) :
    (∑ w : Fin (L + 1), c w * parityVec (startCompleteVertexLabel x L w) p) =
      c v * parityVec (startCompleteVertexLabel x L v) p := by
  classical
  apply Finset.sum_eq_single v
  · intro w _hw hwv
    have hzero : parityVec (startCompleteVertexLabel x L w) p = 0 := by
      by_contra hw
      exact hwv (RelationalPrimeAssignment.parityVec_ne_zero_unique_in_start
        hx hpL hw hv)
    simp [hzero]
  · simp

/-- One valuation equation forces the unique selected occurrence in the other block. -/
theorem existsUnique_selected_opposite_of_prime_equation
    {x y L p : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y) (hpL : L + 1 < p)
    (cLeft cRight : Fin (L + 1) → F₂)
    (heq : (∑ w, cLeft w * parityVec (startCompleteVertexLabel x L w) p) +
      (∑ w, cRight w * parityVec (startCompleteVertexLabel y L w) p) = 0)
    (v : Fin (L + 1)) (hvSelected : cLeft v ≠ 0)
    (hvParity : parityVec (startCompleteVertexLabel x L v) p ≠ 0) :
    ∃! w : Fin (L + 1), cRight w ≠ 0 ∧
      parityVec (startCompleteVertexLabel y L w) p ≠ 0 := by
  classical
  have hleftNe :
      (∑ w, cLeft w * parityVec (startCompleteVertexLabel x L w) p) ≠ 0 := by
    rw [sum_eq_selected hx hpL cLeft v hvParity]
    exact mul_ne_zero hvSelected hvParity
  have hrightNe :
      (∑ w, cRight w * parityVec (startCompleteVertexLabel y L w) p) ≠ 0 := by
    intro hzero
    rw [hzero, add_zero] at heq
    exact hleftNe heq
  obtain ⟨w, _hw, hwTerm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hrightNe
  refine ⟨w, ⟨left_ne_zero_of_mul hwTerm, right_ne_zero_of_mul hwTerm⟩, ?_⟩
  intro w' hw'
  exact RelationalPrimeAssignment.parityVec_ne_zero_unique_in_start
    hy hpL hw'.2 (right_ne_zero_of_mul hwTerm)

/-- A full-value coefficient on the left forces a selected occurrence on the right. -/
theorem existsUnique_opposite_of_left
    {x y L p : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y) (hpL : L + 1 < p)
    (c : Sum (Fin (L + 1)) (Fin (L + 1)) → F₂)
    (heq : ∑ i, c i * parityVec (twoStartCompleteVertexLabel x y L i) p = 0)
    (v : Fin (L + 1)) (hvSelected : c (Sum.inl v) ≠ 0)
    (hvParity : parityVec (startCompleteVertexLabel x L v) p ≠ 0) :
    ∃! w : Fin (L + 1), c (Sum.inr w) ≠ 0 ∧
      parityVec (startCompleteVertexLabel y L w) p ≠ 0 := by
  apply existsUnique_selected_opposite_of_prime_equation hx hy hpL
    (fun w => c (Sum.inl w)) (fun w => c (Sum.inr w)) ?_ v hvSelected hvParity
  simpa only [Fintype.sum_sum_type, twoStartCompleteVertexLabel] using heq

/-- The symmetric right-to-left consequence of the same valuation equation. -/
theorem existsUnique_opposite_of_right
    {x y L p : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y) (hpL : L + 1 < p)
    (c : Sum (Fin (L + 1)) (Fin (L + 1)) → F₂)
    (heq : ∑ i, c i * parityVec (twoStartCompleteVertexLabel x y L i) p = 0)
    (v : Fin (L + 1)) (hvSelected : c (Sum.inr v) ≠ 0)
    (hvParity : parityVec (startCompleteVertexLabel y L v) p ≠ 0) :
    ∃! w : Fin (L + 1), c (Sum.inl w) ≠ 0 ∧
      parityVec (startCompleteVertexLabel x L w) p ≠ 0 := by
  apply existsUnique_selected_opposite_of_prime_equation hy hx hpL
    (fun w => c (Sum.inr w)) (fun w => c (Sum.inl w)) ?_ v hvSelected hvParity
  rw [add_comm]
  simpa only [Fintype.sum_sum_type, twoStartCompleteVertexLabel] using heq

/-- Every prime of a selected left value's large odd kernel has a unique partner. -/
theorem existsUnique_opposite_for_largeKernel_of_left
    {x y L : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (c : Sum (Fin (L + 1)) (Fin (L + 1)) → F₂)
    (hEq : ∀ p : ℕ, p.Prime →
      ∑ i, c i * parityVec (twoStartCompleteVertexLabel x y L i) p = 0)
    (v : Fin (L + 1)) (hvSelected : c (Sum.inl v) ≠ 0)
    {p : ℕ} (hpSupport : p ∈ LargeOddKernel.largeOddPrimeSupport (L + 1)
      (startCompleteVertexLabel x L v)) :
    ∃! w : Fin (L + 1), c (Sum.inr w) ≠ 0 ∧
      parityVec (startCompleteVertexLabel y L w) p ≠ 0 := by
  have hpData := LargeOddKernel.prime_and_large_of_mem_largeOddPrimeSupport hpSupport
  exact existsUnique_opposite_of_left hx hy hpData.2 c (hEq p hpData.1)
    v hvSelected (LargeOddKernel.mem_largeOddPrimeSupport_iff.mp hpSupport).2

/-- The symmetric large-kernel partner statement for a selected right value. -/
theorem existsUnique_opposite_for_largeKernel_of_right
    {x y L : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (c : Sum (Fin (L + 1)) (Fin (L + 1)) → F₂)
    (hEq : ∀ p : ℕ, p.Prime →
      ∑ i, c i * parityVec (twoStartCompleteVertexLabel x y L i) p = 0)
    (v : Fin (L + 1)) (hvSelected : c (Sum.inr v) ≠ 0)
    {p : ℕ} (hpSupport : p ∈ LargeOddKernel.largeOddPrimeSupport (L + 1)
      (startCompleteVertexLabel y L v)) :
    ∃! w : Fin (L + 1), c (Sum.inl w) ≠ 0 ∧
      parityVec (startCompleteVertexLabel x L w) p ≠ 0 := by
  have hpData := LargeOddKernel.prime_and_large_of_mem_largeOddPrimeSupport hpSupport
  exact existsUnique_opposite_of_right hx hy hpData.2 c (hEq p hpData.1)
    v hvSelected (LargeOddKernel.mem_largeOddPrimeSupport_iff.mp hpSupport).2

/-- A selected left coefficient puts the right start in the retained CRT cover. -/
theorem right_mem_startsForSomeAssignment_of_selected_left
    {N L x y : ℕ} (hN : 2 ≤ N)
    (hx : x ∈ dyadicBlock N) (hy : y ∈ dyadicBlock N)
    (c : Sum (Fin (L + 1)) (Fin (L + 1)) → F₂)
    (hEq : ∀ p : ℕ, p.Prime →
      ∑ i, c i * parityVec (twoStartCompleteVertexLabel x y L i) p = 0)
    (v : Fin (L + 1)) (hvSelected : c (Sum.inl v) ≠ 0) :
    y ∈ startsForSomeAssignment N L (startCompleteVertexLabel x L v) := by
  classical
  have hxOne : 1 ≤ x := one_le_two.trans (two_le_of_mem_dyadicBlock hN hx)
  have hyOne : 1 ≤ y := one_le_two.trans (two_le_of_mem_dyadicBlock hN hy)
  let assignment : LargePrimeAssignment L (startCompleteVertexLabel x L v) :=
    fun p => Classical.choose
      (existsUnique_opposite_for_largeKernel_of_left hxOne hyOne c hEq v hvSelected p.2)
  rw [mem_startsForSomeAssignment]
  refine ⟨assignment, ?_⟩
  rw [mem_startsForAssignment]
  refine ⟨hy, ?_⟩
  intro p
  exact (Classical.choose_spec
    (existsUnique_opposite_for_largeKernel_of_left hxOne hyOne c hEq v hvSelected p.2)).1.2

/-- A selected right coefficient puts the left start in the retained CRT cover. -/
theorem left_mem_startsForSomeAssignment_of_selected_right
    {N L x y : ℕ} (hN : 2 ≤ N)
    (hx : x ∈ dyadicBlock N) (hy : y ∈ dyadicBlock N)
    (c : Sum (Fin (L + 1)) (Fin (L + 1)) → F₂)
    (hEq : ∀ p : ℕ, p.Prime →
      ∑ i, c i * parityVec (twoStartCompleteVertexLabel x y L i) p = 0)
    (v : Fin (L + 1)) (hvSelected : c (Sum.inr v) ≠ 0) :
    x ∈ startsForSomeAssignment N L (startCompleteVertexLabel y L v) := by
  classical
  have hxOne : 1 ≤ x := one_le_two.trans (two_le_of_mem_dyadicBlock hN hx)
  have hyOne : 1 ≤ y := one_le_two.trans (two_le_of_mem_dyadicBlock hN hy)
  let assignment : LargePrimeAssignment L (startCompleteVertexLabel y L v) :=
    fun p => Classical.choose
      (existsUnique_opposite_for_largeKernel_of_right hxOne hyOne c hEq v hvSelected p.2)
  rw [mem_startsForSomeAssignment]
  refine ⟨assignment, ?_⟩
  rw [mem_startsForAssignment]
  refine ⟨hx, ?_⟩
  intro p
  exact (Classical.choose_spec
    (existsUnique_opposite_for_largeKernel_of_right hxOne hyOne c hEq v hvSelected p.2)).1.2

end
end PaperC.V282.FullPrimeAssignment
