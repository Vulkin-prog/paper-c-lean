import PaperCV282.FullPrimeAssignment
import PaperC.Combinatorics.BoundedRatioRelationalHosts

/-!
# Full-value assignments on arbitrary positive intervals

The large-prime equations of an unrestricted full-value coefficient vector
place the opposite start in the retained interval CRT classes. Only positive
starts are needed: neither block parity, a finite prime cutoff, a bound on
the endpoint ratio, nor a comparison of the window length with the lower
endpoint enters these wrappers.
-/

namespace PaperC.V282.FullIntervalPrimeAssignment

open Affine BoundedRatioGeometry
open scoped BigOperators

noncomputable section

/-- A selected left value places the right start in the interval assignment cover. -/
theorem right_mem_boundedAssignment_of_selected_left
    {A Z L x y : ℕ} (hA : 2 ≤ A)
    (hx : x ∈ boundedRatioBlock A Z) (hy : y ∈ boundedRatioBlock A Z)
    (c : Sum (Fin (L + 1)) (Fin (L + 1)) → F₂)
    (hEq : ∀ p : ℕ, p.Prime →
      ∑ i, c i * parityVec (twoStartCompleteVertexLabel x y L i) p = 0)
    (v : Fin (L + 1)) (hvSelected : c (Sum.inl v) ≠ 0) :
    y ∈ BoundedRatioRelationalHosts.startsForSomeAssignment A Z L
      (startCompleteVertexLabel x L v) := by
  classical
  have hxOne : 1 ≤ x := one_le_two.trans (hA.trans (mem_boundedRatioBlock.mp hx).1)
  have hyOne : 1 ≤ y := one_le_two.trans (hA.trans (mem_boundedRatioBlock.mp hy).1)
  let assignment : LargeKernelAssignments.LargePrimeAssignment L
      (startCompleteVertexLabel x L v) :=
    fun p => Classical.choose
      (FullPrimeAssignment.existsUnique_opposite_for_largeKernel_of_left
        hxOne hyOne c hEq v hvSelected p.2)
  rw [BoundedRatioRelationalHosts.mem_startsForSomeAssignment]
  refine ⟨assignment, ?_⟩
  rw [BoundedRatioRelationalHosts.mem_startsForAssignment]
  refine ⟨hy, ?_⟩
  intro p
  exact (Classical.choose_spec
    (FullPrimeAssignment.existsUnique_opposite_for_largeKernel_of_left
      hxOne hyOne c hEq v hvSelected p.2)).1.2

/-- The symmetric interval cover for a selected right value. -/
theorem left_mem_boundedAssignment_of_selected_right
    {A Z L x y : ℕ} (hA : 2 ≤ A)
    (hx : x ∈ boundedRatioBlock A Z) (hy : y ∈ boundedRatioBlock A Z)
    (c : Sum (Fin (L + 1)) (Fin (L + 1)) → F₂)
    (hEq : ∀ p : ℕ, p.Prime →
      ∑ i, c i * parityVec (twoStartCompleteVertexLabel x y L i) p = 0)
    (v : Fin (L + 1)) (hvSelected : c (Sum.inr v) ≠ 0) :
    x ∈ BoundedRatioRelationalHosts.startsForSomeAssignment A Z L
      (startCompleteVertexLabel y L v) := by
  classical
  have hxOne : 1 ≤ x := one_le_two.trans (hA.trans (mem_boundedRatioBlock.mp hx).1)
  have hyOne : 1 ≤ y := one_le_two.trans (hA.trans (mem_boundedRatioBlock.mp hy).1)
  let assignment : LargeKernelAssignments.LargePrimeAssignment L
      (startCompleteVertexLabel y L v) :=
    fun p => Classical.choose
      (FullPrimeAssignment.existsUnique_opposite_for_largeKernel_of_right
        hxOne hyOne c hEq v hvSelected p.2)
  rw [BoundedRatioRelationalHosts.mem_startsForSomeAssignment]
  refine ⟨assignment, ?_⟩
  rw [BoundedRatioRelationalHosts.mem_startsForAssignment]
  refine ⟨hx, ?_⟩
  intro p
  exact (Classical.choose_spec
    (FullPrimeAssignment.existsUnique_opposite_for_largeKernel_of_right
      hxOne hyOne c hEq v hvSelected p.2)).1.2

end
end PaperC.V282.FullIntervalPrimeAssignment
