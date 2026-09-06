import PaperCV282.AllStartConditionalDependency
import PaperCV282.CutoffGraphDegree

/-!
# The actual all-site graph and the arithmetic degree

The natural-number neighbor set and the graph on the dyadic subtype are
identified exactly. In particular the full closed neighborhood has one
more vertex than the arithmetic open neighbor set. This uses all sites,
including defective starts, with no change to the conditional indicators.
-/

namespace PaperC.V282.CutoffGraphCompatibility

open AllStartConditionalDependency CutoffGraphDegree ArratiaGoldsteinGordonInput
open LargePrimeDependencyGraph

noncomputable section

/-- Forgetting the subtype identifies the open graph neighborhood exactly. -/
theorem openNeighborhood_image_eq_cutoffNeighbors {N L Y : ℕ}
    (x : {x : ℕ // x ∈ dyadicBlock N}) :
    ((closedNeighborhood (allStartDependencyGraph N L Y) x).erase x).image Subtype.val =
      cutoffNeighbors L Y (dyadicBlock N) x.val := by
  classical
  ext y
  simp only [Finset.mem_image,Finset.mem_erase,mem_closedNeighborhood,
    allStartDependencyGraph_adj,mem_cutoffNeighbors]
  constructor
  · rintro ⟨z,⟨hne,heq | hadj⟩,rfl⟩
    · exact False.elim (hne heq)
    · exact ⟨z.property,hadj⟩
  · rintro ⟨hy,hadj⟩
    refine ⟨⟨y,hy⟩,⟨?_,Or.inr hadj⟩,rfl⟩
    intro heq
    exact hadj.1 (congrArg Subtype.val heq).symm

/-- The closed graph neighborhood adds exactly the chosen site. -/
theorem closedNeighborhood_image_eq_insert_cutoffNeighbors {N L Y : ℕ}
    (x : {x : ℕ // x ∈ dyadicBlock N}) :
    (closedNeighborhood (allStartDependencyGraph N L Y) x).image Subtype.val =
      insert x.val (cutoffNeighbors L Y (dyadicBlock N) x.val) := by
  classical
  rw [← Finset.insert_erase (self_mem_closedNeighborhood (allStartDependencyGraph N L Y) x),
    Finset.image_insert,openNeighborhood_image_eq_cutoffNeighbors]

/-- Exact agreement of the two open degree counts. -/
theorem card_openNeighborhood_eq_cutoffNeighbors {N L Y : ℕ}
    (x : {x : ℕ // x ∈ dyadicBlock N}) :
    ((closedNeighborhood (allStartDependencyGraph N L Y) x).erase x).card =
      (cutoffNeighbors L Y (dyadicBlock N) x.val).card := by
  rw [← openNeighborhood_image_eq_cutoffNeighbors x]
  exact (Finset.card_image_of_injective _ Subtype.val_injective).symm

/-- The closed-neighborhood cardinal is the actual open degree plus one. -/
theorem card_closedNeighborhood_eq_cutoffNeighbors_add_one {N L Y : ℕ}
    (x : {x : ℕ // x ∈ dyadicBlock N}) :
    (closedNeighborhood (allStartDependencyGraph N L Y) x).card =
      (cutoffNeighbors L Y (dyadicBlock N) x.val).card + 1 := by
  classical
  have hnot : x.val ∉ cutoffNeighbors L Y (dyadicBlock N) x.val := by
    intro hx
    exact not_largePrimeAdjacent_self L Y x.val (mem_cutoffNeighbors.mp hx).2
  have hcard := congrArg Finset.card (closedNeighborhood_image_eq_insert_cutoffNeighbors (L := L) (Y := Y) x)
  rw [Finset.card_image_of_injective _ Subtype.val_injective,Finset.card_insert_of_notMem hnot] at hcard
  exact hcard

/-- The genuine all-site graph meets the closed-degree premise for soft deletion. -/
theorem card_closedNeighborhood_le_maxDegree {N L Y : ℕ}
    (x : {x : ℕ // x ∈ dyadicBlock N}) :
    (closedNeighborhood (allStartDependencyGraph N L Y) x).card ≤
      cutoffMaxDegree L Y (dyadicBlock N) + 1 := by
  rw [card_closedNeighborhood_eq_cutoffNeighbors_add_one]
  exact Nat.add_le_add_right (Finset.le_sup (f := fun z =>
    (cutoffNeighbors L Y (dyadicBlock N) z).card) x.property) 1

/-- The finite arithmetic degree bound applies directly to the conditional graph. -/
theorem card_closedNeighborhood_cast_le {N L Y : ℕ}
    (hN : 2 ≤ N) (hL : L ≤ N) (hLY : L ≤ Y) (hY : 1 < Y)
    (x : {x : ℕ // x ∈ dyadicBlock N}) :
    ((closedNeighborhood (allStartDependencyGraph N L Y) x).card : ℝ) ≤
      (L + 1 : ℝ) ^ 2 * (Real.log (3 * N : ℕ) / Real.log Y) * ((N : ℝ) / Y + 1) + 1 := by
  rw [card_closedNeighborhood_eq_cutoffNeighbors_add_one,Nat.cast_add,Nat.cast_one]
  simpa only [add_comm] using add_le_add_right
    (card_cutoffNeighbors_le hN hL hLY hY (Finset.Subset.refl _) x.property) 1

end
end PaperC.V282.CutoffGraphCompatibility
