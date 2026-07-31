import PaperC.Combinatorics.LargePrimeComponents
import PaperC.Combinatorics.PinnedGraphResolution

set_option maxHeartbeats 1600000

/-!
# Resolution of the concrete large-prime graph

This module specializes `PinnedGraphResolution` to the graph
`G_{>B}(x,y)` and the space `W_{>B}(x,y)` from Section 6.  It provides the
canonical linear equivalence with one binary parameter per unpinned
component, the exact dimension formula `D+c`, and the vertex-budget bound
`D+2c ≤ 2(L+1)`.
-/

namespace PaperC
namespace LargePrimeGraphResolution

open LargePrimeOccurrences
open LargePrimeGraph
open PinnedGraphResolution

noncomputable section

noncomputable local instance instDecidableLargePrimeAdj
    (x y L : ℕ) :
    DecidableRel (largePrimeGraph x y L).Adj :=
  Classical.decRel _

/-- The finite set of vertices pinned by at least one large prime. -/
noncomputable def pinnedVertices
    (x y L : ℕ) : Finset (Occurrence L) := by
  classical
  exact Finset.univ.filter (IsPinned x y L)

@[simp]
theorem mem_pinnedVertices
    {x y L : ℕ} {v : Occurrence L} :
    v ∈ pinnedVertices x y L ↔
      IsPinned x y L v := by
  classical
  simp [pinnedVertices]

/--
The occurrence equations defining `W_{>B}` are exactly the pinned-graph
equations.
-/
theorem largePrimeSolution_eq_pinnedGraphSpace
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) :
    largePrimeSolution x y L =
      PinnedGraphSpace
        (largePrimeGraph x y L)
        (pinnedVertices x y L) := by
  ext u
  rw [mem_largePrimeSolution_iff_graph_rules hx hy]
  rw [mem_pinnedGraphSpace]
  constructor
  · rintro ⟨hedge, hpin⟩
    exact
      ⟨hedge, fun v hv ↦
        hpin (mem_pinnedVertices.mp hv)⟩
  · rintro ⟨hedge, hpin⟩
    exact
      ⟨hedge, fun v hv ↦
        hpin v (mem_pinnedVertices.mpr hv)⟩

/--
Lemma 6.1: canonical resolution of `W_{>B}` by its unpinned connected
components.
-/
noncomputable def largePrimeSolutionLinearEquiv
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) :
    largePrimeSolution x y L ≃ₗ[F₂]
      (UnpinnedComponent
          (largePrimeGraph x y L)
          (pinnedVertices x y L) → F₂) :=
  (LinearEquiv.ofEq _ _
      (largePrimeSolution_eq_pinnedGraphSpace hx hy)).trans
    (pinnedGraphLinearEquiv
      (largePrimeGraph x y L)
      (pinnedVertices x y L))

/-- `D`: the number of isolated unpinned components. -/
noncomputable def defectiveComponentCount
    (x y L : ℕ) : ℕ :=
  (isolatedUnpinnedComponents
    (largePrimeGraph x y L)
    (pinnedVertices x y L)).card

/-- `c`: the number of nontrivial unpinned components. -/
noncomputable def nontrivialComponentCount
    (x y L : ℕ) : ℕ :=
  (nontrivialUnpinnedComponents
    (largePrimeGraph x y L)
    (pinnedVertices x y L)).card

/-- Exact dimension formula `dim W_{>B}=D+c`. -/
theorem finrank_largePrimeSolution
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) :
    Module.finrank F₂ (largePrimeSolution x y L) =
      defectiveComponentCount x y L +
        nontrivialComponentCount x y L := by
  rw [largePrimeSolution_eq_pinnedGraphSpace hx hy]
  rw [finrank_pinnedGraphSpace]
  rw [card_unpinnedComponent_eq_isolated_add_nontrivial]
  rfl

/-- The two complete boundaries contain exactly `2(L+1)` occurrences. -/
theorem card_occurrence (L : ℕ) :
    Fintype.card (Occurrence L) = 2 * (L + 1) := by
  simp [Occurrence]
  omega

/-- Vertex budget from Lemma 6.1: `D+2c≤2B`, with `B=L+1`. -/
theorem defective_add_twice_nontrivial_le
    (x y L : ℕ) :
    defectiveComponentCount x y L +
        2 * nontrivialComponentCount x y L ≤
      2 * (L + 1) := by
  have hbound :=
    card_isolated_add_twice_card_nontrivial_le
      (largePrimeGraph x y L)
      (pinnedVertices x y L)
  rw [card_occurrence] at hbound
  exact hbound

/-! ## Identification of `D` with defective vertices -/

/-- The finite set of vertices carrying no large odd prime. -/
noncomputable def defectiveVertices
    (x y L : ℕ) : Finset (Occurrence L) := by
  classical
  exact Finset.univ.filter (IsDefective x y L)

@[simp]
theorem mem_defectiveVertices
    {x y L : ℕ} {v : Occurrence L} :
    v ∈ defectiveVertices x y L ↔
      IsDefective x y L v := by
  classical
  simp [defectiveVertices]

/-- The manuscript's literal defective-vertex count. -/
noncomputable def defectiveVertexCount
    (x y L : ℕ) : ℕ :=
  (defectiveVertices x y L).card

/--
If no edge leaves `v`, every vertex reachable from `v` is `v` itself.
-/
theorem eq_of_reachable_of_no_adj
    {V : Type*} {G : SimpleGraph V}
    {v w : V}
    (hisolated : ∀ z : V, ¬G.Adj v z)
    (hreach : G.Reachable v w) :
    w = v := by
  apply hreach.elim
  intro walk
  cases walk with
  | nil => rfl
  | cons hvz walk =>
      exact (hisolated _ hvz).elim

/-- A defective vertex generates an isolated unpinned component. -/
theorem isIsolatedUnpinnedComponent_of_isDefective
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    {v : Occurrence L}
    (hv : IsDefective x y L v) :
    IsIsolatedUnpinnedComponent
      (largePrimeGraph x y L)
      (pinnedVertices x y L)
      ((largePrimeGraph x y L).connectedComponentMk v) := by
  constructor
  · rintro ⟨w, hwPin, hwComponent⟩
    have hreach :
        (largePrimeGraph x y L).Reachable v w :=
      SimpleGraph.ConnectedComponent.exact
        hwComponent.symm
    have hwv :
        w = v :=
      eq_of_reachable_of_no_adj
        (not_adj_of_isDefective hv) hreach
    have hvNotPinned :=
      not_isPinned_of_isDefective hv
    exact hvNotPinned
      (hwv ▸ mem_pinnedVertices.mp hwPin)
  · rw [Fintype.card_eq_one_iff]
    let vIn :
        ((largePrimeGraph x y L).connectedComponentMk v).supp :=
      ⟨v,
        SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩
    refine ⟨vIn, ?_⟩
    intro wIn
    apply Subtype.ext
    have hcomponent :
        (largePrimeGraph x y L).connectedComponentMk wIn.1 =
          (largePrimeGraph x y L).connectedComponentMk v := by
      simpa only [
        SimpleGraph.ConnectedComponent.mem_supp_iff]
        using wIn.2
    have hreach :
        (largePrimeGraph x y L).Reachable v wIn.1 :=
      SimpleGraph.ConnectedComponent.exact
        hcomponent.symm
    exact
      eq_of_reachable_of_no_adj
        (not_adj_of_isDefective hv) hreach

/-- An isolated unpinned component representative is a defective vertex. -/
theorem isDefective_of_isolatedUnpinnedComponent
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    {C : (largePrimeGraph x y L).ConnectedComponent}
    (hC :
      IsIsolatedUnpinnedComponent
        (largePrimeGraph x y L)
        (pinnedVertices x y L) C) :
    IsDefective x y L C.out := by
  apply isDefective_of_not_isPinned_of_isolated hx hy
  · intro hpin
    apply hC.1
    exact
      ⟨C.out, mem_pinnedVertices.mpr hpin,
        C.out_eq⟩
  · intro w hadj
    have hcomponent :
        (largePrimeGraph x y L).connectedComponentMk w = C := by
      calc
        (largePrimeGraph x y L).connectedComponentMk w =
            (largePrimeGraph x y L).connectedComponentMk C.out :=
          SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
            hadj.symm
        _ = C := C.out_eq
    have hOutMem : C.out ∈ C.supp := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      exact C.out_eq
    have hwMem : w ∈ C.supp := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      exact hcomponent
    obtain ⟨root, hroot⟩ :=
      Fintype.card_eq_one_iff.mp hC.2
    have heq :
        (⟨C.out, hOutMem⟩ : C.supp) =
          ⟨w, hwMem⟩ := by
      exact (hroot _).trans (hroot _).symm
    exact hadj.ne (congrArg Subtype.val heq)

/--
Defective vertices and isolated unpinned components are canonically
equivalent.
-/
noncomputable def defectiveVerticesEquivIsolatedComponents
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) :
    {v // v ∈ defectiveVertices x y L} ≃
      {C // C ∈
        isolatedUnpinnedComponents
          (largePrimeGraph x y L)
          (pinnedVertices x y L)} where
  toFun v :=
    ⟨(largePrimeGraph x y L).connectedComponentMk v.1,
      (mem_isolatedUnpinnedComponents
        (largePrimeGraph x y L)).mpr
        (isIsolatedUnpinnedComponent_of_isDefective
          hx hy (mem_defectiveVertices.mp v.2))⟩
  invFun C :=
    ⟨C.1.out,
      mem_defectiveVertices.mpr
        (isDefective_of_isolatedUnpinnedComponent
          hx hy
          ((mem_isolatedUnpinnedComponents
            (largePrimeGraph x y L)).mp C.2))⟩
  left_inv := by
    intro v
    apply Subtype.ext
    have hreach :
        (largePrimeGraph x y L).Reachable
          v.1
          ((largePrimeGraph x y L).connectedComponentMk v.1).out :=
      SimpleGraph.ConnectedComponent.exact
        ((largePrimeGraph x y L).connectedComponentMk v.1).out_eq.symm
    exact
      eq_of_reachable_of_no_adj
        (not_adj_of_isDefective
          (mem_defectiveVertices.mp v.2))
        hreach
  right_inv := by
    intro C
    apply Subtype.ext
    exact C.1.out_eq

/-- The two definitions of `D` have exactly the same cardinality. -/
theorem defectiveVertexCount_eq_defectiveComponentCount
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) :
    defectiveVertexCount x y L =
      defectiveComponentCount x y L := by
  have hcard :=
    Fintype.card_congr
      (defectiveVerticesEquivIsolatedComponents
        (L := L) hx hy)
  simpa [defectiveVertexCount, defectiveComponentCount]
    using hcard

/-- Lemma 6.1 with `D` stated literally as the number of defective vertices. -/
theorem finrank_largePrimeSolution_eq_defective_add_components
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) :
    Module.finrank F₂ (largePrimeSolution x y L) =
      defectiveVertexCount x y L +
        nontrivialComponentCount x y L := by
  rw [finrank_largePrimeSolution hx hy,
    ← defectiveVertexCount_eq_defectiveComponentCount hx hy]

/-- Literal form of the vertex budget `D+2c≤2B`. -/
theorem defectiveVertex_add_twice_nontrivial_le
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) :
    defectiveVertexCount x y L +
        2 * nontrivialComponentCount x y L ≤
      2 * (L + 1) := by
  rw [defectiveVertexCount_eq_defectiveComponentCount hx hy]
  exact defective_add_twice_nontrivial_le x y L

end

end LargePrimeGraphResolution
end PaperC
