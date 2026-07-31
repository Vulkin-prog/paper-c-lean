import PaperC.Combinatorics.GraphCycleRank
import PaperC.LinearAlgebra.PrivatePivots
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Pi

/-!
# Dimension bound for the binary cycle space

This file closes the graph-theoretic dimension obligation left parametric in
`PaperC.Combinatorics.GraphCycleRank`.

An edge presentation consists of two endpoint maps `left right : E → V`.  We use the explicit
reflexive-transitive closure of the corresponding undirected adjacency relation.  The substantive
graph hypothesis is that every vertex is reachable from the chosen root of its component.

Under that hypothesis the incidence image contains the independent family

`1_v + 1_(root (component v))`

indexed by the non-root vertices.  Rank-nullity therefore gives

`finrank cycleSpace ≤ |E| - |V| + |C|`.

This is the inequality needed in Lemma 14.6.  Loops and parallel edges are allowed; connectivity,
rather than simplicity, is the essential hypothesis.
-/

namespace PaperC
namespace CycleSpaceDimension

open Fintype LinearMap Module
open GraphCycleRank

variable {V E C P : Type*}
variable [Fintype V] [DecidableEq V]
variable [Fintype E] [DecidableEq E]
variable [Fintype C] [DecidableEq C]
variable [Fintype P] [DecidableEq P]

/--
Rank-nullity with the dimension of a finite function space rewritten to its cardinality.
Keeping the linear map abstract here avoids expensive reduction of its concrete definition.
-/
private theorem finrank_range_add_finrank_ker_eq_card
    {ι M : Type*} [Fintype ι]
    [AddCommGroup M] [Module F₂ M]
    (f : (ι → F₂) →ₗ[F₂] M) :
    Module.finrank F₂ (LinearMap.range f) +
        Module.finrank F₂ (LinearMap.ker f) =
      Fintype.card ι := by
  calc
    Module.finrank F₂ (LinearMap.range f) +
          Module.finrank F₂ (LinearMap.ker f) =
        Module.finrank F₂ (ι → F₂) :=
      f.finrank_range_add_finrank_ker
    _ = Fintype.card ι := Module.finrank_pi F₂

/-- Two vertices are adjacent in the undirected graph presented by `left` and `right`. -/
def PresentedAdjacent (left right : E → V) (u v : V) : Prop :=
  ∃ e : E,
    (left e = u ∧ right e = v) ∨
    (left e = v ∧ right e = u)

/--
Reachability in an undirected edge presentation.  This custom closure keeps the multigraph edge
which witnesses each step available to the incidence calculation.
-/
inductive PresentedReachable (left right : E → V) : V → V → Prop
  | refl (v : V) : PresentedReachable left right v v
  | tail {u v w : V} :
      PresentedReachable left right u v →
      PresentedAdjacent left right v w →
      PresentedReachable left right u w

/-- The endpoint vector `1_u + 1_v`. -/
def endpointVector (u v : V) : V → F₂ :=
  Pi.single u 1 + Pi.single v 1

@[simp]
theorem endpointVector_self (v : V) :
    endpointVector v v = 0 := by
  ext w
  by_cases h : v = w <;>
    simp [endpointVector, Pi.single_apply, h] <;> decide

theorem endpointVector_add_endpointVector (u v w : V) :
    endpointVector u v + endpointVector v w = endpointVector u w := by
  ext z
  simp only [endpointVector, Pi.add_apply, Pi.single_apply, Pi.zero_apply]
  split_ifs <;> decide

/-- Every displayed edge vector belongs to the range of the incidence map. -/
theorem incidenceVector_mem_range
    (left right : E → V) (e : E) :
    incidenceVector left right e ∈ LinearMap.range (incidenceMap left right) := by
  refine ⟨Pi.single e 1, ?_⟩
  rw [incidenceMap, Fintype.linearCombination_apply_single, one_smul]

/-- An adjacency step contributes its endpoint vector to the incidence range. -/
theorem endpointVector_mem_range_of_adjacent
    (left right : E → V) {u v : V}
    (h : PresentedAdjacent left right u v) :
    endpointVector u v ∈ LinearMap.range (incidenceMap left right) := by
  obtain ⟨e, he | he⟩ := h
  · have hmem := incidenceVector_mem_range left right e
    simpa [endpointVector, incidenceVector, he.1, he.2] using hmem
  · have hmem := incidenceVector_mem_range left right e
    simpa [endpointVector, incidenceVector, he.1, he.2, add_comm] using hmem

/-- A path telescopes in characteristic two. -/
theorem endpointVector_mem_range_of_reachable
    (left right : E → V) {u v : V}
    (h : PresentedReachable left right u v) :
    endpointVector u v ∈ LinearMap.range (incidenceMap left right) := by
  induction h with
  | refl =>
      rw [endpointVector_self]
      exact (LinearMap.range (incidenceMap left right)).zero_mem
  | tail huv hvw ih =>
      rw [← endpointVector_add_endpointVector]
      exact (LinearMap.range (incidenceMap left right)).add_mem ih
        (endpointVector_mem_range_of_adjacent left right hvw)

/-- Vertices other than the distinguished root of their component. -/
abbrev NonRoot (component : V → C) (root : C → V) :=
  {v : V // v ≠ root (component v)}

/-- The independent endpoint vectors obtained by joining each non-root vertex to its root. -/
def rootedEndpointVector
    (component : V → C) (root : C → V)
    (v : NonRoot component root) : V → F₂ :=
  endpointVector v.1 (root (component v.1))

@[simp]
theorem rootedEndpointVector_apply_self
    (component : V → C) (root : C → V)
    (v : NonRoot component root) :
    rootedEndpointVector component root v v.1 = 1 := by
  simp [rootedEndpointVector, endpointVector, v.2]

theorem rootedEndpointVector_apply_ne
    (component : V → C) (root : C → V)
    (hroot : ∀ c : C, component (root c) = c)
    (v w : NonRoot component root) (hwv : w ≠ v) :
    rootedEndpointVector component root w v.1 = 0 := by
  have hwv' : w.1 ≠ v.1 := by
    intro h
    exact hwv (Subtype.ext h)
  have hrootne : root (component w.1) ≠ v.1 := by
    intro h
    have hc : component v.1 = component w.1 := by
      rw [← h]
      exact hroot (component w.1)
    apply v.2
    rw [hc, h]
  simp [rootedEndpointVector, endpointVector, hwv', hrootne]

/-- The root-to-vertex endpoint vectors are linearly independent. -/
theorem linearIndependent_rootedEndpointVector
    (component : V → C) (root : C → V)
    (hroot : ∀ c : C, component (root c) = c) :
    LinearIndependent F₂ (rootedEndpointVector component root) := by
  apply PrivatePivots.linearIndependent_of_private_pivots
    (R := F₂)
    (rootedEndpointVector component root)
    (fun v => (LinearMap.proj v.1 : (V → F₂) →ₗ[F₂] F₂))
  · intro v
    simp
  · intro v w hwv
    exact rootedEndpointVector_apply_ne component root hroot v w hwv

/-- Component labels are equivalent to the vertices selected as component roots. -/
def rootVertexEquiv
    (component : V → C) (root : C → V)
    (hroot : ∀ c : C, component (root c) = c) :
    C ≃ {v : V // v = root (component v)} where
  toFun c := ⟨root c, by simp [hroot c]⟩
  invFun v := component v.1
  left_inv c := hroot c
  right_inv v := by
    apply Subtype.ext
    exact v.2.symm

/-- There are exactly `|V| - |C|` non-root vertices. -/
theorem card_nonRoot
    (component : V → C) (root : C → V)
    (hroot : ∀ c : C, component (root c) = c) :
    Fintype.card (NonRoot component root) =
      Fintype.card V - Fintype.card C := by
  rw [Fintype.card_subtype_compl (fun v : V => v = root (component v))]
  congr 1
  exact Fintype.card_congr (rootVertexEquiv component root hroot).symm

/--
Connectivity to the selected component roots forces the incidence rank to be at least
`|V| - |C|`.
-/
theorem card_vertices_sub_components_le_finrank_incidenceRange
    (left right : E → V)
    (component : V → C) (root : C → V)
    (hroot : ∀ c : C, component (root c) = c)
    (hconnected :
      ∀ v : V, PresentedReachable left right (root (component v)) v) :
    Fintype.card V - Fintype.card C ≤
      Module.finrank F₂ (LinearMap.range (incidenceMap left right)) := by
  let b := rootedEndpointVector component root
  have hb : LinearIndependent F₂ b :=
    linearIndependent_rootedEndpointVector component root hroot
  have hspan :
      Submodule.span F₂ (Set.range b) ≤
        LinearMap.range (incidenceMap left right) := by
    rw [Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    have hpath := hconnected v.1
    have hmem :=
      endpointVector_mem_range_of_reachable left right hpath
    simpa [b, rootedEndpointVector, endpointVector, add_comm] using hmem
  rw [← card_nonRoot component root hroot, ← finrank_span_eq_card hb]
  exact Submodule.finrank_mono hspan

/--
The truncation-safe form of the cyclomatic bound.  The number of non-root vertices is
`|V| - |C|`, so rank-nullity gives nullity at most `|E| - (|V| - |C|)`.
-/
theorem finrank_cycleSpace_le_card_edges_sub_nonRoot
    (left right : E → V)
    (component : V → C) (root : C → V)
    (hroot : ∀ c : C, component (root c) = c)
    (hconnected :
      ∀ v : V, PresentedReachable left right (root (component v)) v) :
    Module.finrank F₂ (cycleSpace left right) ≤
      Fintype.card E - (Fintype.card V - Fintype.card C) := by
  have hrange :=
    card_vertices_sub_components_le_finrank_incidenceRange
      left right component root hroot hconnected
  have hnullity :
      Module.finrank F₂ (LinearMap.range (incidenceMap left right)) +
          Module.finrank F₂ (LinearMap.ker (incidenceMap left right)) =
        Fintype.card E := by
    exact finrank_range_add_finrank_ker_eq_card (incidenceMap left right)
  rw [cycleSpace]
  omega

/--
The required cyclomatic dimension bound for an arbitrary finite edge presentation.

The expression uses natural-number subtraction, matching the convention in
`GraphCycleRank`.  The root section ensures `|C| ≤ |V|`.
-/
theorem finrank_cycleSpace_le_cyclomaticNumber
    (left right : E → V)
    (component : V → C) (root : C → V)
    (hroot : ∀ c : C, component (root c) = c)
    (hconnected :
      ∀ v : V, PresentedReachable left right (root (component v)) v) :
    Module.finrank F₂ (cycleSpace left right) ≤
      Fintype.card E - Fintype.card V + Fintype.card C := by
  have hsafe :=
    finrank_cycleSpace_le_card_edges_sub_nonRoot
      left right component root hroot hconnected
  have hroot_injective : Function.Injective root := by
    intro c d hcd
    rw [← hroot c, ← hroot d, hcd]
  have hcardCV : Fintype.card C ≤ Fintype.card V :=
    Fintype.card_le_of_injective root hroot_injective
  omega

/--
Lemma 14.6, nullity form, with the graph connectivity hypothesis in place of the former
dimension hypothesis `hcycle`.
-/
theorem finrank_ker_representedEdgeMap_le_cyclomaticNumber
    (vertexVector : V → P → F₂) (left right : E → V)
    (component : V → C) (root : C → V)
    (hroot : ∀ c : C, component (root c) = c)
    (hedge : ∀ e : E, component (left e) = component (right e))
    (hconnected :
      ∀ v : V, PresentedReachable left right (root (component v)) v)
    (hprivate : HasPrivatePivots vertexVector component root) :
    Module.finrank F₂
        (LinearMap.ker (representedEdgeMap vertexVector left right)) ≤
      Fintype.card E - Fintype.card V + Fintype.card C :=
  GraphCycleRank.finrank_ker_representedEdgeMap_le_cyclomaticNumber
    vertexVector left right component root hroot hedge hprivate
      (finrank_cycleSpace_le_cyclomaticNumber
        left right component root hroot hconnected)

/--
Lemma 14.6, nullity form with truncation-safe cyclomatic arithmetic.
-/
theorem finrank_ker_representedEdgeMap_le_card_edges_sub_nonRoot
    (vertexVector : V → P → F₂) (left right : E → V)
    (component : V → C) (root : C → V)
    (hroot : ∀ c : C, component (root c) = c)
    (hedge : ∀ e : E, component (left e) = component (right e))
    (hconnected :
      ∀ v : V, PresentedReachable left right (root (component v)) v)
    (hprivate : HasPrivatePivots vertexVector component root) :
    Module.finrank F₂
        (LinearMap.ker (representedEdgeMap vertexVector left right)) ≤
      Fintype.card E - (Fintype.card V - Fintype.card C) :=
  (GraphCycleRank.finrank_ker_representedEdgeMap_le_cycleSpace
      vertexVector left right component root hroot hedge hprivate).trans
    (finrank_cycleSpace_le_card_edges_sub_nonRoot
      left right component root hroot hconnected)

/--
Lemma 14.6 in the paper's rank form: private pivots on every non-root vertex give rank at least
`|V| - |C|`.
-/
theorem card_vertices_sub_components_le_rank_representedEdgeMap
    (vertexVector : V → P → F₂) (left right : E → V)
    (component : V → C) (root : C → V)
    (hroot : ∀ c : C, component (root c) = c)
    (hedge : ∀ e : E, component (left e) = component (right e))
    (hconnected :
      ∀ v : V, PresentedReachable left right (root (component v)) v)
    (hprivate : HasPrivatePivots vertexVector component root) :
    Fintype.card V - Fintype.card C ≤
      Module.finrank F₂
        (LinearMap.range (representedEdgeMap vertexVector left right)) := by
  have hker :=
    finrank_ker_representedEdgeMap_le_card_edges_sub_nonRoot
      vertexVector left right component root hroot hedge hconnected hprivate
  have hnullity :
      Module.finrank F₂
          (LinearMap.range (representedEdgeMap vertexVector left right)) +
          Module.finrank F₂
          (LinearMap.ker (representedEdgeMap vertexVector left right)) =
        Fintype.card E := by
    exact finrank_range_add_finrank_ker_eq_card
      (representedEdgeMap vertexVector left right)
  have hincRange :
      Fintype.card V - Fintype.card C ≤
        Module.finrank F₂ (LinearMap.range (incidenceMap left right)) :=
    card_vertices_sub_components_le_finrank_incidenceRange
      left right component root hroot hconnected
  have hincNullity :
      Module.finrank F₂ (LinearMap.range (incidenceMap left right)) +
          Module.finrank F₂ (LinearMap.ker (incidenceMap left right)) =
        Fintype.card E :=
    finrank_range_add_finrank_ker_eq_card (incidenceMap left right)
  have hcardEV :
      Fintype.card V - Fintype.card C ≤ Fintype.card E := by
    omega
  have hsum :
      Module.finrank F₂
            (LinearMap.ker (representedEdgeMap vertexVector left right)) +
          (Fintype.card V - Fintype.card C) ≤
        Fintype.card E :=
    Nat.add_le_of_le_sub hcardEV hker
  have hcancel :
      Module.finrank F₂
            (LinearMap.ker (representedEdgeMap vertexVector left right)) +
          (Fintype.card V - Fintype.card C) ≤
        Module.finrank F₂
            (LinearMap.ker (representedEdgeMap vertexVector left right)) +
          Module.finrank F₂
            (LinearMap.range (representedEdgeMap vertexVector left right)) := by
    calc
      Module.finrank F₂
              (LinearMap.ker (representedEdgeMap vertexVector left right)) +
            (Fintype.card V - Fintype.card C) ≤
          Fintype.card E := hsum
      _ =
          Module.finrank F₂
              (LinearMap.range (representedEdgeMap vertexVector left right)) +
            Module.finrank F₂
              (LinearMap.ker (representedEdgeMap vertexVector left right)) :=
        hnullity.symm
      _ =
          Module.finrank F₂
              (LinearMap.ker (representedEdgeMap vertexVector left right)) +
            Module.finrank F₂
              (LinearMap.range (representedEdgeMap vertexVector left right)) :=
        Nat.add_comm _ _
  exact Nat.le_of_add_le_add_left hcancel

end CycleSpaceDimension
end PaperC
