import PaperC.Arithmetic.ParityVector
import PaperC.Combinatorics.TreeBoundary
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option maxHeartbeats 800000

/-!
# Private pivots and the binary cycle space

This file isolates the linear-combinatorial core of Paper C, Lemma 14.6.  We use an oriented
presentation of a finite undirected multigraph: an edge `e` has endpoints `left e` and `right e`.
The orientation is immaterial over `F₂`.

The main theorem says that, if all vertices except a distinguished root in each component have a
private coordinate, then every dependence between the represented edge vectors lies in the
binary cycle space.  Rank-nullity then gives the rank lower bound once the usual cyclomatic
dimension bound for that cycle space is available.
-/

namespace PaperC
namespace GraphCycleRank

open Fintype LinearMap Module

variable {V E C P : Type*}
variable [Fintype V] [DecidableEq V]
variable [Fintype E] [DecidableEq E]
variable [Fintype C] [DecidableEq C]
variable [Fintype P] [DecidableEq P]

/-- The binary incidence vector of an edge with the displayed endpoints. -/
def incidenceVector (left right : E → V) (e : E) : V → F₂ :=
  Pi.single (left e) 1 + Pi.single (right e) 1

/-- The binary incidence map.  Its kernel is the usual binary cycle space. -/
def incidenceMap (left right : E → V) : (E → F₂) →ₗ[F₂] (V → F₂) :=
  Fintype.linearCombination F₂ (incidenceVector left right)

/-- The binary cycle space of an edge presentation. -/
def cycleSpace (left right : E → V) : Submodule F₂ (E → F₂) :=
  LinearMap.ker (incidenceMap left right)

/-- The vector attached to an edge is the sum of the vectors at its two endpoints. -/
def representedEdgeVector
    (vertexVector : V → P → F₂) (left right : E → V) (e : E) : P → F₂ :=
  vertexVector (left e) + vertexVector (right e)

/-- Linear combinations of the represented edge vectors. -/
def representedEdgeMap
    (vertexVector : V → P → F₂) (left right : E → V) :
    (E → F₂) →ₗ[F₂] (P → F₂) :=
  Fintype.linearCombination F₂ (representedEdgeVector vertexVector left right)

/--
All non-root vertices possess a private coordinate: at that coordinate their vertex vector is
one, and every other vertex vector is zero.
-/
def HasPrivatePivots
    (vertexVector : V → P → F₂) (component : V → C) (root : C → V) : Prop :=
  ∀ v : V, v ≠ root (component v) →
    ∃ p : P, ∀ w : V, vertexVector w p = if w = v then 1 else 0

@[simp]
theorem incidenceVector_apply
    (left right : E → V) (e : E) (v : V) :
    incidenceVector left right e v =
      (if v = left e then 1 else 0) + (if v = right e then 1 else 0) := by
  simp only [incidenceVector, Pi.add_apply, Pi.single_apply]

@[simp]
theorem incidenceMap_apply
    (left right : E → V) (x : E → F₂) (v : V) :
    incidenceMap left right x v =
      ∑ e : E, x e * ((if v = left e then 1 else 0) +
        (if v = right e then 1 else 0)) := by
  simp [incidenceMap, Fintype.linearCombination_apply, incidenceVector_apply, smul_eq_mul]

/--
A private coordinate reads a represented-edge dependence as the incidence equation at its
private vertex.
-/
theorem incidenceMap_apply_eq_privateCoordinate
    (vertexVector : V → P → F₂) (left right : E → V)
    (component : V → C) (root : C → V)
    (hprivate : HasPrivatePivots vertexVector component root)
    (x : E → F₂) {v : V} (hv : v ≠ root (component v)) :
    ∃ p : P,
      incidenceMap left right x v = representedEdgeMap vertexVector left right x p := by
  obtain ⟨p, hp⟩ := hprivate v hv
  refine ⟨p, ?_⟩
  simp only [incidenceMap_apply, representedEdgeMap, Fintype.linearCombination_apply,
    representedEdgeVector, Finset.sum_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro e _
  rw [hp (left e), hp (right e)]
  by_cases hl : v = left e <;> by_cases hr : v = right e <;> simp [hl, hr, eq_comm]

/--
Every dependence of represented edge vectors satisfies the incidence equation at each vertex
which has a private coordinate.
-/
theorem incidence_eq_zero_at_nonRoot_of_mem_ker
    (vertexVector : V → P → F₂) (left right : E → V)
    (component : V → C) (root : C → V)
    (hprivate : HasPrivatePivots vertexVector component root)
    {x : E → F₂} (hx : x ∈ LinearMap.ker (representedEdgeMap vertexVector left right))
    {v : V} (hv : v ≠ root (component v)) :
    incidenceMap left right x v = 0 := by
  obtain ⟨p, hp⟩ :=
    incidenceMap_apply_eq_privateCoordinate vertexVector left right component root hprivate x hv
  rw [hp]
  have hzero : representedEdgeMap vertexVector left right x = 0 := hx
  rw [hzero]
  rfl

/--
The sum of all incidence coordinates in one component is zero, because every edge inside that
component contributes twice (and every edge outside it contributes zero).
-/
theorem sum_incidenceMap_on_component_eq_zero
    (left right : E → V) (component : V → C)
    (hedge : ∀ e : E, component (left e) = component (right e))
    (x : E → F₂) (c : C) :
    ∑ v ∈ Finset.univ.filter (fun v : V ↦ component v = c),
        incidenceMap left right x v = 0 := by
  classical
  simp only [incidenceMap_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e _
  rw [← Finset.mul_sum]
  have hleft :
      ∑ v ∈ Finset.univ.filter (fun v : V ↦ component v = c),
          (if v = left e then (1 : F₂) else 0) =
        if component (left e) = c then 1 else 0 := by
    by_cases hc : component (left e) = c <;> simp [hc]
  have hright :
      ∑ v ∈ Finset.univ.filter (fun v : V ↦ component v = c),
          (if v = right e then (1 : F₂) else 0) =
        if component (right e) = c then 1 else 0 := by
    by_cases hc : component (right e) = c <;> simp [hc]
  rw [Finset.sum_add_distrib, hleft, hright]
  by_cases hc : component (left e) = c
  · have hcr : component (right e) = c := by
      rw [← hedge e]
      exact hc
    rw [if_pos hc, if_pos hcr, show (1 + 1 : F₂) = 0 by decide, mul_zero]
  · have hcr : component (right e) ≠ c := by
      rw [← hedge e]
      exact hc
    simp [hc, hcr]

/--
Private pivots force every represented-edge dependence to have even degree at every vertex.
Equivalently, its coefficient vector lies in the binary cycle space.
-/
theorem ker_representedEdgeMap_le_cycleSpace
    (vertexVector : V → P → F₂) (left right : E → V)
    (component : V → C) (root : C → V)
    (_hroot : ∀ c : C, component (root c) = c)
    (hedge : ∀ e : E, component (left e) = component (right e))
    (hprivate : HasPrivatePivots vertexVector component root) :
    LinearMap.ker (representedEdgeMap vertexVector left right) ≤
      cycleSpace left right := by
  intro x hx
  rw [cycleSpace, LinearMap.mem_ker]
  funext v
  by_cases hv : v = root (component v)
  · let c : C := component v
    have hvc : component v = c := rfl
    have hsum :=
      sum_incidenceMap_on_component_eq_zero left right component hedge x c
    have hrootc : root c = v := by
      dsimp [c]
      exact hv.symm
    have hothers :
        ∀ w ∈ Finset.univ.filter (fun w : V ↦ component w = c),
          w ≠ v → incidenceMap left right x w = 0 := by
      intro w hw hwv
      apply incidence_eq_zero_at_nonRoot_of_mem_ker
        vertexVector left right component root hprivate hx
      intro hwr
      have hwc : component w = c := (Finset.mem_filter.mp hw).2
      have : root (component w) = v := by
        rw [hwc, hrootc]
      exact hwv (hwr.trans this)
    have hv_mem : v ∈ Finset.univ.filter (fun w : V ↦ component w = c) := by
      simp [hvc]
    rw [Finset.sum_eq_add_sum_diff_singleton hv_mem] at hsum
    have hdiff :
        ∑ w ∈ (Finset.univ.filter (fun w : V ↦ component w = c)) \ {v},
          incidenceMap left right x w = 0 := by
      apply Finset.sum_eq_zero
      intro w hw
      apply hothers w
      · exact (Finset.mem_sdiff.mp hw).1
      · simpa using (Finset.mem_sdiff.mp hw).2
    rw [hdiff, add_zero] at hsum
    simpa using hsum
  · simpa using incidence_eq_zero_at_nonRoot_of_mem_ker
      vertexVector left right component root hprivate hx hv

/--
Pointwise form: a vanishing combination of represented edge vectors has binary degree zero at
every vertex.
-/
theorem representedEdge_dependence_has_even_degree
    (vertexVector : V → P → F₂) (left right : E → V)
    (component : V → C) (root : C → V)
    (hroot : ∀ c : C, component (root c) = c)
    (hedge : ∀ e : E, component (left e) = component (right e))
    (hprivate : HasPrivatePivots vertexVector component root)
    {x : E → F₂} (hx : representedEdgeMap vertexVector left right x = 0) :
    ∀ v : V,
      ∑ e : E, x e * ((if v = left e then 1 else 0) +
        (if v = right e then 1 else 0)) = 0 := by
  intro v
  rw [← incidenceMap_apply]
  have hxker : x ∈ LinearMap.ker (representedEdgeMap vertexVector left right) := hx
  exact congrFun
    (LinearMap.mem_ker.mp
      (ker_representedEdgeMap_le_cycleSpace
        vertexVector left right component root hroot hedge hprivate hxker)) v

/-- The nullity of represented edge vectors is at most the dimension of the cycle space. -/
theorem finrank_ker_representedEdgeMap_le_cycleSpace
    (vertexVector : V → P → F₂) (left right : E → V)
    (component : V → C) (root : C → V)
    (hroot : ∀ c : C, component (root c) = c)
    (hedge : ∀ e : E, component (left e) = component (right e))
    (hprivate : HasPrivatePivots vertexVector component root) :
    Module.finrank F₂ (LinearMap.ker (representedEdgeMap vertexVector left right)) ≤
      Module.finrank F₂ (cycleSpace left right) :=
  Submodule.finrank_mono
    (ker_representedEdgeMap_le_cycleSpace
      vertexVector left right component root hroot hedge hprivate)

/-- Nullity form, after supplying any upper bound `β` for the binary cycle space. -/
theorem finrank_ker_representedEdgeMap_le_beta
    (vertexVector : V → P → F₂) (left right : E → V)
    (component : V → C) (root : C → V)
    (hroot : ∀ c : C, component (root c) = c)
    (hedge : ∀ e : E, component (left e) = component (right e))
    (hprivate : HasPrivatePivots vertexVector component root)
    (β : ℕ) (hcycle : Module.finrank F₂ (cycleSpace left right) ≤ β) :
    Module.finrank F₂ (LinearMap.ker (representedEdgeMap vertexVector left right)) ≤ β :=
  (finrank_ker_representedEdgeMap_le_cycleSpace
    vertexVector left right component root hroot hedge hprivate).trans hcycle

/--
Cyclomatic specialization of the nullity bound.  Here
`|E| - |V| + |C|` is `β₁` for an edge presentation whose component index is `C`.
-/
theorem finrank_ker_representedEdgeMap_le_cyclomaticNumber
    (vertexVector : V → P → F₂) (left right : E → V)
    (component : V → C) (root : C → V)
    (hroot : ∀ c : C, component (root c) = c)
    (hedge : ∀ e : E, component (left e) = component (right e))
    (hprivate : HasPrivatePivots vertexVector component root)
    (hcycle :
      Module.finrank F₂ (cycleSpace left right) ≤
        Fintype.card E - Fintype.card V + Fintype.card C) :
    Module.finrank F₂ (LinearMap.ker (representedEdgeMap vertexVector left right)) ≤
      Fintype.card E - Fintype.card V + Fintype.card C :=
  finrank_ker_representedEdgeMap_le_beta
    vertexVector left right component root hroot hedge hprivate
      (Fintype.card E - Fintype.card V + Fintype.card C) hcycle

end GraphCycleRank
end PaperC
