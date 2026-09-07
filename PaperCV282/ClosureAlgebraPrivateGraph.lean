import PaperCV282.ClosureAlgebraIncidence
import PaperC.LinearAlgebra.PrivatePivots

/-! # Private pivots with the cyclomatic dimension discharged

The component labels are the actual connectivity quotient. The assumptions
only give a root in each component and private coordinates off those roots.
No cycle dimension or rank assertion is supplied as an input.
-/
namespace PaperC.V282.ClosureAlgebraPrivateGraph

open GraphCycleRank ClosureAlgebraIncidence Module

noncomputable section

variable {V E P : Type*}
variable [Fintype V] [Fintype E] [Fintype P]
variable [DecidableEq V] [DecidableEq E] [DecidableEq P]

/-- The exact cyclomatic number, with nontruncated addition before subtraction. -/
def cyclomaticNumber (left right : E → V) : ℕ :=
  Fintype.card E + Fintype.card (Component left right) - Fintype.card V

/-- Lemma 2.7, including the dimension computation for the graph itself. -/
theorem lemma_two_seven (left right : E → V) (vertexVector : V → P → F₂)
    (root : Component left right → V)
    (hroot : ∀ c, component left right (root c) = c)
    (hprivate : HasPrivatePivots vertexVector (component left right) root) :
    LinearMap.ker (representedEdgeMap vertexVector left right) ≤ cycleSpace left right ∧
    finrank F₂ (cycleSpace left right) = cyclomaticNumber left right ∧
    Fintype.card E - cyclomaticNumber left right ≤
      finrank F₂ (LinearMap.range (representedEdgeMap vertexVector left right)) := by
  classical
  have hk := ker_representedEdgeMap_le_cycleSpace vertexVector left right
    (component left right) root hroot (component_edge left right) hprivate
  have hd := finrank_cycleSpace left right
  have hm := Submodule.finrank_mono hk
  have hn := LinearMap.finrank_range_add_finrank_ker (representedEdgeMap vertexVector left right)
  rw [Module.finrank_fintype_fun_eq_card] at hn
  refine ⟨hk,hd,?_⟩
  change Fintype.card E - (Fintype.card E + Fintype.card (Component left right) -
    Fintype.card V) ≤ _
  omega

/-- Equivalent rank form: at least one degree of freedom per non-root vertex. -/
theorem rank_add_components_le (left right : E → V) (vertexVector : V → P → F₂)
    (root : Component left right → V)
    (hroot : ∀ c, component left right (root c) = c)
    (hprivate : HasPrivatePivots vertexVector (component left right) root) :
    Fintype.card V ≤ finrank F₂ (LinearMap.range (representedEdgeMap vertexVector left right)) +
      Fintype.card (Component left right) := by
  have h := (lemma_two_seven left right vertexVector root hroot hprivate).2.2
  have hi := incidence_rank_add_components left right
  have hn := LinearMap.finrank_range_add_finrank_ker (incidenceMap left right)
  rw [Module.finrank_fintype_fun_eq_card] at hn
  dsimp [cyclomaticNumber] at h
  omega

omit [Fintype E] [Fintype P] [DecidableEq E] [DecidableEq P] in
/-- The tree clause has full edge rank, directly from the tree boundary theorem. -/
theorem lemma_two_seven_tree (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsTree) (r : V) (v : V → P →₀ F₂)
    (pivot : {w : V // w ≠ r} → P)
    (hdiag : ∀ w, v w.val (pivot w) = 1)
    (hoff : ∀ w z, z ≠ w.val → v z (pivot w) = 0) :
    finrank F₂ (Submodule.span F₂ (Set.range
      (fun e : G.edgeSet => PrivatePivots.edgeSum v e.val))) = Fintype.card G.edgeSet :=
  finrank_span_eq_card (PrivatePivots.tree_edgeSum_linearIndependent_of_private_nonroot
    G hG r v pivot hdiag hoff)

end
end PaperC.V282.ClosureAlgebraPrivateGraph
