import PaperCV282.ClosureAlgebraSquareTuple
import PaperC.LinearAlgebra.PrivatePivots

/-! # Square-product edge relations for an arbitrary finite tree

The boundary bijection is now restricted to the actual arithmetic kernel.
Summing the parity vectors of edge endpoints cancels every even degree;
therefore the surviving boundary product is a square exactly for relations.
-/
namespace PaperC.V282.ClosureAlgebraTreeSquares

open Affine TreeBoundary PrivatePivots
open scoped BigOperators

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A nonloop edge reads each of its two endpoint values once. -/
theorem edgeSum_eq_vertex_sum (f : V → F₂) (e : Sym2 V) (hne : ¬ e.IsDiag) :
    edgeSum f e = ∑ v, if v ∈ e then f v else 0 := by
  induction e using Sym2.inductionOn with
  | _ a b =>
    have hab : a ≠ b := by simpa only [Sym2.mk_isDiag_iff] using hne
    rw [edgeSum_pair]
    calc
      f a + f b = ∑ v, ((if v=a then f v else 0) + (if v=b then f v else 0)) := by
        simp [Finset.sum_add_distrib]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro v _
        by_cases ha : v=a <;> by_cases hb : v=b <;> simp_all [Sym2.mem_iff]

/-- Only vertices of odd selected degree survive the edge sum over F₂. -/
theorem sum_edgeSum_eq_boundary (f : V → F₂) (F : Finset (Sym2 V))
    (hF : ∀ e ∈ F, ¬e.IsDiag) :
    ∑ e ∈ F, edgeSum f e = ∑ v ∈ boundary F, f v := by
  calc
    (∑ e ∈ F, edgeSum f e) = ∑ e ∈ F, ∑ v, if v ∈ e then f v else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      exact edgeSum_eq_vertex_sum f e (hF e he)
    _ = ∑ v, ∑ e ∈ F, if v ∈ e then f v else 0 := Finset.sum_comm
    _ = ∑ v ∈ boundary F, f v := by
      rw [boundary, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro v _
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      by_cases ho : Odd (F.filter (fun e => v ∈ e)).card
      · rw [if_pos ho, ZMod.natCast_eq_one_iff_odd.mpr ho, one_mul]
      · rw [if_neg ho, ZMod.natCast_eq_zero_iff_even.mpr (Nat.not_odd_iff_even.mp ho), zero_mul]

/-- Actual parity-vector edge relations are the boundary square products. -/
theorem edge_relation_iff_square {G : SimpleGraph V} [DecidableRel G.Adj]
    (label : V → ℕ) (hpos : ∀ v, 0 < label v) (F : EdgeSubset G) :
    (∑ e ∈ F, edgeSum (fun v => parityVec (label v)) e.val) = 0 ↔
      ∃ r : ℕ, (∏ v ∈ (boundaryMap G F).val, label v) = r^2 := by
  have he : (∑ e ∈ F, edgeSum (fun v => parityVec (label v)) e.val) =
      ∑ v ∈ (boundaryMap G F).val, parityVec (label v) := by
    ext p
    simp only [Finsupp.finsetSum_apply]
    have heval (e : Sym2 V) : edgeSum (fun v => parityVec (label v)) e p =
        edgeSum (fun v => parityVec (label v) p) e := by
      induction e using Sym2.inductionOn with
      | _ a b => rfl
    simp only [heval]
    change (∑ e ∈ F, edgeSum (fun v => parityVec (label v) p) e.val) =
      ∑ v ∈ boundary (edgeValueFinset F), parityVec (label v) p
    rw [← sum_edgeSum_eq_boundary _ (edgeValueFinset F)]
    · simp only [edgeValueFinset, Finset.sum_map]
      rfl
    · intro e he
      obtain ⟨heG,_⟩ := mem_edgeValueFinset.mp he
      exact G.not_isDiag_of_mem_edgeSet heG
  rw [he]
  exact sum_parityVec_eq_zero_iff_prod_eq_sq _ label (fun v _ => (hpos v).ne')

/-- The additional arbitrary-tree clause of Lemma 2.2, without arithmetic assumptions. -/
def lemma_two_two_tree {G : SimpleGraph V} [DecidableRel G.Adj] (hG : G.IsTree)
    (label : V → ℕ) (hpos : ∀ v, 0 < label v) :
    {F : EdgeSubset G // (∑ e ∈ F, edgeSum (fun v => parityVec (label v)) e.val) = 0} ≃
      {S : EvenVertexSubset V // ∃ r : ℕ, (∏ v ∈ S.val, label v) = r^2} :=
  (treeBoundaryEquiv hG).subtypeEquiv (edge_relation_iff_square label hpos)

end
end PaperC.V282.ClosureAlgebraTreeSquares
