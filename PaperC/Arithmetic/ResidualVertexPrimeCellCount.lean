import PaperC.Arithmetic.ResidualChannelCells
import PaperC.Affine.RationalChannelCode

/-!
# Equivalence of the two residual-cell coordinate systems

Lemma 7.2 counts residual cells in signed-offset coordinates
`{-1, ..., L-1}²`, whereas the canonical certificates use complete-start
vertices `Fin (L+1)²`.  The two definitions are literally equivalent under
`v ↦ v-1`.  This file records the finite equivalence and, in particular,
the equality of their cardinalities.
-/

namespace PaperC

open Affine.RationalChannelCode

noncomputable section

/--
Residual vertex cells and signed-offset residual cells at a fixed prime are
equivalent.
-/
noncomputable def residualVertexPrimeCellEquiv
    (L a b p : ℕ) (h : ℤ) :
    {cell // cell ∈ residualVertexPrimeCells L a b p h} ≃
      {cell // cell ∈ residualPrimeCells L a b p h} where
  toFun cell :=
    ⟨(channelVertexOffset cell.1.1,
        channelVertexOffset cell.1.2),
      mem_residualVertexPrimeCells_iff_offsets_mem.mp cell.2⟩
  invFun cell := by
    have hbox := (mem_residualPrimeCells.mp cell.2).1
    rw [mem_offsetBox] at hbox
    let left : Fin (L + 1) :=
      offsetVertexOfMem cell.1.1
        (by simpa only [mem_offsetInterval] using hbox.1)
    let right : Fin (L + 1) :=
      offsetVertexOfMem cell.1.2
        (by simpa only [mem_offsetInterval] using hbox.2)
    refine ⟨(left, right), ?_⟩
    rw [mem_residualVertexPrimeCells_iff_offsets_mem]
    simpa [left, right] using cell.2
  left_inv cell := by
    apply Subtype.ext
    apply Prod.ext
    · simp
    · simp
  right_inv cell := by
    apply Subtype.ext
    apply Prod.ext
    · simp
    · simp

/-- The two residual-cell finsets have the same cardinality. -/
theorem residualVertexPrimeCells_card_eq_residualPrimeCells_card
    (L a b p : ℕ) (h : ℤ) :
    (residualVertexPrimeCells L a b p h).card =
      (residualPrimeCells L a b p h).card := by
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_congr
    (residualVertexPrimeCellEquiv L a b p h)

end

end PaperC
