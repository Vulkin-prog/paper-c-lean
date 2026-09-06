import PaperC.Combinatorics.PinnedGraphResolution
import Mathlib.LinearAlgebra.Matrix.Rank

/-! # The actual finite binary incidence matrix

Rows of weight two define a simple graph, and rows of weight one pin their
column. Repeated pins and zero rows or columns are retained. Incidence mass
counts entries equal to one, rather than rows.
-/
namespace PaperC.V282.SimpleIncidenceModel

open Matrix Finset SimpleGraph

noncomputable section

variable {R V : Type*} [Fintype R] [Fintype V] [DecidableEq V]

/-- The support of an actual row. -/
def rowSupport (H : Matrix R V F₂) (r : R) : Finset V :=
  Finset.univ.filter (fun v => H r v ≠ 0)

/-- The support of an actual column. -/
def columnSupport (H : Matrix R V F₂) (v : V) : Finset R :=
  Finset.univ.filter (fun r => H r v ≠ 0)

/-- The literal number of nonzero binary entries. -/
def incidenceMass (H : Matrix R V F₂) : ℕ := ∑ r, (rowSupport H r).card

/-- Two active entries in one row form an edge. -/
def incidenceGraph (H : Matrix R V F₂) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ r, rowSupport H r = {u,v}
  symm := ⟨by
    rintro u v ⟨hne,r,hr⟩
    exact ⟨hne.symm,r,hr.trans (Finset.pair_comm _ _)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance instDecidableIncidenceAdj (H : Matrix R V F₂) : DecidableRel (incidenceGraph H).Adj :=
  Classical.decRel _

/-- A column is pinned when some row has precisely that support. -/
def pinnedColumns (H : Matrix R V F₂) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => ∃ r, rowSupport H r = {v})

omit [Fintype R] [DecidableEq V] in
theorem mem_rowSupport (H : Matrix R V F₂) (r : R) (v : V) :
    v ∈ rowSupport H r ↔ H r v ≠ 0 := by simp [rowSupport]

omit [Fintype V] [DecidableEq V] in
theorem mem_columnSupport (H : Matrix R V F₂) (r : R) (v : V) :
    r ∈ columnSupport H v ↔ H r v ≠ 0 := by simp [columnSupport]

theorem mem_pinnedColumns (H : Matrix R V F₂) (v : V) :
    v ∈ pinnedColumns H ↔ ∃ r, rowSupport H r = {v} := by
  classical
  simp [pinnedColumns]

theorem binary_eq_one_of_ne_zero {a : F₂} (ha : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact (ha rfl).elim
  · rfl

omit [Fintype R] [DecidableEq V] in
/-- Matrix multiplication reads each nonzero entry as the binary coefficient one. -/
theorem mulVecLin_apply_eq_support_sum (H : Matrix R V F₂) (f : V → F₂) (r : R) :
    (H.mulVecLin f) r = ∑ v ∈ rowSupport H r, f v := by
  classical
  change (∑ v, H r v * f v) = _
  rw [rowSupport, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : H r v = 0
  · simp [hv]
  · simp [binary_eq_one_of_ne_zero hv]

omit [Fintype R] in
/-- All row shapes allowed by the hypothesis, including the zero row. -/
theorem row_shapes (H : Matrix R V F₂) (r : R) (hrow : (rowSupport H r).card ≤ 2) :
    rowSupport H r = ∅ ∨ (∃ v, rowSupport H r = {v}) ∨
      ∃ u v, u ≠ v ∧ rowSupport H r = {u,v} := by
  by_cases hzero : (rowSupport H r).card = 0
  · exact Or.inl (Finset.card_eq_zero.mp hzero)
  by_cases hone : (rowSupport H r).card = 1
  · exact Or.inr (Or.inl (Finset.card_eq_one.mp hone))
  exact Or.inr (Or.inr (Finset.card_eq_two.mp (by omega)))

omit [DecidableEq V] in
/-- The same incidence mass is obtained by summing actual column weights. -/
theorem incidenceMass_eq_sum_columnSupport (H : Matrix R V F₂) :
    incidenceMass H = ∑ v, (columnSupport H v).card := by
  classical
  simp only [incidenceMass, rowSupport, columnSupport, Finset.card_filter]
  exact Finset.sum_comm

end
end PaperC.V282.SimpleIncidenceModel
