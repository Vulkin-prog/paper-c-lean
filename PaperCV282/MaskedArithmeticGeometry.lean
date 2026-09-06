import PaperC.Probability.LargePrimeDependencyGraph
import PaperCV282.WindowValues

/-!
# The literal whole-support deletion rule of Theorem 4.1

Badness includes the left boundary x-1.  The historical terminalBadStarts
only checks the non-root run vertices, so it is used through an inclusion,
not identified with the new deletion set.  All masks remain explicit.
-/

namespace PaperC.V282.MaskedArithmeticGeometry

open LargePrimeDependencyGraph BadStartCount DefectivePredicate WindowValues
open scoped BigOperators

noncomputable section

/-- Starts having a defective value anywhere on the complete tree support. -/
def fullBadStarts (N L Y : ℕ) : Finset ℕ := by
  classical
  exact (dyadicBlock N).filter fun x => ∃ n ∈ startTreeSupport x L, HDefective Y n

/-- The actual sites retained from the deterministic position mask. -/
def fullGoodMask (N L Y : ℕ) (mask : Finset ℕ) : Finset ℕ :=
  mask \ fullBadStarts N L Y

/-- The actual sites removed from the deterministic position mask. -/
def fullBadMask (N L Y : ℕ) (mask : Finset ℕ) : Finset ℕ :=
  mask ∩ fullBadStarts N L Y

/-- Ordered open edges of the induced graph on the actual retained sites. -/
def fullMaskedEdges (N L Y : ℕ) (mask : Finset ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (fullGoodMask N L Y mask).offDiag.filter fun p => LargePrimeAdjacent L Y p.1 p.2

/-- The literal closed-neighborhood pair population on the retained mask. -/
def fullMaskedClosedPairs (N L Y : ℕ) (mask : Finset ℕ) : Finset (ℕ × ℕ) :=
  (fullGoodMask N L Y mask).diag ∪ fullMaskedEdges N L Y mask

/-- The manuscript's complete defective-vertex weight, on a chosen mask. -/
def fullDefectMass (L : ℕ) (mask : Finset ℕ) : ℕ :=
  ∑ x ∈ mask, (2 ^ (defectIndices (L + 1) x (L + 1)).card - 1)

theorem mem_fullBadStarts {N L Y x : ℕ} :
    x ∈ fullBadStarts N L Y ↔
      x ∈ dyadicBlock N ∧ ∃ n ∈ startTreeSupport x L, HDefective Y n := by
  classical
  simp [fullBadStarts]

theorem mem_fullGoodMask {N L Y x : ℕ} {mask : Finset ℕ} :
    x ∈ fullGoodMask N L Y mask ↔ x ∈ mask ∧ x ∉ fullBadStarts N L Y := by
  simp [fullGoodMask]

theorem mem_fullBadMask {N L Y x : ℕ} {mask : Finset ℕ} :
    x ∈ fullBadMask N L Y mask ↔ x ∈ mask ∧ x ∈ fullBadStarts N L Y := by
  simp [fullBadMask]

theorem mem_fullMaskedEdges {N L Y : ℕ} {mask : Finset ℕ} {p : ℕ × ℕ} :
    p ∈ fullMaskedEdges N L Y mask ↔
      p.1 ∈ fullGoodMask N L Y mask ∧ p.2 ∈ fullGoodMask N L Y mask ∧
        LargePrimeAdjacent L Y p.1 p.2 := by
  classical
  simp only [fullMaskedEdges, Finset.mem_filter, Finset.mem_offDiag]
  constructor
  · rintro ⟨⟨hx, hy, _⟩, h⟩
    exact ⟨hx, hy, h⟩
  · rintro ⟨hx, hy, h⟩
    exact ⟨⟨hx, hy, h.1⟩, h⟩

theorem fullBadStarts_subset_block (N L Y : ℕ) :
    fullBadStarts N L Y ⊆ dyadicBlock N := by
  classical
  exact Finset.filter_subset _ _

theorem fullGoodMask_subset_mask (N L Y : ℕ) (mask : Finset ℕ) :
    fullGoodMask N L Y mask ⊆ mask := Finset.sdiff_subset

theorem fullBadMask_subset_mask (N L Y : ℕ) (mask : Finset ℕ) :
    fullBadMask N L Y mask ⊆ mask := Finset.inter_subset_left

theorem terminalBadStarts_subset_fullBadStarts (N L Y : ℕ) :
    terminalBadStarts N L Y ⊆ fullBadStarts N L Y := by
  intro x hx
  obtain ⟨hxb, j, hj, hd⟩ := mem_terminalBadStarts.mp hx
  exact mem_fullBadStarts.mpr ⟨hxb, x + j,
    mem_startTreeSupport.mpr (Or.inr ⟨j,hj,rfl⟩),
    (LargeOddKernel.largeOddKernel_eq_one_iff_hDefective _ _).mp hd⟩

theorem fullGoodMask_subset_historical_good {N L Y : ℕ} {mask : Finset ℕ}
    (hmask : mask ⊆ dyadicBlock N) :
    fullGoodMask N L Y mask ⊆ goodStarts N L Y := by
  intro x hx
  obtain ⟨hxm, hxbad⟩ := mem_fullGoodMask.mp hx
  exact mem_goodStarts.mpr ⟨hmask hxm,
    fun h => hxbad (terminalBadStarts_subset_fullBadStarts N L Y h)⟩

theorem not_defective_of_mem_fullGoodMask {N L Y x : ℕ} {mask : Finset ℕ}
    (hmask : mask ⊆ dyadicBlock N) (hx : x ∈ fullGoodMask N L Y mask)
    {n : ℕ} (hn : n ∈ startTreeSupport x L) : ¬HDefective Y n := by
  intro hd
  exact (mem_fullGoodMask.mp hx).2
    (mem_fullBadStarts.mpr ⟨hmask (mem_fullGoodMask.mp hx).1,n,hn,hd⟩)

theorem card_fullGood_add_card_fullBad (N L Y : ℕ) (mask : Finset ℕ) :
    (fullGoodMask N L Y mask).card + (fullBadMask N L Y mask).card = mask.card :=
  Finset.card_sdiff_add_card_inter mask (fullBadStarts N L Y)

theorem fullGood_union_fullBad (N L Y : ℕ) (mask : Finset ℕ) :
    fullGoodMask N L Y mask ∪ fullBadMask N L Y mask = mask := by
  exact Finset.sdiff_union_inter _ _

theorem disjoint_fullGood_fullBad (N L Y : ℕ) (mask : Finset ℕ) :
    Disjoint (fullGoodMask N L Y mask) (fullBadMask N L Y mask) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact (mem_fullGoodMask.mp hx).2 (mem_fullBadMask.mp hy).2

theorem fullMaskedEdges_subset_mask_offDiag (N L Y : ℕ) (mask : Finset ℕ) :
    fullMaskedEdges N L Y mask ⊆ mask.offDiag := by
  intro p hp
  obtain ⟨hx, hy, h⟩ := mem_fullMaskedEdges.mp hp
  exact Finset.mem_offDiag.mpr ⟨(mem_fullGoodMask.mp hx).1,(mem_fullGoodMask.mp hy).1,h.1⟩

theorem card_fullMaskedClosedPairs (N L Y : ℕ) (mask : Finset ℕ) :
    (fullMaskedClosedPairs N L Y mask).card =
      (fullGoodMask N L Y mask).card + (fullMaskedEdges N L Y mask).card := by
  have hd : Disjoint (fullGoodMask N L Y mask).diag (fullMaskedEdges N L Y mask) := by
    apply Finset.disjoint_left.mpr
    intro p hp he
    exact (mem_fullMaskedEdges.mp he).2.2.1 (Finset.mem_diag.mp hp).2
  rw [fullMaskedClosedPairs, Finset.card_union_of_disjoint hd, Finset.diag_card]

end
end PaperC.V282.MaskedArithmeticGeometry
