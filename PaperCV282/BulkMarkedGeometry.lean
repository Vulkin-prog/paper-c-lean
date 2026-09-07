import PaperCV282.BulkMarkedTypes
import PaperCV282.MacroscopicMaskGeometry

/-! # The exact contained macroscopic population of Theorem 7.7 -/
namespace PaperC.V282.BulkMarkedGeometry

open MacroscopicGeometry MacroscopicMaskGeometry BulkMarkedTypes

noncomputable section

/-- Inclusive upper endpoint: starts whose base run is contained in [1,M]. -/
def bulkStarts (M L : ℕ) (delta : ℝ) : Finset ℕ :=
  Finset.Icc ⌈(M : ℝ)^delta⌉₊ (M-L+1)

theorem mem_bulkStarts (M L x : ℕ) (delta : ℝ) :
    x∈bulkStarts M L delta ↔ ⌈(M : ℝ)^delta⌉₊≤x ∧ x≤M-L+1 := by
  simp [bulkStarts]

theorem mem_bulkStarts_iff_real (M L x : ℕ) (delta : ℝ) :
    x∈bulkStarts M L delta ↔ (M : ℝ)^delta≤x ∧ x≤M-L+1 := by
  simp [bulkStarts,Nat.ceil_le]

theorem bulkStarts_subset_closed {M L : ℕ} {delta : ℝ} (hM : 1≤M) (hL : 1≤L) :
    bulkStarts M L delta ⊆ Finset.Icc ⌈(M : ℝ)^delta⌉₊ M := by
  intro x hx
  obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp hx
  exact Finset.mem_Icc.mpr ⟨hl,by omega⟩

theorem bulkStarts_subset_Icc {M L : ℕ} {delta : ℝ}
    (hM : 2≤M) (hL : 1≤L) (hdelta : 0<delta) : bulkStarts M L delta ⊆ Finset.Icc 2 M := by
  intro x hx
  have hh := Finset.mem_Icc.mp (bulkStarts_subset_closed (by omega : 1≤M) hL hx)
  exact Finset.mem_Icc.mpr ⟨(two_le_macroscopic_lowerEndpoint hM hdelta).trans hh.1,hh.2⟩

theorem card_bulkStarts_le {M L : ℕ} {delta : ℝ}
    (hM : 2≤M) (hL : 1≤L) (hdelta : 0<delta) : (bulkStarts M L delta).card≤M :=
  card_mask_le (bulkStarts_subset_Icc hM hL hdelta)

/-- The carrier reads the same integer positions as the manuscript. -/
def normalizedPosition (M L : ℕ) (delta : ℝ) (j : SpatialMarkedIndex (bulkStarts M L delta)) : ℝ :=
  (j.1.val : ℝ)/M

theorem normalizedPosition_eq (M L : ℕ) (delta : ℝ)
    (j : SpatialMarkedIndex (bulkStarts M L delta)) :
    normalizedPosition M L delta j = (j.1.val : ℝ)/M := rfl

end
end PaperC.V282.BulkMarkedGeometry
