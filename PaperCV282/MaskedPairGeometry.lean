import PaperCV282.MaskedArithmeticGeometry

namespace PaperC.V282.MaskedPairGeometry

open LargePrimeDependencyGraph MaskedArithmeticGeometry

noncomputable section

/-- Ordered support edges on every site of the mask, including deleted sites. -/
def maskedSupportEdges (L Y : ℕ) (mask : Finset ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact mask.offDiag.filter fun p => LargePrimeAdjacent L Y p.1 p.2

theorem mem_maskedSupportEdges {L Y : ℕ} {mask : Finset ℕ} {p : ℕ × ℕ} :
    p ∈ maskedSupportEdges L Y mask ↔
      p.1 ∈ mask ∧ p.2 ∈ mask ∧ LargePrimeAdjacent L Y p.1 p.2 := by
  classical
  simp only [maskedSupportEdges, Finset.mem_filter, Finset.mem_offDiag]
  constructor
  · rintro ⟨⟨hx, hy, _⟩, h⟩
    exact ⟨hx, hy, h⟩
  · rintro ⟨hx, hy, h⟩
    exact ⟨⟨hx, hy, h.1⟩, h⟩

theorem fullMaskedEdges_eq_restricted_support (N L Y : ℕ) (mask : Finset ℕ) :
    fullMaskedEdges N L Y mask = maskedSupportEdges L Y (fullGoodMask N L Y mask) := rfl

theorem maskedSupportEdges_mono {L Y : ℕ} {s t : Finset ℕ} (h : s ⊆ t) :
    maskedSupportEdges L Y s ⊆ maskedSupportEdges L Y t := by
  intro p hp
  obtain ⟨hx, hy, ha⟩ := mem_maskedSupportEdges.mp hp
  exact mem_maskedSupportEdges.mpr ⟨h hx,h hy,ha⟩

theorem fullMaskedEdges_subset_support (N L Y : ℕ) (mask : Finset ℕ) :
    fullMaskedEdges N L Y mask ⊆ maskedSupportEdges L Y mask :=
  maskedSupportEdges_mono (fullGoodMask_subset_mask N L Y mask)

theorem card_fullMaskedEdges_le_support (N L Y : ℕ) (mask : Finset ℕ) :
    (fullMaskedEdges N L Y mask).card ≤ (maskedSupportEdges L Y mask).card :=
  Finset.card_le_card (fullMaskedEdges_subset_support N L Y mask)

end
end PaperC.V282.MaskedPairGeometry
