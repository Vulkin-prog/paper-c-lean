import PaperCV282.TerminalSliceGeometry
import PaperCV282.OrderedPairCounting
import PaperCV282.ResidualSectorMasks

/-!
# Actual terminal masks in the two arithmetic slice populations

The mask may be filtered by any further condition. Its canonical sector is
checked in its original orientation. Only the counting maps use the larger
and smaller starts, so no symmetry of the canonical classifier is needed.
-/

namespace PaperC.V282.TerminalSectorMasks

open PropositionSixteenOne ResidualSectorPartition ResidualSectorMasks
open SectorEightGeometry TerminalSliceGeometry OrderedPairCounting
open KernelWindowEnergy TerminalPartnerCount

noncomputable section

theorem largerStarts_subset_slice {X : ℕ} {s : Finset (ℕ × ℕ)}
    (hslice : ∀ p ∈ s, X ≤ max p.1 p.2 ∧ max p.1 p.2 < 2 * X) :
    largerStarts s ⊆ Finset.Ico X (2 * X) := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_Ico.mpr (hslice p hp)

theorem smallerPartners_subset_twoKernelPartnerStarts {N M A L X : ℕ}
    (hN : 2 ≤ N) {s : Finset (ℕ × ℕ)}
    (hs : s ⊆ sectorMask (M := M) (L := L) A hN 7)
    (hupper : ∀ p ∈ s, max p.1 p.2 < 2 * X) (x : ℕ) :
    smallerPartners s x ⊆ twoKernelPartnerStarts X L x := by
  intro y hy
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨hp, heq⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpair, hsector⟩ := mem_sectorMask.mp (hs hp)
  have hboth := mem_twoKernelPartnerStarts_both hN ⟨p, hpair⟩ hsector
    ((le_max_left p.1 p.2).trans_lt (hupper p hp))
    ((le_max_right p.1 p.2).trans_lt (hupper p hp))
  rw [← heq]
  rcases le_total p.1 p.2 with h | h
  · simpa only [min_eq_left h, max_eq_right h] using hboth.2
  · simpa only [min_eq_right h, max_eq_left h] using hboth.1

theorem le_card_smallKernelOffsets_largerStarts {N M A L X m : ℕ}
    (hN : 2 ≤ N) (hA : 1 ≤ A) {s : Finset (ℕ × ℕ)}
    (hs : s ⊆ sectorMask (M := M) (L := L) A hN 7)
    (hupper : ∀ p ∈ s, max p.1 p.2 < 2 * X) (hL : L ≤ X)
    (hindex : ∀ pair : SeparatedBoundedRatioPair N M L,
      pair.1 ∈ s → m ≤ L + 1 - 3 * terminalIndex A pair - 1) :
    ∀ x ∈ largerStarts s,
      m ≤ (smallKernelOffsets (L + 1) (kernelThreshold X L) L x).card := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hpair, hsector⟩ := mem_sectorMask.mp (hs hp)
  have hboth := terminalIndex_le_smallKernelOffsets_both hN hA ⟨p, hpair⟩ hsector
    ((le_max_left p.1 p.2).trans_lt (hupper p hp))
    ((le_max_right p.1 p.2).trans_lt (hupper p hp)) hL
  have hm := hindex ⟨p, hpair⟩ hp
  rcases le_total p.1 p.2 with h | h
  · simpa only [max_eq_right h] using hm.trans hboth.2
  · simpa only [max_eq_left h] using hm.trans hboth.1

theorem one_le_card_smallKernelOffsets_largerStarts {N M A L X : ℕ}
    (hN : 2 ≤ N) (hA : 1 ≤ A) {s : Finset (ℕ × ℕ)}
    (hs : s ⊆ sectorMask (M := M) (L := L) A hN 7)
    (hupper : ∀ p ∈ s, max p.1 p.2 < 2 * X) (hL : L ≤ X) :
    ∀ x ∈ largerStarts s,
      1 ≤ (smallKernelOffsets (L + 1) (kernelThreshold X L) L x).card := by
  apply le_card_smallKernelOffsets_largerStarts hN hA hs hupper hL
  intro pair hp
  obtain ⟨hp', hsector⟩ := mem_sectorMask.mp (hs hp)
  have heq : (⟨pair.1, hp'⟩ : SeparatedBoundedRatioPair N M L) = pair := Subtype.ext rfl
  rw [heq] at hsector
  have h := terminalIndex_budget hN pair hsector
  omega

theorem image_subset_sectorMask {N M A L : ℕ} (hN : 2 ≤ N)
    {s : Finset (SeparatedBoundedRatioPair N M L)}
    (hs : s ⊆ sectorPairs N M A L hN 7) :
    s.image Subtype.val ⊆ sectorMask (M := M) (L := L) A hN 7 := by
  classical
  exact Finset.image_subset_image hs

theorem image_geometry {N M A L X m : ℕ} (hN : 2 ≤ N) (hA : 1 ≤ A)
    {s : Finset (SeparatedBoundedRatioPair N M L)}
    (hs : s ⊆ sectorPairs N M A L hN 7)
    (hscale : ∀ p ∈ s, X ≤ max p.1.1 p.1.2 ∧ max p.1.1 p.1.2 < 2 * X)
    (hL : L ≤ X)
    (hindex : ∀ p ∈ s, m ≤ L + 1 - 3 * terminalIndex A p - 1) :
    largerStarts (s.image Subtype.val) ⊆ Finset.Ico X (2 * X) ∧
      (∀ x, smallerPartners (s.image Subtype.val) x ⊆ twoKernelPartnerStarts X L x) ∧
      ∀ x ∈ largerStarts (s.image Subtype.val),
        m ≤ (smallKernelOffsets (L + 1) (kernelThreshold X L) L x).card := by
  classical
  have hmask := image_subset_sectorMask hN hs
  have hscale' : ∀ p ∈ s.image Subtype.val,
      X ≤ max p.1 p.2 ∧ max p.1 p.2 < 2 * X := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact hscale q hq
  have hupper := fun p hp => (hscale' p hp).2
  refine ⟨largerStarts_subset_slice hscale',
    smallerPartners_subset_twoKernelPartnerStarts hN hmask hupper, ?_⟩
  apply le_card_smallKernelOffsets_largerStarts hN hA hmask hupper hL
  intro pair hp
  obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hp
  have hqp : q = pair := Subtype.ext heq
  exact hqp ▸ hindex q hq

theorem image_geometry_one {N M A L X : ℕ} (hN : 2 ≤ N) (hA : 1 ≤ A)
    {s : Finset (SeparatedBoundedRatioPair N M L)}
    (hs : s ⊆ sectorPairs N M A L hN 7)
    (hscale : ∀ p ∈ s, X ≤ max p.1.1 p.1.2 ∧ max p.1.1 p.1.2 < 2 * X)
    (hL : L ≤ X) :
    largerStarts (s.image Subtype.val) ⊆ Finset.Ico X (2 * X) ∧
      (∀ x, smallerPartners (s.image Subtype.val) x ⊆ twoKernelPartnerStarts X L x) ∧
      ∀ x ∈ largerStarts (s.image Subtype.val),
        1 ≤ (smallKernelOffsets (L + 1) (kernelThreshold X L) L x).card := by
  apply image_geometry hN hA hs hscale hL
  intro p hp
  have hsector := mem_sectorPairs.mp (hs hp)
  have h := terminalIndex_budget hN p hsector
  omega

end

end PaperC.V282.TerminalSectorMasks
