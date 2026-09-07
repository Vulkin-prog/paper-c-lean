import PaperCV282.ResidualSectorMass
import PaperCV282.HostRankMass
import PaperCV282.MacroscopicShallowSigma

/-!
# Exact pair masks for the eight residual populations

Forgetting the subtype proof is injective. This exposes each population as
an ordinary finite pair mask, without losing multiplicity or changing its
canonical residual weight. In particular the finite homogeneous host
estimates apply to these masks.
-/

namespace PaperC.V282.ResidualSectorMasks

open PropositionSixteenOne ResidualSectorPartition ResidualSectorMass
open HostRankMass MacroscopicGeometry TwoWindowParity

noncomputable section

/-- The sector as a finite set of ordered pairs, with subtype proofs forgotten. -/
def sectorMask {N M L : ℕ} (A : ℕ) (hN : 2 ≤ N) (sector : Fin 8) : Finset (ℕ × ℕ) :=
  (sectorPairs N M A L hN sector).image Subtype.val

/-- Membership identifies the exact interval pair and its unique sector. -/
theorem mem_sectorMask {N M A L : ℕ} {hN : 2 ≤ N} {sector : Fin 8} {xy : ℕ × ℕ} :
    xy ∈ sectorMask (M := M) (L := L) A hN sector ↔
      ∃ hp : xy ∈ separatedBoundedRatioPairs N M L, sectorOf A hN ⟨xy, hp⟩ = sector := by
  classical
  simp only [sectorMask, Finset.mem_image, mem_sectorPairs]
  constructor
  · rintro ⟨p, hs, rfl⟩
    exact ⟨p.2, hs⟩
  · rintro ⟨hp, hs⟩
    exact ⟨⟨xy, hp⟩, hs, rfl⟩

/-- Every sector mask is contained in the original separated interval. -/
theorem sectorMask_subset {N M A L : ℕ} (hN : 2 ≤ N) (sector : Fin 8) :
    sectorMask (M := M) (L := L) A hN sector ⊆ separatedBoundedRatioPairs N M L := by
  intro xy hxy
  exact (mem_sectorMask.mp hxy).choose

/-- Forgetting proof fields preserves the number of pairs exactly. -/
theorem card_sectorMask {N M A L : ℕ} (hN : 2 ≤ N) (sector : Fin 8) :
    (sectorMask (M := M) (L := L) A hN sector).card =
      (sectorPairs N M A L hN sector).card := by
  classical
  exact Finset.card_image_iff.mpr (fun p _ q _ hpq => Subtype.ext hpq)

/-- Different sectors remain disjoint as masks of actual ordered pairs. -/
theorem sectorMask_disjoint {N M A L : ℕ} (hN : 2 ≤ N)
    {s t : Fin 8} (hst : s ≠ t) :
    Disjoint (sectorMask (M := M) (L := L) A hN s) (sectorMask (M := M) (L := L) A hN t) := by
  classical
  apply Finset.disjoint_left.mpr
  intro xy hs ht
  obtain ⟨hps, hs⟩ := mem_sectorMask.mp hs
  obtain ⟨hpt, ht⟩ := mem_sectorMask.mp ht
  exact hst (hs.symm.trans ht)

/-- The union of the eight masks is the original pair population. -/
theorem sectorMask_cover {N M A L : ℕ} (hN : 2 ≤ N) :
    (Finset.univ.biUnion fun sector : Fin 8 => sectorMask (M := M) (L := L) A hN sector) =
      separatedBoundedRatioPairs N M L := by
  classical
  ext xy
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨sector, hs⟩
    exact sectorMask_subset hN sector hs
  · intro hp
    exact ⟨sectorOf A hN ⟨xy, hp⟩, mem_sectorMask.mpr ⟨hp, rfl⟩⟩

/-- Exact transfer of the homogeneous weighted sum to the ordinary sector mask. -/
theorem relationWeightMass_sectorMask_eq_sum {N M A L : ℕ}
    (hN : 2 ≤ N) (sector : Fin 8) :
    relationWeightMass (M + L) L (sectorMask (M := M) (L := L) A hN sector) =
      ∑ p ∈ sectorPairs N M A L hN sector, homogeneousWeight p := by
  classical
  unfold relationWeightMass sectorMask
  rw [Finset.sum_image]
  · rfl
  · intro p _ q _ hpq
    exact Subtype.ext hpq

/-- A sector's actual residual mass is bounded by its homogeneous mask mass. -/
theorem sectorMassNat_le_relationWeightMass {N M A L : ℕ}
    (hN : 2 ≤ N) (sector : Fin 8) :
    sectorMassNat (M := M) (L := L) A hN sector ≤
      relationWeightMass (M + L) L (sectorMask (M := M) (L := L) A hN sector) := by
  rw [relationWeightMass_sectorMask_eq_sum]
  exact Finset.sum_le_sum fun p _ => residualWeight_le_homogeneousWeight hN p

/-- Real form of the same comparison, with no endpoint-ratio assumption. -/
theorem sectorMass_le_relationWeightMass {N M A L : ℕ}
    (hN : 2 ≤ N) (sector : Fin 8) :
    sectorMass A sector N M L ≤
      (relationWeightMass (M + L) L (sectorMask (M := M) (L := L) A hN sector) : ℝ) := by
  simp only [sectorMass, dif_pos hN]
  exact_mod_cast sectorMassNat_le_relationWeightMass (M := M) (A := A) (L := L) hN sector

/-- The classifier's positive-height test is the one used by the asymptotic estimates. -/
theorem smallPositiveChannel_iff_test {N M A L : ℕ} (p : SeparatedBoundedRatioPair N M L) :
    smallPositiveChannel A p ↔
      MacroscopicShallowSigma.hasSmallPositiveCanonicalHeight A L p.1.1 p.1.2 := by
  unfold smallPositiveChannel MacroscopicShallowSigma.hasSmallPositiveCanonicalHeight pairSigma
  norm_cast

end
end PaperC.V282.ResidualSectorMasks
