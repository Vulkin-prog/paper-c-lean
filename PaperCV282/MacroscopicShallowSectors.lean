import PaperCV282.ResidualSectorMasks
import PaperCV282.MacroscopicShallowProfile
import PaperCV282.MacroscopicAlignedExclusion

/-!
# The literal third and fourth sectors

These endpoints apply the proved broad shallow profile and aligned
exclusion to the new eight-sector partition, with the original real
residual masses. Sector indices are zero-based in Lean.
-/

namespace PaperC.V282.MacroscopicShallowSectors

open PropositionSixteenOne ResidualSectorPartition ResidualSectorMass ResidualSectorMasks
open MacroscopicShallowProfile MacroscopicAlignedExclusion MacroscopicGeometry

noncomputable section

/-- The literal third sector is a submask of the broad shallow population. -/
theorem sector_three_mask_subset {M A L : ℕ} {delta : ℝ}
    (hN : 2 ≤ ⌈(M : ℝ) ^ delta⌉₊) :
    sectorMask (M := M) (L := L) A hN (2 : Fin 8) ⊆ broadShallowPairs M A L delta := by
  intro xy hxy
  obtain ⟨hp, hs⟩ := mem_sectorMask.mp hxy
  have ht := sectorOf_eq_three_iff.mp hs
  apply (mem_broadShallowPairs M A L delta xy).mpr
  refine ⟨hp, ?_, ht.2.2⟩
  exact fun hsmall => ht.2.1 ((smallPositiveChannel_iff_test ⟨xy, hp⟩).mpr hsmall)

/-- The third row of Proposition 3.12, for the actual residual sector mass. -/
theorem sector_three_mass_le_profile_eventually
    (betaMin betaMax delta epsilon : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M → ∀ A : ℕ,
      sectorMass A (2 : Fin 8) ⌈(M : ℝ) ^ delta⌉₊ M L ≤
        (M : ℝ) ^ epsilon *
          ((M : ℝ) ^ (3 / (2 : ℝ)) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (6 : ℝ))) := by
  obtain ⟨Mcore, hcore⟩ := relationWeightMass_le_shallow_profile_eventually
    betaMin betaMax delta epsilon hbetaMin hbeta hdelta hepsilon
  refine ⟨max Mcore 2, ?_⟩
  intro M hM L hlower hupper A
  have hN := two_le_macroscopic_lowerEndpoint ((le_max_right _ _).trans hM) hdelta
  exact (sectorMass_le_relationWeightMass (A := A) (L := L) hN (2 : Fin 8)).trans
    (hcore M ((le_max_left _ _).trans hM) L hlower hupper A _ (sector_three_mask_subset hN))

/-- The aligned fourth population is empty beyond a uniform macroscopic threshold. -/
theorem sector_four_pairs_empty_eventually
    (betaMin betaMax delta : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hdelta : 0 < delta) (A : ℕ) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M →
      ∀ hN : 2 ≤ ⌈(M : ℝ) ^ delta⌉₊,
      sectorPairs ⌈(M : ℝ) ^ delta⌉₊ M A L hN (3 : Fin 8) = ∅ := by
  classical
  obtain ⟨Mcore, hcore⟩ := aligned_component_count_le_sixth_eventually
    betaMin betaMax delta hbetaMin hbeta hdelta A
  refine ⟨Mcore, ?_⟩
  intro M hM L hlower hupper hN
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have htests := sectorOf_eq_four_iff.mp (mem_sectorPairs.mp hp)
  obtain ⟨hx, hy, _⟩ := mem_separatedBoundedRatioPairs.mp p.2
  have hbound := hcore M hM L hlower hupper p.1.1 hx p.1.2 hy htests.2.2.2
  exact htests.2.2.1 hbound

/-- The fourth sector contributes exactly zero residual mass. -/
theorem sector_four_mass_eq_zero_eventually
    (betaMin betaMax delta : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hdelta : 0 < delta) (A : ℕ) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M →
      sectorMass A (3 : Fin 8) ⌈(M : ℝ) ^ delta⌉₊ M L = 0 := by
  obtain ⟨Mcore, hcore⟩ := sector_four_pairs_empty_eventually
    betaMin betaMax delta hbetaMin hbeta hdelta A
  refine ⟨max Mcore 2, ?_⟩
  intro M hM L hlower hupper
  have hN := two_le_macroscopic_lowerEndpoint ((le_max_right _ _).trans hM) hdelta
  have hempty := hcore M ((le_max_left _ _).trans hM) L hlower hupper hN
  simp [sectorMass, dif_pos hN, sectorMassNat, hempty]

end
end PaperC.V282.MacroscopicShallowSectors
