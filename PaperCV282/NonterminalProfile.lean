import PaperCV282.RemainingDeepProfile
import PaperCV282.SectorFiveProfile
import PaperCV282.CappedSectorSixProfile

/-!
# The proved profile with only terminal sector 8 remaining

The rational contribution and residual sectors 1 through 7 have genuine
uniform estimates. The capped reduction retains the exact real ceiling
on sector 8, and the uncapped reduction retains its actual residual mass.
Neither statement assumes or claims the missing terminal-sector bound.
-/

namespace PaperC.V282.NonterminalProfile

open PropositionSixteenOne ResidualSectorMass CappedSectorMass CappedRelationMass
open RemainingDeepProfile SectorFiveProfile SectorSixProfile CappedSectorSixProfile
open MacroscopicGeometry MacroscopicRelationProfile TwoWindowParity ProfileMonomials
open LogarithmicWordPowers

noncomputable section

/-- The full capped start mass satisfies the printed profile plus exactly the capped terminal sector. -/
theorem cappedStartMass_le_profile_add_terminal_eventually
    (betaMin betaMax delta epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M → ∀ T : ℝ, 0 ≤ T →
      cappedStartMass (M + L) L T (separatedPairs (macroscopicStarts M delta) L) ≤
        (M : ℝ) ^ epsilon * cappedProfile M ((2 : ℝ) ^ (L + 1)) T +
          cappedSectorMass 3 7 T ⌈(M : ℝ) ^ delta⌉₊ M L := by
  have heps : 0 < epsilon / 2 := by positivity
  have hbetaMax : 0 ≤ betaMax := (hbetaMin.trans hbeta).le
  obtain ⟨Mknown, hknown⟩ := knownMass_le_profile_eventually
    betaMin betaMax delta (epsilon / 2) hbetaMin hbeta hdelta heps
  obtain ⟨Mfive, hfive⟩ := macroscopic_sector_five_le_profile_eventually
    betaMin betaMax delta (epsilon / 2) hbetaMin hbeta hdelta heps
  obtain ⟨Msix, hsix⟩ := capped_sector_six_le_profile_eventually
    betaMin betaMax delta (epsilon / 2) hbetaMin hbeta hdelta heps
  obtain ⟨Mconstant, hconstant⟩ := polynomial_factor_le_rpow_eventually
    betaMax hbetaMax 2 0 (epsilon / 2) heps
  refine ⟨max Mknown (max Mfive (max Msix (max Mconstant 2))), ?_⟩
  intro M hM L hlower hupper T hT
  have hMtwo : 2 ≤ M := by omega
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hN := two_le_macroscopic_lowerEndpoint hMtwo hdelta
  have hk := hknown M (by omega) L hlower hupper
  have h5 := hfive M (by omega) L hlower hupper 3
  have h6 := hsix M (by omega) L hlower hupper 3 T hT
  have h2 : (2 : ℝ) ≤ (M : ℝ) ^ (epsilon / 2) := by
    simpa using hconstant M (by omega) L (by simpa using hupper)
  have hfinite := cappedStartMass_le_known_add_remaining_caps (M := M) (A := 3) (L := L) hN T
  have h5cap := cappedSectorMass_le_sectorMass 3 4 T ⌈(M : ℝ) ^ delta⌉₊ M L
  have hroot : Real.sqrt M ≤ (M : ℝ) ^ (2 / (3 : ℝ)) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hMone (by norm_num)
  have hmin : 0 ≤ min T ((2 : ℝ) ^ (L + 1)) := le_min hT (by positivity)
  have h6' : cappedSectorMass 3 5 T ⌈(M : ℝ) ^ delta⌉₊ M L ≤
      (M : ℝ) ^ (epsilon / 2) *
        ((M : ℝ) ^ (2 / (3 : ℝ)) * min T ((2 : ℝ) ^ (L + 1))) :=
    h6.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hroot hmin) (by positivity))
  have hfirst : (0 : ℝ) ≤ (M : ℝ) ^ (3 / (2 : ℝ)) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (6 : ℝ)) := by positivity
  have hthird : (0 : ℝ) ≤ (M : ℝ) ^ (2 / (3 : ℝ)) * min T ((2 : ℝ) ^ (L + 1)) := by positivity
  have hsum : cappedStartMass (M + L) L T (separatedPairs (macroscopicStarts M delta) L) ≤
      2 * (M : ℝ) ^ (epsilon / 2) * cappedProfile M ((2 : ℝ) ^ (L + 1)) T +
        cappedSectorMass 3 7 T ⌈(M : ℝ) ^ delta⌉₊ M L := by
    change cappedStartMass (M + L) L T (separatedPairs (macroscopicStarts M delta) L) ≤ _ at hfinite
    unfold cappedProfile
    nlinarith [mul_nonneg (Real.rpow_nonneg hMpos.le (epsilon / 2)) hfirst,
      mul_nonneg (Real.rpow_nonneg hMpos.le (epsilon / 2)) hthird]
  have hP := cappedProfile_nonneg hMpos.le (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (L + 1)) hT
  calc
    _ ≤ _ := hsum
    _ ≤ ((M : ℝ) ^ (epsilon / 2) * (M : ℝ) ^ (epsilon / 2)) *
        cappedProfile M ((2 : ℝ) ^ (L + 1)) T +
          cappedSectorMass 3 7 T ⌈(M : ℝ) ^ delta⌉₊ M L := by gcongr
    _ = _ := by rw [← Real.rpow_add hMpos, show epsilon / 2 + epsilon / 2 = epsilon by ring]

/-- The uncapped start mass has the raw profile plus exactly its genuine terminal residual mass. -/
theorem macroscopicStartMass_le_rawProfile_add_terminal_eventually
    (betaMin betaMax delta epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M →
      (macroscopicStartMassNat M L delta : ℝ) ≤
        (M : ℝ) ^ epsilon * rawProfile M ((2 : ℝ) ^ (L + 1)) +
          sectorMass 3 7 ⌈(M : ℝ) ^ delta⌉₊ M L := by
  have heps : 0 < epsilon / 2 := by positivity
  have hbetaMax : 0 ≤ betaMax := (hbetaMin.trans hbeta).le
  obtain ⟨Mknown, hknown⟩ := knownMass_le_profile_eventually
    betaMin betaMax delta (epsilon / 2) hbetaMin hbeta hdelta heps
  obtain ⟨Mfive, hfive⟩ := macroscopic_sector_five_le_profile_eventually
    betaMin betaMax delta (epsilon / 2) hbetaMin hbeta hdelta heps
  obtain ⟨Msix, hsix⟩ := macroscopic_sector_six_le_profile_eventually
    betaMin betaMax delta (epsilon / 2) hbetaMin hbeta hdelta heps
  obtain ⟨Mconstant, hconstant⟩ := polynomial_factor_le_rpow_eventually
    betaMax hbetaMax 2 0 (epsilon / 2) heps
  refine ⟨max Mknown (max Mfive (max Msix (max Mconstant 2))), ?_⟩
  intro M hM L hlower hupper
  have hMtwo : 2 ≤ M := by omega
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hk := hknown M (by omega) L hlower hupper
  have h5 := hfive M (by omega) L hlower hupper 3
  have h6 := hsix M (by omega) L hlower hupper 3
  have h2 : (2 : ℝ) ≤ (M : ℝ) ^ (epsilon / 2) := by
    simpa using hconstant M (by omega) L (by simpa using hupper)
  have hfinite := macroscopicStartMass_eq_known_add_remaining 3 (L := L) hMtwo hdelta
  unfold remainingMass at hfinite
  have hroot : Real.sqrt M ≤ (M : ℝ) ^ (2 / (3 : ℝ)) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hMone (by norm_num)
  have h6' : sectorMass 3 5 ⌈(M : ℝ) ^ delta⌉₊ M L ≤
      (M : ℝ) ^ (epsilon / 2) * ((M : ℝ) ^ (2 / (3 : ℝ)) * (2 : ℝ) ^ (L + 1)) :=
    h6.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hroot (by positivity)) (by positivity))
  have hfirst : (0 : ℝ) ≤ (M : ℝ) ^ (3 / (2 : ℝ)) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (6 : ℝ)) := by positivity
  have hthird : (0 : ℝ) ≤ (M : ℝ) ^ (2 / (3 : ℝ)) * (2 : ℝ) ^ (L + 1) := by positivity
  have hsum : (macroscopicStartMassNat M L delta : ℝ) ≤
      2 * (M : ℝ) ^ (epsilon / 2) * rawProfile M ((2 : ℝ) ^ (L + 1)) +
        sectorMass 3 7 ⌈(M : ℝ) ^ delta⌉₊ M L := by
    unfold rawProfile
    nlinarith [mul_nonneg (Real.rpow_nonneg hMpos.le (epsilon / 2)) hfirst,
      mul_nonneg (Real.rpow_nonneg hMpos.le (epsilon / 2)) hthird]
  have hP := rawProfile_nonneg hMpos.le (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (L + 1))
  calc
    _ ≤ _ := hsum
    _ ≤ ((M : ℝ) ^ (epsilon / 2) * (M : ℝ) ^ (epsilon / 2)) * rawProfile M ((2 : ℝ) ^ (L + 1)) +
        sectorMass 3 7 ⌈(M : ℝ) ^ delta⌉₊ M L := by gcongr
    _ = _ := by rw [← Real.rpow_add hMpos, show epsilon / 2 + epsilon / 2 = epsilon by ring]

end
end PaperC.V282.NonterminalProfile
