import PaperCV282.MacroscopicEarlyProfile
import PaperCV282.SizeTwoHostAsymptotics
import PaperCV282.CappedSectorMass

/-!
# Isolating the remaining deep populations

This intermediate grouping collects the rational part and sectors
1,2,3,4,7, isolating sectors 5,6,8 in exact finite identities. Capping
preserves those three separate residual ceilings uniformly in the real cap.
NonterminalProfile subsequently inserts the completed bounds for sectors
5 and 6, leaving only terminal sector 8 as the final remainder.
-/

namespace PaperC.V282.RemainingDeepProfile

open PropositionSixteenOne ResidualSectorMass MacroscopicRelationProfile
open MacroscopicEarlyProfile SizeTwoHostAsymptotics LogarithmicWordPowers
open CappedRelationMass CappedSectorMass MacroscopicGeometry TwoWindowParity
open scoped BigOperators

noncomputable section

/-- The rational contribution and all five residual sectors with closed profiles. -/
def knownMass (A N M L : ℕ) : ℝ := earlyMass A N M L + sectorMass A 6 N M L

/-- The three residual populations that remain after this closure. -/
def remainingMass (A N M L : ℕ) : ℝ :=
  sectorMass A 4 N M L + sectorMass A 5 N M L + sectorMass A 7 N M L

/-- Exact remaining mass, without dropping or repeating any population. -/
theorem macroscopicStartMass_eq_known_add_remaining
    (A : ℕ) {M L : ℕ} {delta : ℝ} (hM : 2 ≤ M) (hdelta : 0 < delta) :
    (macroscopicStartMassNat M L delta : ℝ) =
      knownMass A ⌈(M : ℝ) ^ delta⌉₊ M L + remainingMass A ⌈(M : ℝ) ^ delta⌉₊ M L := by
  rw [macroscopicStartMass_eq_early_add_deep A hM hdelta]
  unfold knownMass remainingMass
  ring

theorem remainingMass_nonneg (A N M L : ℕ) : 0 ≤ remainingMass A N M L := by
  exact add_nonneg (add_nonneg (sectorMass_nonneg A 4 N M L)
    (sectorMass_nonneg A 5 N M L)) (sectorMass_nonneg A 7 N M L)

/-- The completed part has the first two monomials, uniformly in the full band. -/
theorem knownMass_le_profile_eventually
    (betaMin betaMax delta epsilon : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M →
      knownMass 3 ⌈(M : ℝ) ^ delta⌉₊ M L ≤ (M : ℝ) ^ epsilon *
        ((M : ℝ) ^ (3 / (2 : ℝ)) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (6 : ℝ)) +
          (M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (2 / (3 : ℝ))) := by
  have heps : 0 < epsilon / 2 := by linarith
  have hbetaMax : 0 ≤ betaMax := (hbetaMin.trans hbeta).le
  obtain ⟨Mearly, hearly⟩ := earlyMass_le_profile_eventually
    betaMin betaMax delta (epsilon / 2) hbetaMin hbeta hdelta heps
  obtain ⟨Mseven, hseven⟩ := macroscopic_sector_seven_le_profile_eventually
    betaMin betaMax (epsilon / 2) hbetaMin hbetaMax heps
  obtain ⟨Mconstant, hconstant⟩ := polynomial_factor_le_rpow_eventually
    betaMax hbetaMax 2 0 (epsilon / 2) heps
  refine ⟨max Mearly (max Mseven (max Mconstant 1)), ?_⟩
  intro M hM L hlower hupper
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have h1 := hearly M (by omega) L hlower hupper
  have h2 := hseven M (by omega) L hlower hupper delta hdelta 3
  have hconstant' : (2 : ℝ) ≤ (M : ℝ) ^ (epsilon / 2) := by
    simpa using hconstant M (by omega) L (by simpa using hupper)
  let X : ℝ := (M : ℝ) ^ (3 / (2 : ℝ)) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (6 : ℝ))
  let Y : ℝ := (M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (2 / (3 : ℝ))
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hsum : knownMass 3 ⌈(M : ℝ) ^ delta⌉₊ M L ≤
      2 * (M : ℝ) ^ (epsilon / 2) * (X + Y) := by
    unfold knownMass
    change earlyMass 3 ⌈(M : ℝ) ^ delta⌉₊ M L ≤ (M : ℝ) ^ (epsilon / 2) * (X + Y) at h1
    change sectorMass 3 6 ⌈(M : ℝ) ^ delta⌉₊ M L ≤ (M : ℝ) ^ (epsilon / 2) * Y at h2
    nlinarith [mul_nonneg (Real.rpow_nonneg hMpos.le (epsilon / 2)) hX]
  calc
    _ ≤ _ := hsum
    _ ≤ ((M : ℝ) ^ (epsilon / 2) * (M : ℝ) ^ (epsilon / 2)) * (X + Y) := by gcongr
    _ = _ := by rw [← Real.rpow_add hMpos, show epsilon / 2 + epsilon / 2 = epsilon by ring]

/-- Finite capped reduction keeps precisely sectors 5,6,8 capped. -/
theorem cappedStartMass_le_known_add_remaining_caps
    {N M A L : ℕ} (hN : 2 ≤ N) (T : ℝ) :
    cappedStartMass (M + L) L T (separatedBoundedRatioPairs N M L) ≤
      knownMass A N M L + cappedSectorMass A 4 T N M L +
        cappedSectorMass A 5 T N M L + cappedSectorMass A 7 T N M L := by
  have hbase := cappedStartMass_le_systematic_add_capped_sectors (M := M) (A := A) (L := L) hN T
  have h0 := cappedSectorMass_le_sectorMass A 0 T N M L
  have h1 := cappedSectorMass_le_sectorMass A 1 T N M L
  have h2 := cappedSectorMass_le_sectorMass A 2 T N M L
  have h3 := cappedSectorMass_le_sectorMass A 3 T N M L
  have h6 := cappedSectorMass_le_sectorMass A 6 T N M L
  simp only [Fin.sum_univ_succ] at hbase
  change cappedStartMass (M + L) L T (separatedBoundedRatioPairs N M L) ≤
    systematicMass A N M L + (cappedSectorMass A 0 T N M L +
      (cappedSectorMass A 1 T N M L + (cappedSectorMass A 2 T N M L +
        (cappedSectorMass A 3 T N M L + (cappedSectorMass A 4 T N M L +
          (cappedSectorMass A 5 T N M L + (cappedSectorMass A 6 T N M L +
            (cappedSectorMass A 7 T N M L + 0)))))))) at hbase
  unfold knownMass earlyMass
  linarith

/-- Uniform reduction of the capped start profile to the three outstanding masses. -/
theorem cappedStartMass_le_profile_add_remaining_caps_eventually
    (betaMin betaMax delta epsilon : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M → ∀ T : ℝ,
      cappedStartMass (M + L) L T (separatedPairs (macroscopicStarts M delta) L) ≤
        (M : ℝ) ^ epsilon *
          ((M : ℝ) ^ (3 / (2 : ℝ)) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (6 : ℝ)) +
            (M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (2 / (3 : ℝ))) +
        cappedSectorMass 3 4 T ⌈(M : ℝ) ^ delta⌉₊ M L +
        cappedSectorMass 3 5 T ⌈(M : ℝ) ^ delta⌉₊ M L +
        cappedSectorMass 3 7 T ⌈(M : ℝ) ^ delta⌉₊ M L := by
  obtain ⟨Mknown, hknown⟩ := knownMass_le_profile_eventually
    betaMin betaMax delta epsilon hbetaMin hbeta hdelta hepsilon
  refine ⟨max Mknown 2, ?_⟩
  intro M hM L hlower hupper T
  have hN := two_le_macroscopic_lowerEndpoint ((le_max_right _ _).trans hM) hdelta
  have hfinite := cappedStartMass_le_known_add_remaining_caps (M := M) (A := 3) (L := L) hN T
  change cappedStartMass (M + L) L T (separatedPairs (macroscopicStarts M delta) L) ≤ _ at hfinite
  have hbound := hknown M ((le_max_left _ _).trans hM) L hlower hupper
  linarith

end
end PaperC.V282.RemainingDeepProfile
