import PaperCV282.MacroscopicSmallProductProfile
import PaperCV282.MacroscopicSmallHeightSector
import PaperCV282.MacroscopicShallowSectors
import PaperCV282.ProfileMonomials

/-!
# Completed early rows and the remaining deep residual mass

All three rows of Proposition 3.12 now have proofs with the actual
canonical sector weights. The aligned fourth row is zero. The exact
remaining part of the full start mass consists of sectors 5 through 8.
-/

namespace PaperC.V282.MacroscopicEarlyProfile

open PropositionSixteenOne ResidualSectorMass MacroscopicRelationProfile
open MacroscopicSmallProductProfile MacroscopicSmallHeightSector MacroscopicShallowSectors
open RationalMassAsymptotics LogarithmicWordPowers ProfileMonomials
open scoped BigOperators

noncomputable section

/-- Rational mass plus the first four genuine residual sectors. -/
def earlyMass (A N M L : ℕ) : ℝ :=
  systematicMass A N M L + sectorMass A 0 N M L + sectorMass A 1 N M L +
    sectorMass A 2 N M L + sectorMass A 3 N M L

/-- Exact identification of what remains after the completed early contribution. -/
theorem macroscopicStartMass_eq_early_add_deep
    (A : ℕ) {M L : ℕ} {delta : ℝ} (hM : 2 ≤ M) (hdelta : 0 < delta) :
    (macroscopicStartMassNat M L delta : ℝ) =
      earlyMass A ⌈(M : ℝ) ^ delta⌉₊ M L +
        sectorMass A 4 ⌈(M : ℝ) ^ delta⌉₊ M L +
        sectorMass A 5 ⌈(M : ℝ) ^ delta⌉₊ M L +
        sectorMass A 6 ⌈(M : ℝ) ^ delta⌉₊ M L +
        sectorMass A 7 ⌈(M : ℝ) ^ delta⌉₊ M L := by
  rw [macroscopicStartMass_eq_systematic_add_sectors A hM hdelta]
  simp [earlyMass, Fin.sum_univ_succ]
  ring

/-- The three literal estimates of Proposition 3.12, under one common threshold. -/
theorem proposition_three_twelve
    (betaMin betaMax delta epsilon : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M →
      sectorMass 3 0 ⌈(M : ℝ) ^ delta⌉₊ M L ≤ (M : ℝ) ^ epsilon *
        ((M : ℝ) ^ (3 / (2 : ℝ)) + (M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (2 : ℝ))) ∧
      sectorMass 3 1 ⌈(M : ℝ) ^ delta⌉₊ M L ≤ (M : ℝ) ^ epsilon *
        ((M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (2 : ℝ)) +
          (M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (3 : ℝ))) ∧
      sectorMass 3 2 ⌈(M : ℝ) ^ delta⌉₊ M L ≤ (M : ℝ) ^ epsilon *
        ((M : ℝ) ^ (3 / (2 : ℝ)) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (6 : ℝ))) ∧
      sectorMass 3 3 ⌈(M : ℝ) ^ delta⌉₊ M L = 0 := by
  obtain ⟨Mone, hone⟩ := sector_one_mass_le_profile_eventually
    betaMin betaMax delta epsilon hbetaMin hbeta hdelta hepsilon
  obtain ⟨Mtwo, htwo⟩ := sector_two_mass_le_rational_profile_eventually
    betaMin betaMax delta epsilon hbetaMin hbeta hdelta hepsilon
  obtain ⟨Mthree, hthree⟩ := sector_three_mass_le_profile_eventually
    betaMin betaMax delta epsilon hbetaMin hbeta hdelta hepsilon
  obtain ⟨Mfour, hfour⟩ := sector_four_mass_eq_zero_eventually
    betaMin betaMax delta hbetaMin hbeta hdelta 3
  refine ⟨max Mone (max Mtwo (max Mthree Mfour)), ?_⟩
  intro M hM L hlower hupper
  exact ⟨hone M (by omega) L hlower hupper 3 (by omega),
    htwo M (by omega) L hlower hupper 3 (by omega),
    hthree M (by omega) L hlower hupper 3,
    hfour M (by omega) L hlower hupper⟩

/-- The completed contribution is controlled by the first two raw monomials. -/
theorem earlyMass_le_profile_eventually
    (betaMin betaMax delta epsilon : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M →
      earlyMass 3 ⌈(M : ℝ) ^ delta⌉₊ M L ≤ (M : ℝ) ^ epsilon *
        ((M : ℝ) ^ (3 / (2 : ℝ)) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (6 : ℝ)) +
          (M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (2 / (3 : ℝ))) := by
  have heps : 0 < epsilon / 2 := by linarith
  have hbetaMax : 0 ≤ betaMax := (hbetaMin.trans hbeta).le
  obtain ⟨Msector, hsector⟩ := proposition_three_twelve
    betaMin betaMax delta (epsilon / 2) hbetaMin hbeta hdelta heps
  obtain ⟨Mrational, hrational⟩ := systematicMass_uniform_profile betaMax hbetaMax (epsilon / 2) heps
  obtain ⟨Mconstant, hconstant⟩ := polynomial_factor_le_rpow_eventually betaMax hbetaMax 5 0 (epsilon / 2) heps
  refine ⟨max Msector (max Mrational (max Mconstant 1)), ?_⟩
  intro M hM L hlower hupper
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  obtain ⟨hone, htwo, hthree, hfour⟩ := hsector M (by omega) L hlower hupper
  have hrat := hrational M (by omega) L (by simpa using hupper) ⌈(M : ℝ) ^ delta⌉₊ 3 (by omega)
  have hf : (5 : ℝ) ≤ (M : ℝ) ^ (epsilon / 2) := by
    simpa using hconstant M (by omega) L (by simpa using hupper)
  let Q : ℝ := (2 : ℝ) ^ (L + 1)
  let E : ℝ := (M : ℝ) ^ (epsilon / 2)
  let X : ℝ := (M : ℝ) ^ (3 / (2 : ℝ)) * Q ^ (1 / (6 : ℝ))
  let Y : ℝ := (M : ℝ) * Q ^ (2 / (3 : ℝ))
  have hQ : 1 ≤ Q := by dsimp [Q]; exact one_le_pow₀ (by norm_num)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hX : 0 ≤ X := by dsimp [X, Q]; positivity
  have hY : 0 ≤ Y := by dsimp [Y, Q]; positivity
  have hhost : (M : ℝ) ^ (3 / (2 : ℝ)) ≤ X := host_monomial_le_shallow (by positivity) hQ
  have hhalves : (M : ℝ) * Q ^ (1 / (2 : ℝ)) + (M : ℝ) * Q ^ (1 / (3 : ℝ)) ≤ 2 * Y :=
    rational_monomials_le_two_moderate (by positivity) hQ
  have hhalf : (M : ℝ) * Q ^ (1 / (2 : ℝ)) ≤ Y :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hQ (by norm_num)) (by positivity)
  have hsum : earlyMass 3 ⌈(M : ℝ) ^ delta⌉₊ M L ≤ 5 * E * (X + Y) := by
    have hr : systematicMass 3 ⌈(M : ℝ) ^ delta⌉₊ M L ≤ E * (2 * Y) := by
      refine hrat.trans ?_
      dsimp [E]
      have hhalves' : (M : ℝ) * (Q ^ (1 / (2 : ℝ)) + Q ^ (1 / (3 : ℝ))) ≤ 2 * Y := by nlinarith
      exact mul_le_mul_of_nonneg_left hhalves' (by positivity)
    have h1 : sectorMass 3 0 ⌈(M : ℝ) ^ delta⌉₊ M L ≤ E * (X + Y) :=
      hone.trans (mul_le_mul_of_nonneg_left (add_le_add hhost hhalf) hE)
    have h2 : sectorMass 3 1 ⌈(M : ℝ) ^ delta⌉₊ M L ≤ E * (2 * Y) :=
      htwo.trans (mul_le_mul_of_nonneg_left hhalves hE)
    unfold earlyMass
    change sectorMass 3 2 ⌈(M : ℝ) ^ delta⌉₊ M L ≤ E * X at hthree
    nlinarith [mul_nonneg hE hX]
  calc
    _ ≤ _ := hsum
    _ ≤ E * E * (X + Y) := by dsimp [E] at *; gcongr
    _ = (M : ℝ) ^ epsilon * (X + Y) := by
      dsimp [E]
      rw [← Real.rpow_add hMpos, show epsilon / 2 + epsilon / 2 = epsilon by ring]

end
end PaperC.V282.MacroscopicEarlyProfile
