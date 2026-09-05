import PaperCV282.MacroscopicBoundedHosts
import PaperCV282.SectorFiveRank

/-!
# Complete fifth-sector profile

The exact eight-sector partition's fifth branch supplies a residual
component of size at most eleven. Its unconditional host count and exact
rank budget give the literal `M^(1+epsilon) Q_B^(2/3)` profile.
-/

namespace PaperC.V282.SectorFiveProfile

open ResidualSectorMass SectorFiveRank MacroscopicBoundedHosts MacroscopicGeometry

noncomputable section

/-- The fifth sector's full macroscopic profile, with the genuine residual weight.
The threshold precedes the word length and canonical selector. -/
theorem macroscopic_sector_five_le_profile_eventually
    (betaMin betaMax delta epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M → ∀ A : ℕ,
      sectorMass A 4 ⌈(M : ℝ) ^ delta⌉₊ M L ≤
        (M : ℝ) ^ epsilon * ((M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (2 / (3 : ℝ))) := by
  have heps : 0 < epsilon / 2 := by linarith
  obtain ⟨Mhost, hhost⟩ := card_boundedHosts_le_linear_profile_eventually
    11 betaMin betaMax (epsilon / 2) hbetaMin (hbetaMin.trans hbeta) heps
  obtain ⟨Mweight, hweight⟩ := sector_five_mass_le_host_card_eventually
    betaMin betaMax delta (epsilon / 2) hbetaMin hbeta hdelta heps
  refine ⟨max Mhost (max Mweight 2), ?_⟩
  intro M hM L hlower hupper A
  have hrest : max Mweight 2 ≤ M := (le_max_right _ _).trans hM
  have hMtwo : 2 ≤ M := (le_max_right _ _).trans hrest
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hN := two_le_macroscopic_lowerEndpoint hMtwo hdelta
  have hh := hhost M ((le_max_left _ _).trans hM) L hlower hupper
    ⌈(M : ℝ) ^ delta⌉₊ A hN
  have hw := hweight M ((le_max_left _ _).trans hrest) L hlower hupper A
  calc
    _ ≤ _ := hw
    _ ≤ ((M : ℝ) ^ (epsilon / 2) * M) *
        ((M : ℝ) ^ (epsilon / 2) * ((2 : ℝ) ^ (L + 1)) ^ (2 / (3 : ℝ))) :=
      mul_le_mul_of_nonneg_right hh (by positivity)
    _ = ((M : ℝ) ^ (epsilon / 2) * (M : ℝ) ^ (epsilon / 2)) *
        ((M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (2 / (3 : ℝ))) := by ring
    _ = _ := by rw [← Real.rpow_add hMpos, show epsilon / 2 + epsilon / 2 = epsilon by ring]

end
end PaperC.V282.SectorFiveProfile
