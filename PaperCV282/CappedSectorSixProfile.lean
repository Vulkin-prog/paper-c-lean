import PaperCV282.SectorSixProfile
import PaperCV282.CappedSectorMass

/-!
# The sixth residual sector with an arbitrary real ceiling

The square-root host count and the corrected-defect factor are chosen
before the ceiling. Taking the latter factor outside the minimum keeps
the exact `min(T,Q_B)` dependence needed for the capped profile.
-/

namespace PaperC.V282.CappedSectorSixProfile

open PropositionSixteenOne ResidualSectorPartition ResidualSectorMass CappedSectorMass
open SectorSixProfile MacroscopicPointwiseDefects MacroscopicGeometry

noncomputable section

/-- The genuine capped sixth-sector mass, uniformly before the coding parameter and the real cap. -/
theorem capped_sector_six_le_profile_eventually
    (betaMin betaMax delta epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M → ∀ A : ℕ, ∀ T : ℝ, 0 ≤ T →
      cappedSectorMass A 5 T ⌈(M : ℝ) ^ delta⌉₊ M L ≤
        (M : ℝ) ^ epsilon * (Real.sqrt M * min T ((2 : ℝ) ^ (L + 1))) := by
  have heps : 0 < epsilon / 2 := by positivity
  obtain ⟨Mhost, hhost⟩ := card_sector_six_le_half_profile_eventually
    betaMin betaMax delta (epsilon / 2) hbetaMin (hbetaMin.trans hbeta) hdelta heps
  obtain ⟨Mdefect, hdefect⟩ := two_pow_correctedDefect_le_rpow_eventually
    betaMin betaMax delta (epsilon / 2) hbetaMin hbeta hdelta heps
  refine ⟨max Mhost (max Mdefect 2), ?_⟩
  intro M hM L hlower hupper A T hT
  have hMtwo : 2 ≤ M := by omega
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hN : 2 ≤ ⌈(M : ℝ) ^ delta⌉₊ := two_le_macroscopic_lowerEndpoint hMtwo hdelta
  have hE : (1 : ℝ) ≤ (M : ℝ) ^ (epsilon / 2) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ M by omega)) heps.le
  have hc := hhost M (by omega) L hlower hupper A hN
  have hw : ∀ pair ∈ sectorPairs ⌈(M : ℝ) ^ delta⌉₊ M A L hN 5,
      (residualWeight A hN pair : ℝ) ≤ (M : ℝ) ^ (epsilon / 2) * (2 : ℝ) ^ (L + 1) := by
    intro pair hpair
    have hgeo := mem_separatedBoundedRatioPairs.mp pair.property
    have hd := hdefect M (by omega) L hlower hupper A pair.1.1 hgeo.1 pair.1.2 hgeo.2.1
    exact (residualWeight_cast_le_defect_mul_wordCount hN pair (mem_sectorPairs.mp hpair)).trans
      (mul_le_mul_of_nonneg_right hd (by positivity))
  have hfinite := cappedSectorMass_le_card_mul_envelope_min hN 5 hE hT hw
  have hmin : 0 ≤ min T ((2 : ℝ) ^ (L + 1)) := le_min hT (by positivity)
  calc
    _ ≤ _ := hfinite
    _ ≤ ((M : ℝ) ^ (epsilon / 2) * Real.sqrt M) * (M : ℝ) ^ (epsilon / 2) *
        min T ((2 : ℝ) ^ (L + 1)) := by gcongr
    _ = ((M : ℝ) ^ (epsilon / 2) * (M : ℝ) ^ (epsilon / 2)) *
        (Real.sqrt M * min T ((2 : ℝ) ^ (L + 1))) := by ring
    _ = _ := by rw [← Real.rpow_add hMpos, show epsilon / 2 + epsilon / 2 = epsilon by ring]

end
end PaperC.V282.CappedSectorSixProfile
