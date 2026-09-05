import PaperCV282.MacroscopicSmallProductLoss
import PaperCV282.SmallProductMass
import PaperCV282.HostRealPowers
import PaperCV282.RationalMassAsymptotics

/-!
# The first residual sector in the full logarithmic band

The exact small-product condition `P# <= M` gives a uniform pointwise
subpolynomial bound for `2^tau`. The zero-systematic branch is supported on
relational hosts, while the positive-systematic branch is paid by the
base-two rational mass. This proves the first row of Proposition 3.12
without a moment estimate for certificate populations.
-/

namespace PaperC.V282.MacroscopicSmallProductProfile

open PropositionSixteenOne ResidualSectorPartition ResidualSectorMass ResidualSectorMasks
open MacroscopicGeometry MacroscopicSmallProductLoss SmallProductMass HostRealPowers
open RationalMassAsymptotics LogarithmicWordPowers FullHostComparison

noncomputable section

/-- The true first-sector residual mass has the host-plus-rational profile,
uniformly in the coding parameter after all ambient thresholds. -/
theorem sector_one_mass_le_profile_eventually
    (betaMin betaMax delta epsilon : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M → ∀ A : ℕ, 1 ≤ A →
      sectorMass A 0 ⌈(M : ℝ) ^ delta⌉₊ M L ≤
        (M : ℝ) ^ epsilon *
          ((M : ℝ) ^ (3 / (2 : ℝ)) +
            (M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (2 : ℝ))) := by
  have hbetaMax : 0 < betaMax := hbetaMin.trans hbeta
  have hthird : 0 < epsilon / 3 := by positivity
  obtain ⟨Mtau, htau⟩ := two_pow_pairTau_le_rpow_eventually
    betaMin betaMax delta (epsilon / 3) hbetaMin hbeta hdelta hthird
  obtain ⟨Mhost, hhost⟩ := card_startRelationHosts_le_real_profile
    betaMax hbetaMax.le (epsilon / 3) hthird
  obtain ⟨Mrational, hrational⟩ := systematicMass_uniform_profile
    betaMax hbetaMax.le (epsilon / 3) hthird
  obtain ⟨Mconstant, hconstant⟩ := polynomial_factor_le_rpow_eventually
    betaMax hbetaMax.le 4 0 (epsilon / 3) hthird
  refine ⟨max Mtau (max Mhost (max Mrational (max Mconstant 2))), ?_⟩
  intro M hM L hLmin hLmax A hA
  have hMtau : Mtau ≤ M := (le_max_left _ _).trans hM
  have hrest : max Mhost (max Mrational (max Mconstant 2)) ≤ M := (le_max_right _ _).trans hM
  have hMhost : Mhost ≤ M := (le_max_left _ _).trans hrest
  have htail : max Mrational (max Mconstant 2) ≤ M := (le_max_right _ _).trans hrest
  have hMrational : Mrational ≤ M := (le_max_left _ _).trans htail
  have htail' : max Mconstant 2 ≤ M := (le_max_right _ _).trans htail
  have hMconstant : Mconstant ≤ M := (le_max_left _ _).trans htail'
  have hMtwo : 2 ≤ M := (le_max_right _ _).trans htail'
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hN : 2 ≤ ⌈(M : ℝ) ^ delta⌉₊ := two_le_macroscopic_lowerEndpoint hMtwo hdelta
  let s : Finset (ℕ × ℕ) := sectorMask (M := M) (L := L) A hN 0
  let u : ℝ := (M : ℝ) ^ (epsilon / 3)
  let Q : ℝ := (2 : ℝ) ^ (L + 1)
  let P : ℝ := (M : ℝ) ^ (3 / (2 : ℝ)) + (M : ℝ) * Q ^ (1 / (2 : ℝ))
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hP : 0 ≤ P := by dsimp [P, Q]; positivity
  have hfour : (4 : ℝ) ≤ u := by
    have h := hconstant M hMconstant L (by exact_mod_cast hLmax)
    simpa [u] using h
  have hs : s ⊆ Finset.Icc 2 M ×ˢ Finset.Icc 2 M :=
    (sectorMask_subset hN 0).trans
      (separatedPairs_macroscopicStarts_subset_Icc_product hMtwo hdelta L)
  have hh : ((startRelationHosts (M + L) L s).card : ℝ) ≤
      u * (M : ℝ) ^ (3 / (2 : ℝ)) :=
    hhost M hMhost L (by exact_mod_cast hLmax) s hs
  have hr : (BoundedRatioGeometry.boundedRationalMass ⌈(M : ℝ) ^ delta⌉₊ M A L 2 : ℝ) ≤
      u * ((M : ℝ) * (Q ^ (1 / (2 : ℝ)) + Q ^ (1 / (3 : ℝ)))) := by
    have h := hrational M hMrational L (by exact_mod_cast hLmax) ⌈(M : ℝ) ^ delta⌉₊ A hA
    rwa [systematicMass_eq_boundedRationalMass hN] at h
  have hfinite : sectorMass A 0 ⌈(M : ℝ) ^ delta⌉₊ M L ≤
      u * (((startRelationHosts (M + L) L s).card : ℝ) +
        2 * (BoundedRatioGeometry.boundedRationalMass ⌈(M : ℝ) ^ delta⌉₊ M A L 2 : ℝ)) := by
    apply sectorMass_le_factor_hosts_add_rational hN 0 hu
    intro p hp
    have hcoords := mem_separatedBoundedRatioPairs.mp p.2
    exact htau M hMtau L hLmin hLmax _ hN A p hcoords.1 hcoords.2.1
      (sectorOf_eq_one_iff.mp (mem_sectorPairs.mp hp))
  have hQ : 1 ≤ Q := by dsimp [Q]; exact one_le_pow₀ (by norm_num)
  have hroots : Q ^ (1 / (3 : ℝ)) ≤ Q ^ (1 / (2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hQ (by norm_num)
  have hrHalf :
      (BoundedRatioGeometry.boundedRationalMass ⌈(M : ℝ) ^ delta⌉₊ M A L 2 : ℝ) ≤
        2 * u * (M : ℝ) * Q ^ (1 / (2 : ℝ)) := by
    refine hr.trans ?_
    have hrootNonneg : 0 ≤ Q ^ (1 / (2 : ℝ)) := by positivity
    nlinarith [mul_nonneg hu (Nat.cast_nonneg M),
      mul_le_mul_of_nonneg_left hroots (mul_nonneg hu (Nat.cast_nonneg M))]
  have hsum : ((startRelationHosts (M + L) L s).card : ℝ) +
      2 * (BoundedRatioGeometry.boundedRationalMass ⌈(M : ℝ) ^ delta⌉₊ M A L 2 : ℝ) ≤
        4 * u * P := by
    have hhostNonneg : 0 ≤ u * (M : ℝ) ^ (3 / (2 : ℝ)) := by positivity
    dsimp [P]
    nlinarith
  calc
    sectorMass A 0 ⌈(M : ℝ) ^ delta⌉₊ M L ≤
        u * (((startRelationHosts (M + L) L s).card : ℝ) +
          2 * (BoundedRatioGeometry.boundedRationalMass ⌈(M : ℝ) ^ delta⌉₊ M A L 2 : ℝ)) := hfinite
    _ ≤ u * (4 * u * P) := mul_le_mul_of_nonneg_left hsum hu
    _ ≤ u * (u * u * P) := by gcongr
    _ = (M : ℝ) ^ epsilon * P := by
      dsimp [u]
      rw [← mul_assoc, ← mul_assoc, ← Real.rpow_add hMpos, ← Real.rpow_add hMpos]
      congr 2
      ring

end
end PaperC.V282.MacroscopicSmallProductProfile
