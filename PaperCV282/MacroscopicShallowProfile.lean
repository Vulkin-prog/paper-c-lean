import PaperCV282.HostRankMass
import PaperCV282.HostRealPowers
import PaperCV282.MacroscopicShallowSigma
import PaperCV282.MacroscopicPointwiseDefects

/-!
# The shallow host-and-rank profile on the macroscopic interval

After the positive small-channel test fails and `6*c# <= B`, even the
homogeneous mass on any chosen submask is bounded by
`M^epsilon * M^(3/2) * Q_B^(1/6)`. All error factors are proved uniformly;
the rank and host bounds are not assumptions of the final endpoint.
-/

namespace PaperC.V282.MacroscopicShallowProfile

open Affine PropositionSixteenOne ResidualComponentCounts
open MacroscopicGeometry TwoWindowParity HostRankMass HostRealPowers
open MacroscopicShallowSigma MacroscopicPointwiseDefects

noncomputable section

/-- The broad shallow mask forgets only the preceding large-product test. -/
def broadShallowPairs (M A L : ℕ) (delta : ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact (nonSmallSigmaPairs M A L delta).filter fun xy =>
    6 * canonicalResidualComponentCount A xy.1 xy.2 L ≤ L + 1

/-- The two tests used by the shallow estimate, on exactly the macroscopic mask. -/
theorem mem_broadShallowPairs (M A L : ℕ) (delta : ℝ) (xy : ℕ × ℕ) :
    xy ∈ broadShallowPairs M A L delta ↔
      xy ∈ separatedPairs (macroscopicStarts M delta) L ∧
      ¬ hasSmallPositiveCanonicalHeight A L xy.1 xy.2 ∧
      6 * canonicalResidualComponentCount A xy.1 xy.2 L ≤ L + 1 := by
  classical
  simp [broadShallowPairs, mem_nonSmallSigmaPairs, and_assoc]

/-- Every broad shallow pair has the original separated macroscopic geometry. -/
theorem broadShallowPairs_subset (M A L : ℕ) (delta : ℝ) :
    broadShallowPairs M A L delta ⊆ separatedPairs (macroscopicStarts M delta) L := by
  intro xy hxy
  exact ((mem_broadShallowPairs M A L delta xy).mp hxy).1

/-- The systematic and corrected-defect factors together remain subpolynomial. -/
theorem sigma_defect_factor_le_rpow_eventually
    (betaMin betaMax delta epsilon : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M → ∀ A x : ℕ,
      x ∈ macroscopicStarts M delta → ∀ y : ℕ,
      y ∈ macroscopicStarts M delta → ¬ hasSmallPositiveCanonicalHeight A L x y →
      (2 : ℝ) ^ RationalMassFinite.canonicalPairSigma A L x y *
        (2 : ℝ) ^ canonicalCorrectedDefectCount A x y L ≤ (M : ℝ) ^ epsilon := by
  have heps : 0 < epsilon / 2 := by linarith
  obtain ⟨Msigma, hsigma⟩ := two_pow_sigma_le_rpow_eventually betaMin betaMax
    hbetaMin (hbetaMin.trans hbeta) (epsilon / 2) heps
  obtain ⟨Mdefect, hdefect⟩ := two_pow_correctedDefect_le_rpow_eventually
    betaMin betaMax delta (epsilon / 2) hbetaMin hbeta hdelta heps
  refine ⟨max Msigma (max Mdefect 1), ?_⟩
  intro M hM L hlower hupper A x hx y hy hnot
  have hrest : max Mdefect 1 ≤ M := (le_max_right _ _).trans hM
  have hMpos : (0 : ℝ) < M := by exact_mod_cast
    (show 0 < M by have := (le_max_right _ _).trans hrest; omega)
  have hs := hsigma M ((le_max_left _ _).trans hM) L
    (by simpa using hlower) (by simpa using hupper) A x y hnot
  have hd := hdefect M ((le_max_left _ _).trans hrest) L hlower hupper A x hx y hy
  calc
    _ ≤ (M : ℝ) ^ (epsilon / 2) * (M : ℝ) ^ (epsilon / 2) :=
      mul_le_mul hs hd (by positivity) (by positivity)
    _ = (M : ℝ) ^ (epsilon / 2 + epsilon / 2) := (Real.rpow_add hMpos _ _).symm
    _ = _ := by congr 1; ring

/-- A proved pointwise envelope for the full homogeneous weight in the broad shallow mask. -/
theorem homogeneousWeight_le_shallow_profile_eventually
    (betaMin betaMax delta epsilon : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M → ∀ A : ℕ,
      ∀ xy ∈ broadShallowPairs M A L delta,
      ((2 ^ relationRho (twoStartSystem (M + L) xy.1 xy.2 L) - 1 : ℕ) : ℝ) ≤
        (M : ℝ) ^ epsilon * ((2 : ℝ) ^ (L + 1)) ^ (1 / (6 : ℝ)) := by
  obtain ⟨Mfactor, hfactor⟩ := sigma_defect_factor_le_rpow_eventually
    betaMin betaMax delta epsilon hbetaMin hbeta hdelta hepsilon
  refine ⟨max Mfactor 2, ?_⟩
  intro M hM L hlower hupper A xy hxy
  obtain ⟨hsep, hnot, hc⟩ := (mem_broadShallowPairs M A L delta xy).mp hxy
  obtain ⟨hx, hy, _⟩ := (mem_separatedPairs (macroscopicStarts M delta) L xy.1 xy.2).mp hsep
  let p : SeparatedBoundedRatioPair ⌈(M : ℝ) ^ delta⌉₊ M L := ⟨xy, hsep⟩
  have hN := two_le_macroscopic_lowerEndpoint ((le_max_right _ _).trans hM) hdelta
  have hpoint := homogeneousWeight_cast_le_shallow_factors (A := A) hN p hc
  have hf := hfactor M ((le_max_left _ _).trans hM) L hlower hupper A xy.1 hx xy.2 hy hnot
  exact hpoint.trans (mul_le_mul_of_nonneg_right hf (by positivity))

/-- The complete host-and-rank estimate, uniform in every submask of the broad shallow population. -/
theorem relationWeightMass_le_shallow_profile_eventually
    (betaMin betaMax delta epsilon : ℝ)
    (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M → ∀ A : ℕ,
      ∀ s : Finset (ℕ × ℕ), s ⊆ broadShallowPairs M A L delta →
      (relationWeightMass (M + L) L s : ℝ) ≤
        (M : ℝ) ^ epsilon *
          ((M : ℝ) ^ (3 / (2 : ℝ)) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (6 : ℝ))) := by
  have heps : 0 < epsilon / 2 := by linarith
  obtain ⟨Mpoint, hpoint⟩ := homogeneousWeight_le_shallow_profile_eventually
    betaMin betaMax delta (epsilon / 2) hbetaMin hbeta hdelta heps
  obtain ⟨Mhost, hhost⟩ := card_startRelationHosts_le_real_profile
    betaMax (hbetaMin.trans hbeta).le (epsilon / 2) heps
  refine ⟨max Mpoint (max Mhost 2), ?_⟩
  intro M hM L hlower hupper A s hs
  have hrest : max Mhost 2 ≤ M := (le_max_right _ _).trans hM
  have hMtwo : 2 ≤ M := (le_max_right _ _).trans hrest
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hsfull : s ⊆ Finset.Icc 2 M ×ˢ Finset.Icc 2 M :=
    hs.trans ((broadShallowPairs_subset M A L delta).trans
      (separatedPairs_macroscopicStarts_subset_Icc_product hMtwo hdelta L))
  have hh := hhost M ((le_max_left _ _).trans hrest) L (by simpa using hupper) s hsfull
  have hm := relationWeightMass_cast_le_hosts_mul (M + L) L
    ((M : ℝ) ^ (epsilon / 2) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (6 : ℝ))) s (by
      intro xy hxy
      have hxs : xy ∈ s := (Finset.mem_filter.mp hxy).1
      exact hpoint M ((le_max_left _ _).trans hM) L hlower hupper A xy (hs hxs))
  calc
    _ ≤ _ := hm
    _ ≤ ((M : ℝ) ^ (epsilon / 2) * (M : ℝ) ^ (3 / (2 : ℝ))) *
        ((M : ℝ) ^ (epsilon / 2) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (6 : ℝ))) :=
      mul_le_mul_of_nonneg_right hh (by positivity)
    _ = ((M : ℝ) ^ (epsilon / 2) * (M : ℝ) ^ (epsilon / 2)) *
        ((M : ℝ) ^ (3 / (2 : ℝ)) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (6 : ℝ))) := by ring
    _ = _ := by rw [← Real.rpow_add hMpos, show epsilon / 2 + epsilon / 2 = epsilon by ring]

end
end PaperC.V282.MacroscopicShallowProfile
