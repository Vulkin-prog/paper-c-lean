import PaperCV282.NonterminalProfile
import PaperCV282.SectorEightProfile
import PaperCV282.HostRealPowers

/-!
# Complete macroscopic start and full-value relation profiles

The genuine eighth-sector estimate closes the earlier nonterminal
reductions. The full-value comparison uses the unrestricted arithmetic
hosts. Every displayed word factor remains Q_B=2^(L+1); the common real
ceiling is chosen after the threshold. These endpoints concern the literal
macroscopic mask, with separate names for the raw and interpolated bounds.
-/

namespace PaperC.V282.WholeRelationProfile

open NonterminalProfile SectorEightProfile HostRealPowers ProfileMonomials
open MacroscopicGeometry MacroscopicRelationProfile TwoWindowParity TwoWindowSquareHosts
open CappedRelationMass ResidualSectorMass CappedSectorMass LogarithmicWordPowers

noncomputable section

/-- The three-term start profile of Theorem 3.1 on the actual macroscopic domain. -/
theorem theorem_three_one_raw_macroscopic
    (betaMin betaMax delta epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log M →
      (macroscopicStartMassNat M L delta : ℝ) ≤
        (M : ℝ) ^ epsilon * rawProfile M ((2 : ℝ) ^ (L + 1)) := by
  have heps : 0 < epsilon / 2 := by positivity
  obtain ⟨Mnonterminal, hnonterminal⟩ := macroscopicStartMass_le_rawProfile_add_terminal_eventually
    betaMin betaMax delta (epsilon / 2) hbetaMin hbeta hdelta heps
  obtain ⟨Mterminal, hterminal⟩ := macroscopic_sector_eight_le_profile_eventually
    betaMin betaMax delta (epsilon / 2) hbetaMin hbeta hdelta heps
  obtain ⟨Mconstant, hconstant⟩ := polynomial_factor_le_rpow_eventually
    betaMax (hbetaMin.trans hbeta).le 2 0 (epsilon / 2) heps
  refine ⟨max Mnonterminal (max Mterminal (max Mconstant 1)), ?_⟩
  intro M hM L hlower hupper
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hn := hnonterminal M (by omega) L hlower hupper
  have ht := hterminal M (by omega) L hlower hupper 3 (by omega)
  have h2 : (2 : ℝ) ≤ (M : ℝ) ^ (epsilon / 2) := by
    simpa using hconstant M (by omega) L (by simpa using hupper)
  have hfirst : (0 : ℝ) ≤ (M : ℝ) ^ (3 / (2 : ℝ)) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (6 : ℝ)) := by positivity
  have hsum : (macroscopicStartMassNat M L delta : ℝ) ≤
      2 * (M : ℝ) ^ (epsilon / 2) * rawProfile M ((2 : ℝ) ^ (L + 1)) := by
    unfold rawProfile at *
    nlinarith [mul_nonneg (Real.rpow_nonneg hMpos.le (epsilon / 2)) hfirst]
  have hP := rawProfile_nonneg hMpos.le (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (L + 1))
  calc
    _ ≤ _ := hsum
    _ ≤ ((M : ℝ) ^ (epsilon / 2) * (M : ℝ) ^ (epsilon / 2)) * rawProfile M ((2 : ℝ) ^ (L + 1)) := by gcongr
    _ = _ := by rw [← Real.rpow_add hMpos, show epsilon / 2 + epsilon / 2 = epsilon by ring]

/-- Equation (3.26), uniformly also for every nonnegative real ceiling. -/
theorem proposition_three_twenty_seven_start_macroscopic
    (betaMin betaMax delta epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log M →
      ∀ T : ℝ, 0 ≤ T →
      cappedStartMass (M + L) L T (separatedPairs (macroscopicStarts M delta) L) ≤
        (M : ℝ) ^ epsilon * cappedProfile M ((2 : ℝ) ^ (L + 1)) T := by
  have heps : 0 < epsilon / 2 := by positivity
  obtain ⟨Mnonterminal, hnonterminal⟩ := cappedStartMass_le_profile_add_terminal_eventually
    betaMin betaMax delta (epsilon / 2) hbetaMin hbeta hdelta heps
  obtain ⟨Mterminal, hterminal⟩ := capped_sector_eight_le_profile_eventually
    betaMin betaMax delta (epsilon / 2) hbetaMin hbeta hdelta heps
  obtain ⟨Mconstant, hconstant⟩ := polynomial_factor_le_rpow_eventually
    betaMax (hbetaMin.trans hbeta).le 2 0 (epsilon / 2) heps
  refine ⟨max Mnonterminal (max Mterminal (max Mconstant 1)), ?_⟩
  intro M hM L hlower hupper T hT
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hn := hnonterminal M (by omega) L hlower hupper T hT
  have ht := hterminal M (by omega) L hlower hupper 3 (by omega) T hT
  have h2 : (2 : ℝ) ≤ (M : ℝ) ^ (epsilon / 2) := by
    simpa using hconstant M (by omega) L (by simpa using hupper)
  have hfirst : (0 : ℝ) ≤ (M : ℝ) ^ (3 / (2 : ℝ)) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (6 : ℝ)) := by positivity
  have hsum : cappedStartMass (M + L) L T (separatedPairs (macroscopicStarts M delta) L) ≤
      2 * (M : ℝ) ^ (epsilon / 2) * cappedProfile M ((2 : ℝ) ^ (L + 1)) T := by
    unfold cappedProfile at *
    nlinarith [mul_nonneg (Real.rpow_nonneg hMpos.le (epsilon / 2)) hfirst]
  have hP := cappedProfile_nonneg hMpos.le (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (L + 1)) hT
  calc
    _ ≤ _ := hsum
    _ ≤ ((M : ℝ) ^ (epsilon / 2) * (M : ℝ) ^ (epsilon / 2)) * cappedProfile M ((2 : ℝ) ^ (L + 1)) T := by gcongr
    _ = _ := by rw [← Real.rpow_add hMpos, show epsilon / 2 + epsilon / 2 = epsilon by ring]

/-- The first inequality of (3.25) for the full-value macroscopic relation mass. -/
theorem proposition_three_twenty_six_raw_macroscopic
    (betaMin betaMax delta epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log M →
      (macroscopicValueMassNat M L delta : ℝ) ≤
        (M : ℝ) ^ epsilon * rawProfile M ((2 : ℝ) ^ (L + 1)) := by
  have heps : 0 < epsilon / 2 := by positivity
  obtain ⟨Mstart, hstart⟩ := theorem_three_one_raw_macroscopic
    betaMin betaMax delta (epsilon / 2) hbetaMin hbeta hdelta heps
  obtain ⟨Mhost, hhost⟩ := proposition_three_seven_real betaMax (hbetaMin.trans hbeta).le (epsilon / 2) heps
  obtain ⟨Mconstant, hconstant⟩ := polynomial_factor_le_rpow_eventually
    betaMax (hbetaMin.trans hbeta).le 7 0 (epsilon / 2) heps
  refine ⟨max Mstart (max Mhost (max Mconstant 2)), ?_⟩
  intro M hM L hlower hupper
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hs := hstart M (by omega) L hlower hupper
  have hh := (hhost M (by omega) L (by simpa using hupper) delta hdelta).2
  have h7 : (7 : ℝ) ≤ (M : ℝ) ^ (epsilon / 2) := by
    simpa using hconstant M (by omega) L (by simpa using hupper)
  have hfinite : (macroscopicValueMassNat M L delta : ℝ) ≤
      4 * (macroscopicStartMassNat M L delta : ℝ) +
        3 * ((squareProductHosts L (separatedPairs (macroscopicStarts M delta) L)).card : ℝ) := by
    exact_mod_cast macroscopicValueMassNat_le_four_start_add_hosts (L := L) (by omega : 2 ≤ M) hdelta
  have hdom : (M : ℝ) ^ (3 / (2 : ℝ)) ≤ rawProfile M ((2 : ℝ) ^ (L + 1)) := by
    have hshallow := host_monomial_le_shallow (by positivity : (0 : ℝ) ≤ M)
      (show (1 : ℝ) ≤ (2 : ℝ) ^ (L + 1) from one_le_pow₀ (by norm_num))
    unfold rawProfile
    have ha : (0 : ℝ) ≤ M * ((2 : ℝ) ^ (L + 1)) ^ (2 / (3 : ℝ)) := by positivity
    have hb : (0 : ℝ) ≤ (M : ℝ) ^ (2 / (3 : ℝ)) * (2 : ℝ) ^ (L + 1) := by positivity
    linarith
  have hhp := hh.trans (mul_le_mul_of_nonneg_left hdom (by positivity : 0 ≤ (M : ℝ) ^ (epsilon / 2)))
  have hsum : (macroscopicValueMassNat M L delta : ℝ) ≤
      7 * (M : ℝ) ^ (epsilon / 2) * rawProfile M ((2 : ℝ) ^ (L + 1)) := by linarith
  have hP := rawProfile_nonneg hMpos.le (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (L + 1))
  calc
    _ ≤ _ := hsum
    _ ≤ ((M : ℝ) ^ (epsilon / 2) * (M : ℝ) ^ (epsilon / 2)) * rawProfile M ((2 : ℝ) ^ (L + 1)) := by gcongr
    _ = _ := by rw [← Real.rpow_add hMpos, show epsilon / 2 + epsilon / 2 = epsilon by ring]

/-- Equation (3.27) with the same real ceiling in the full-value and start sums. -/
theorem proposition_three_twenty_seven_value_macroscopic
    (betaMin betaMax delta epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log M →
      ∀ T : ℝ, 0 ≤ T →
      cappedValueMass (M + L) L T (separatedPairs (macroscopicStarts M delta) L) ≤
        (M : ℝ) ^ epsilon * cappedProfile M ((2 : ℝ) ^ (L + 1)) T := by
  have heps : 0 < epsilon / 2 := by positivity
  obtain ⟨Mstart, hstart⟩ := proposition_three_twenty_seven_start_macroscopic
    betaMin betaMax delta (epsilon / 2) hbetaMin hbeta hdelta heps
  obtain ⟨Mhost, hhost⟩ := proposition_three_seven_real betaMax (hbetaMin.trans hbeta).le (epsilon / 2) heps
  obtain ⟨Mconstant, hconstant⟩ := polynomial_factor_le_rpow_eventually
    betaMax (hbetaMin.trans hbeta).le 7 0 (epsilon / 2) heps
  refine ⟨max Mstart (max Mhost (max Mconstant 2)), ?_⟩
  intro M hM L hlower hupper T hT
  have hMtwo : 2 ≤ M := by omega
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hs := hstart M (by omega) L hlower hupper T hT
  have hh := (hhost M (by omega) L (by simpa using hupper) delta hdelta).2
  have h7 : (7 : ℝ) ≤ (M : ℝ) ^ (epsilon / 2) := by
    simpa using hconstant M (by omega) L (by simpa using hupper)
  have hmask := separatedPairs_macroscopicStarts_subset_Icc_product hMtwo hdelta L
  have hfinite := cappedValueMass_le_four_start_add_square_hosts (M + L) L hT
    (separatedPairs (macroscopicStarts M delta) L) (by
      intro xy hxy
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp (hmask hxy)
      exact ⟨(Finset.mem_Icc.mp hx).1, (Finset.mem_Icc.mp hy).1⟩) (by
      intro xy hxy
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp (hmask hxy)
      have hxM := (Finset.mem_Icc.mp hx).2
      have hyM := (Finset.mem_Icc.mp hy).2
      constructor <;> omega)
  have hdom : (M : ℝ) ^ (3 / (2 : ℝ)) ≤ cappedProfile M ((2 : ℝ) ^ (L + 1)) T := by
    have hshallow := host_monomial_le_shallow (by positivity : (0 : ℝ) ≤ M)
      (show (1 : ℝ) ≤ (2 : ℝ) ^ (L + 1) from one_le_pow₀ (by norm_num))
    unfold cappedProfile
    have ha : (0 : ℝ) ≤ M * ((2 : ℝ) ^ (L + 1)) ^ (2 / (3 : ℝ)) := by positivity
    have hb : (0 : ℝ) ≤ (M : ℝ) ^ (2 / (3 : ℝ)) * min T ((2 : ℝ) ^ (L + 1)) := by positivity
    linarith
  have hhp := hh.trans (mul_le_mul_of_nonneg_left hdom (by positivity : 0 ≤ (M : ℝ) ^ (epsilon / 2)))
  have hsum : cappedValueMass (M + L) L T (separatedPairs (macroscopicStarts M delta) L) ≤
      7 * (M : ℝ) ^ (epsilon / 2) * cappedProfile M ((2 : ℝ) ^ (L + 1)) T := by linarith
  have hP := cappedProfile_nonneg hMpos.le (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (L + 1)) hT
  calc
    _ ≤ _ := hsum
    _ ≤ ((M : ℝ) ^ (epsilon / 2) * (M : ℝ) ^ (epsilon / 2)) * cappedProfile M ((2 : ℝ) ^ (L + 1)) T := by gcongr
    _ = _ := by rw [← Real.rpow_add hMpos, show epsilon / 2 + epsilon / 2 = epsilon by ring]

/-- Equation (3.4), with its interpolation constant absorbed into the arbitrary error exponent. -/
theorem theorem_three_one_coarse_macroscopic
    (betaMin betaMax delta epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log M →
      (macroscopicStartMassNat M L delta : ℝ) ≤
        (M : ℝ) ^ epsilon * coarseProfile M ((2 : ℝ) ^ (L + 1)) := by
  have heps : 0 < epsilon / 2 := by positivity
  obtain ⟨Mraw, hraw⟩ := theorem_three_one_raw_macroscopic
    betaMin betaMax delta (epsilon / 2) hbetaMin hbeta hdelta heps
  obtain ⟨Mconstant, hconstant⟩ := polynomial_factor_le_rpow_eventually
    betaMax (hbetaMin.trans hbeta).le 2 0 (epsilon / 2) heps
  refine ⟨max Mraw (max Mconstant 1), ?_⟩
  intro M hM L hlower hupper
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hr := hraw M (by omega) L hlower hupper
  have h2 : (2 : ℝ) ≤ (M : ℝ) ^ (epsilon / 2) := by
    simpa using hconstant M (by omega) L (by simpa using hupper)
  have hcoarse := rawProfile_le_two_coarseProfile hMpos (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (L + 1))
  have hP := coarseProfile_nonneg hMpos.le (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (L + 1))
  calc
    _ ≤ _ := hr
    _ ≤ (M : ℝ) ^ (epsilon / 2) * (2 * coarseProfile M ((2 : ℝ) ^ (L + 1))) := by gcongr
    _ ≤ (M : ℝ) ^ (epsilon / 2) * ((M : ℝ) ^ (epsilon / 2) * coarseProfile M ((2 : ℝ) ^ (L + 1))) := by gcongr
    _ = _ := by rw [← mul_assoc, ← Real.rpow_add hMpos, show epsilon / 2 + epsilon / 2 = epsilon by ring]

/-- The second inequality of (3.25), for the actual full-value mass. -/
theorem proposition_three_twenty_six_coarse_macroscopic
    (betaMin betaMax delta epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log M →
      (macroscopicValueMassNat M L delta : ℝ) ≤
        (M : ℝ) ^ epsilon * coarseProfile M ((2 : ℝ) ^ (L + 1)) := by
  have heps : 0 < epsilon / 2 := by positivity
  obtain ⟨Mraw, hraw⟩ := proposition_three_twenty_six_raw_macroscopic
    betaMin betaMax delta (epsilon / 2) hbetaMin hbeta hdelta heps
  obtain ⟨Mconstant, hconstant⟩ := polynomial_factor_le_rpow_eventually
    betaMax (hbetaMin.trans hbeta).le 2 0 (epsilon / 2) heps
  refine ⟨max Mraw (max Mconstant 1), ?_⟩
  intro M hM L hlower hupper
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hr := hraw M (by omega) L hlower hupper
  have h2 : (2 : ℝ) ≤ (M : ℝ) ^ (epsilon / 2) := by
    simpa using hconstant M (by omega) L (by simpa using hupper)
  have hcoarse := rawProfile_le_two_coarseProfile hMpos (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (L + 1))
  have hP := coarseProfile_nonneg hMpos.le (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (L + 1))
  calc
    _ ≤ _ := hr
    _ ≤ (M : ℝ) ^ (epsilon / 2) * (2 * coarseProfile M ((2 : ℝ) ^ (L + 1))) := by gcongr
    _ ≤ (M : ℝ) ^ (epsilon / 2) * ((M : ℝ) ^ (epsilon / 2) * coarseProfile M ((2 : ℝ) ^ (L + 1))) := by gcongr
    _ = _ := by rw [← mul_assoc, ← Real.rpow_add hMpos, show epsilon / 2 + epsilon / 2 = epsilon by ring]

end
end PaperC.V282.WholeRelationProfile
