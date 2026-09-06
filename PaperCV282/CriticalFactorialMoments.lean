import PaperCV282.DyadicRelationProfile
import PaperCV282.TouchingPairMass
import PaperCV282.CriticalFirstMomentRate

/-!
# Quantitative second factorial moments from the proved arithmetic profile

The numerator counts the three actual off-diagonal populations. Overlap
exclusion, the touching bound and the complete separated profile give an
explicit one-third saving at critical lengths. No Poisson approximation
or external asymptotic relation-mass hypothesis is used.
-/

namespace PaperC.V282.CriticalFactorialMoments

open SectionTwelveMoments DyadicRelationProfile TouchingPairMass ProfileMonomials
open LogarithmicWordPowers CriticalProfileNormalization

noncomputable section

/-- All three actual factorial-error populations satisfy the complete coarse profile. -/
theorem factorialErrorNumerator_le_profile_eventually
    (betaMin betaMax epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      factorialErrorNumerator N L ≤
        (N : ℝ) ^ epsilon * coarseProfile N ((2 : ℝ) ^ (L + 1)) := by
  have heps : 0 < epsilon / 2 := by positivity
  have hbetaMax : 0 ≤ betaMax := (hbetaMin.trans hbeta).le
  obtain ⟨Nsep, hsep⟩ := jointDefectMass_separated_le_coarse_eventually
    betaMin betaMax (epsilon / 2) hbetaMin hbeta heps
  obtain ⟨Ntouch, htouch⟩ := historical_touchingMass_le_eventually
    betaMin betaMax (epsilon / 2) hbetaMin hbeta heps
  obtain ⟨Nlength, hlength⟩ := polynomial_factor_le_rpow_eventually betaMax hbetaMax 2 1 (epsilon / 2) heps
  obtain ⟨Nconstant, hconstant⟩ := polynomial_factor_le_rpow_eventually betaMax hbetaMax 3 0 (epsilon / 2) heps
  refine ⟨max Nsep (max Ntouch (max Nlength (max Nconstant 1))), ?_⟩
  intro N hN L hlo hhi
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let P := coarseProfile N ((2 : ℝ) ^ (L + 1))
  have hP : 0 ≤ P := coarseProfile_nonneg hNpos.le (by positivity)
  have hNP : (N : ℝ) ≤ P := by
    have hh : (N : ℝ) ≤ (N : ℝ) ^ (5 / (3 : ℝ)) := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hNone (by norm_num : (1 : ℝ) ≤ 5 / 3)
    exact hh.trans (le_add_of_nonneg_right (by positivity))
  have hlen : 2 * (L + 1 : ℝ) ≤ (N : ℝ) ^ (epsilon / 2) := by
    simpa only [pow_one, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (L + 1 : ℝ))]
      using hlength N (by omega) L (by simpa using hhi)
  have hoverlap : ((overlappingPairs N L).card : ℝ) ≤ (N : ℝ) ^ (epsilon / 2) * P := by
    have hn : ((overlappingPairs N L).card : ℝ) ≤ 2 * (N : ℝ) * L := by
      exact_mod_cast card_overlappingPairs_le_two_mul N L
    calc
      _ ≤ _ := hn
      _ ≤ (N : ℝ) * (2 * (L + 1 : ℝ)) := by nlinarith
      _ ≤ (N : ℝ) * (N : ℝ) ^ (epsilon / 2) := by gcongr
      _ ≤ P * (N : ℝ) ^ (epsilon / 2) := by gcongr
      _ = _ := by ring
  have ht : (TouchingMass.touchingMass N L : ℝ) ≤ (N : ℝ) ^ (epsilon / 2) * P := by
    calc
      _ ≤ (N : ℝ) ^ (1 + epsilon / 2) := htouch N (by omega) L hlo hhi
      _ = (N : ℝ) ^ (epsilon / 2) * N := by rw [Real.rpow_add hNpos, Real.rpow_one]; ring
      _ ≤ _ := by gcongr
  have hs := hsep N (by omega) L hlo hhi
  have hthree : (3 : ℝ) ≤ (N : ℝ) ^ (epsilon / 2) := by
    simpa using hconstant N (by omega) L (by simpa using hhi)
  have htotal : factorialErrorNumerator N L ≤ 3 * (N : ℝ) ^ (epsilon / 2) * P := by
    unfold factorialErrorNumerator
    linarith
  calc
    _ ≤ _ := htotal
    _ ≤ ((N : ℝ) ^ (epsilon / 2) * (N : ℝ) ^ (epsilon / 2)) * P := by gcongr
    _ = _ := by rw [← Real.rpow_add hNpos, show epsilon / 2 + epsilon / 2 = epsilon by ring]

/-- The exact independent baseline error has the stated quantitative critical rate. -/
theorem critical_factorialMomentError_le_eventually (C epsilon : ℝ)
    (hC : 0 ≤ C) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      CriticalRunWindow.InRunLengthWindow C N L →
      |factorialMomentError N L| ≤ (N : ℝ) ^ (-(1 / (3 : ℝ)) + epsilon) := by
  have heps : 0 < epsilon / 2 := by positivity
  let K := CriticalRunWindow.balanceConstant C
  obtain ⟨Nwindow, hwindow⟩ := CriticalRunWindow.firstMomentWindow_eventually hC
  obtain ⟨Nnumerator, hnumerator⟩ := factorialErrorNumerator_le_profile_eventually
    CriticalRunWindow.lowerConstant CriticalRunWindow.upperConstant (epsilon / 2)
    CriticalRunWindow.lowerConstant_pos CriticalRunWindow.lowerConstant_lt_upperConstant heps
  obtain ⟨Nconstant, hconstant⟩ := constant_le_rpow_in_criticalWindow_eventually
    C (K ^ 2 + 2 * K) (epsilon / 2) hC heps
  refine ⟨max Nwindow (max Nnumerator (max Nconstant 2)), ?_⟩
  intro N hN L hrun
  have hw := hwindow N (by omega) L hrun
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hnum := hnumerator N (by omega) L (by simpa using hw.1.2.2.1) (by simpa using hw.1.2.2.2)
  have hnormalized := coarseProfile_div_runSquare_le (by omega : 0 < N) hw.2.2
  have hc := hconstant N (by omega) L hrun
  calc
    _ ≤ factorialErrorNumerator N L / (2 : ℝ) ^ (2 * L) :=
      abs_factorialMomentError_le (by omega) hw.2.1
    _ ≤ ((N : ℝ) ^ (epsilon / 2) * coarseProfile N ((2 : ℝ) ^ (L + 1))) /
        (2 : ℝ) ^ (2 * L) := by gcongr
    _ = (N : ℝ) ^ (epsilon / 2) *
        (coarseProfile N ((2 : ℝ) ^ (L + 1)) / (2 : ℝ) ^ (2 * L)) := by ring
    _ ≤ (N : ℝ) ^ (epsilon / 2) * ((K ^ 2 + 2 * K) * (N : ℝ) ^ (-(1 / (3 : ℝ)))) := by gcongr
    _ ≤ (N : ℝ) ^ (epsilon / 2) * ((N : ℝ) ^ (epsilon / 2) * (N : ℝ) ^ (-(1 / (3 : ℝ)))) := by gcongr
    _ = _ := by rw [← mul_assoc, ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]; congr 1; ring

/-- Replacing the falling-factorial baseline by the square of the actual target mean. -/
theorem critical_second_factorial_moment_le_eventually (C epsilon : ℝ)
    (hC : 0 ≤ C) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      CriticalRunWindow.InRunLengthWindow C N L →
      |(dyadicSecondFactorialMoment N L : ℝ) - criticalMean N L ^ 2| ≤
        (N : ℝ) ^ (-(1 / (3 : ℝ)) + epsilon) := by
  have heps : 0 < epsilon / 2 := by positivity
  let K := CriticalRunWindow.balanceConstant C
  obtain ⟨Nerror, herror⟩ := critical_factorialMomentError_le_eventually C (epsilon / 2) hC heps
  obtain ⟨Nwindow, hwindow⟩ := CriticalRunWindow.firstMomentWindow_eventually hC
  obtain ⟨Nconstant, hconstant⟩ := constant_le_rpow_in_criticalWindow_eventually
    C (1 + K ^ 2) (epsilon / 2) hC heps
  refine ⟨max Nerror (max Nwindow (max Nconstant 2)), ?_⟩
  intro N hN L hrun
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hw := hwindow N (by omega) L hrun
  have hbalance : criticalMean N L ≤ K := hw.2.2
  have hmeanNonneg : 0 ≤ criticalMean N L := by unfold criticalMean; positivity
  have hbaseline : |factorialBaselinePoissonError N L| ≤
      K ^ 2 * (N : ℝ) ^ (-(1 / (3 : ℝ)) + epsilon / 2) := by
    rw [factorialBaselinePoissonError_eq (by omega)]
    rw [abs_div, abs_neg, abs_of_pos hNpos, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ (2 * L))]
    have hid : (N : ℝ) / (2 : ℝ) ^ (2 * L) = criticalMean N L ^ 2 / N := by
      unfold criticalMean
      rw [show 2 * L = L * 2 by omega, pow_mul]
      field_simp
    rw [hid]
    calc
      _ ≤ K ^ 2 / N := div_le_div_of_nonneg_right (pow_le_pow_left₀ hmeanNonneg hbalance 2) hNpos.le
      _ = K ^ 2 * (N : ℝ) ^ (-(1 : ℝ)) := by rw [Real.rpow_neg_one]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hNone (by linarith)) (sq_nonneg K)
  have htriangle : |(dyadicSecondFactorialMoment N L : ℝ) - criticalMean N L ^ 2| ≤
      |factorialMomentError N L| + |factorialBaselinePoissonError N L| := by
    convert abs_add_le (factorialMomentError N L) (factorialBaselinePoissonError N L) using 1
    congr 1
    unfold factorialMomentError factorialBaselinePoissonError
    ring
  have he := herror N (by omega) L hrun
  have hc := hconstant N (by omega) L hrun
  calc
    _ ≤ _ := htriangle
    _ ≤ (1 + K ^ 2) * (N : ℝ) ^ (-(1 / (3 : ℝ)) + epsilon / 2) := by nlinarith
    _ ≤ (N : ℝ) ^ (epsilon / 2) * (N : ℝ) ^ (-(1 / (3 : ℝ)) + epsilon / 2) := by gcongr
    _ = _ := by rw [← Real.rpow_add hNpos]; congr 1; ring

end
end PaperC.V282.CriticalFactorialMoments
