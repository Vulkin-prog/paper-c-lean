import PaperCV282.SectorSixHostCover
import PaperCV282.MacroscopicTwoDefectStarts
import PaperCV282.MacroscopicPointwiseDefects

/-!
# The unconditional profile of residual sector 6

Two defects in one block give subpolynomially many first starts. A
size-two component leaves a square-root fibre for the other start. The
full residual weight is then bounded using the actual canonical rank
identity and the proved corrected-defect estimate.
-/

namespace PaperC.V282.SectorSixProfile

open Affine PropositionSixteenOne ResidualSectorPartition ResidualSectorMass
open ResidualComponentCounts SectorSixHostCover MacroscopicTwoDefectStarts
open MacroscopicGeometry MacroscopicPointwiseDefects LogarithmicWordPowers
open BoundedRatioManyDefectsFibers SquarefreeSmoothCount
open scoped BigOperators

noncomputable section

/-- The degree-one fibre factor is uniformly bounded by three square roots of the scale. -/
theorem sqrt_cutoff_add_one_le {M L : ℕ} (hM : 1 ≤ M) (hL : L ≤ M) :
    ((Nat.sqrt (M + L) + 1 : ℕ) : ℝ) ≤ 3 * Real.sqrt M := by
  have hroot : Real.sqrt (M + L : ℝ) ≤ 2 * Real.sqrt M := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · rw [mul_pow, Real.sq_sqrt (by positivity)]
      have hcast : (L : ℝ) ≤ M := by exact_mod_cast hL
      nlinarith
  have hone : (1 : ℝ) ≤ Real.sqrt M := Real.one_le_sqrt.mpr (by exact_mod_cast hM)
  have hnat : (Nat.sqrt (M + L) : ℝ) ≤ Real.sqrt (M + L : ℝ) := by
    simpa only [Nat.cast_add] using (Real.nat_sqrt_le_real_sqrt (a := M + L))
  push_cast
  linarith

/-- The complete sixth-sector host count is `M^(1/2+epsilon)`. -/
theorem card_sector_six_le_half_profile_eventually
    (betaMin betaMax delta epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbetaMax : 0 < betaMax) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M → ∀ A : ℕ, ∀ hN : 2 ≤ ⌈(M : ℝ) ^ delta⌉₊,
      ((sectorPairs ⌈(M : ℝ) ^ delta⌉₊ M A L hN 5).card : ℝ) ≤
        (M : ℝ) ^ epsilon * Real.sqrt M := by
  have heps : 0 < epsilon / 3 := by linarith
  obtain ⟨Mbase, hbase⟩ := card_twoDefectBaseCover_le_rpow_eventually
    betaMin betaMax delta (epsilon / 3) hbetaMin hbetaMax hdelta heps
  obtain ⟨Msmooth, hsmooth⟩ := MacroscopicSmoothKernels.card_squarefreeSmoothUpTo_le_rpow_eventually
    betaMin betaMax (epsilon / 3) hbetaMin hbetaMax heps
  obtain ⟨Mpoly, hpoly⟩ := polynomial_factor_le_rpow_eventually betaMax hbetaMax.le 54 4
    (epsilon / 3) heps
  obtain ⟨Mlength, hlength⟩ := MacroscopicCanonicalCode.logarithmic_power_lt_rpow_eventually
    betaMax 1 hbetaMax.le (by norm_num) 1 (by omega)
  refine ⟨max Mbase (max Msmooth (max Mpoly (max Mlength 2))), ?_⟩
  intro M hM L hlower hupper A hN
  have hrest1 : max Msmooth (max Mpoly (max Mlength 2)) ≤ M := (le_max_right _ _).trans hM
  have hrest2 : max Mpoly (max Mlength 2) ≤ M := (le_max_right _ _).trans hrest1
  have hrest3 : max Mlength 2 ≤ M := (le_max_right _ _).trans hrest2
  have hMtwo : 2 ≤ M := (le_max_right _ _).trans hrest3
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hl := hlength M ((le_max_left _ _).trans hrest3) (L + 1) (by simpa using hupper)
  have hL : L ≤ M := by
    simp only [pow_one, Real.rpow_one, Nat.cast_add, Nat.cast_one] at hl
    have : (L : ℝ) ≤ M := by linarith
    exact_mod_cast this
  have hb := hbase M ((le_max_left _ _).trans hM) L hlower hupper
  have hs := hsmooth M ((le_max_left _ _).trans hrest1) L hlower hupper ((M + L) ^ 2)
  have hp : 54 * (L + 1 : ℝ) ^ 4 ≤ (M : ℝ) ^ (epsilon / 3) := by
    have hh := hpoly M ((le_max_left _ _).trans hrest2) L (by simpa using hupper)
    simpa only [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 54 * (L + 1 : ℝ) ^ 4)] using hh
  have hr := sqrt_cutoff_add_one_le (by omega : 1 ≤ M) hL
  have hf : ((sectorPairs ⌈(M : ℝ) ^ delta⌉₊ M A L hN 5).card : ℝ) ≤
      2 * ((twoDefectBaseCover ⌈(M : ℝ) ^ delta⌉₊ M (L + 1)).card : ℝ) *
        (9 * (L + 1 : ℝ) ^ 4) * ((squarefreeSmoothUpTo (L + 1) ((M + L) ^ 2)).card : ℝ) *
          ((Nat.sqrt (M + L) + 1 : ℕ) : ℝ) := by
    have hh := card_sector_six_le (M := M) (A := A) (L := L) hN
    have hcast := (Nat.cast_le (α := ℝ)).mpr hh
    push_cast at hcast
    push_cast
    convert hcast using 1 <;> first | rfl | ring
  calc
    _ ≤ _ := hf
    _ ≤ 2 * ((twoDefectBaseCover ⌈(M : ℝ) ^ delta⌉₊ M (L + 1)).card : ℝ) *
        (9 * (L + 1 : ℝ) ^ 4) * ((squarefreeSmoothUpTo (L + 1) ((M + L) ^ 2)).card : ℝ) *
          (3 * Real.sqrt M) := mul_le_mul_of_nonneg_left hr (by positivity)
    _ = (((twoDefectBaseCover ⌈(M : ℝ) ^ delta⌉₊ M (L + 1)).card : ℝ) *
        (54 * (L + 1 : ℝ) ^ 4) * ((squarefreeSmoothUpTo (L + 1) ((M + L) ^ 2)).card : ℝ)) *
          Real.sqrt M := by ring
    _ ≤ (((M : ℝ) ^ (epsilon / 3) * (M : ℝ) ^ (epsilon / 3)) *
        (M : ℝ) ^ (epsilon / 3)) * Real.sqrt M := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul (mul_le_mul hb hp (by positivity) (by positivity)) hs
        (by positivity) (by positivity)
    _ = _ := by
      rw [← Real.rpow_add hMpos, ← Real.rpow_add hMpos]
      congr 2
      ring

/-- Pointwise residual weight of the actual sixth sector, before the defect factor is absorbed. -/
theorem residualWeight_cast_le_defect_mul_wordCount
    {N M A L : ℕ} (hN : 2 ≤ N) (pair : SeparatedBoundedRatioPair N M L)
    (hsix : sectorOf A hN pair = 5) :
    (residualWeight A hN pair : ℝ) ≤
      (2 : ℝ) ^ canonicalCorrectedDefectCount A pair.1.1 pair.1.2 L * (2 : ℝ) ^ (L + 1) := by
  have hlate : 4 ≤ (sectorOf A hN pair).val := by rw [hsix]; decide
  have hsigma := sigma_eq_zero_of_sector_at_least_five hN pair hlate
  have hrank := residualTau_add_rank_eq_corrected_add_components hN pair
    (nonaligned_of_sector_at_least_five hN pair hlate)
  have hslack := slack_add_componentCount (A := A) hN pair
  have htau : pairTau A hN pair ≤ canonicalCorrectedDefectCount A pair.1.1 pair.1.2 L + (L + 1) := by omega
  have hw : residualWeight A hN pair ≤
      2 ^ (canonicalCorrectedDefectCount A pair.1.1 pair.1.2 L + (L + 1)) := by
    simp only [residualWeight, hsigma, pow_zero, one_mul]
    exact (Nat.sub_le _ _).trans (Nat.pow_le_pow_right (by omega) htau)
  have hcast : (residualWeight A hN pair : ℝ) ≤
      (2 : ℝ) ^ (canonicalCorrectedDefectCount A pair.1.1 pair.1.2 L + (L + 1)) := by exact_mod_cast hw
  simpa only [pow_add] using hcast

/-- The complete weighted sixth-sector profile, with the true word count explicit. -/
theorem macroscopic_sector_six_le_profile_eventually
    (betaMin betaMax delta epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M → ∀ A : ℕ,
      sectorMass A 5 ⌈(M : ℝ) ^ delta⌉₊ M L ≤
        (M : ℝ) ^ epsilon * (Real.sqrt M * (2 : ℝ) ^ (L + 1)) := by
  have heps : 0 < epsilon / 2 := by linarith
  obtain ⟨Mhost, hhost⟩ := card_sector_six_le_half_profile_eventually
    betaMin betaMax delta (epsilon / 2) hbetaMin (hbetaMin.trans hbeta) hdelta heps
  obtain ⟨Mdefect, hdefect⟩ := two_pow_correctedDefect_le_rpow_eventually
    betaMin betaMax delta (epsilon / 2) hbetaMin hbeta hdelta heps
  refine ⟨max Mhost (max Mdefect 2), ?_⟩
  intro M hM L hlower hupper A
  have hrest : max Mdefect 2 ≤ M := (le_max_right _ _).trans hM
  have hMtwo : 2 ≤ M := (le_max_right _ _).trans hrest
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hN : 2 ≤ ⌈(M : ℝ) ^ delta⌉₊ := two_le_macroscopic_lowerEndpoint hMtwo hdelta
  have hc := hhost M ((le_max_left _ _).trans hM) L hlower hupper A hN
  have hw : ∀ pair ∈ sectorPairs ⌈(M : ℝ) ^ delta⌉₊ M A L hN 5,
      (residualWeight A hN pair : ℝ) ≤ (M : ℝ) ^ (epsilon / 2) * (2 : ℝ) ^ (L + 1) := by
    intro pair hpair
    have hgeo := mem_separatedBoundedRatioPairs.mp pair.property
    have hd := hdefect M ((le_max_left _ _).trans hrest) L hlower hupper A pair.1.1 hgeo.1
      pair.1.2 hgeo.2.1
    exact (residualWeight_cast_le_defect_mul_wordCount hN pair (mem_sectorPairs.mp hpair)).trans
      (mul_le_mul_of_nonneg_right hd (by positivity))
  have hmass : sectorMass A 5 ⌈(M : ℝ) ^ delta⌉₊ M L ≤
      ((sectorPairs ⌈(M : ℝ) ^ delta⌉₊ M A L hN 5).card : ℝ) *
        ((M : ℝ) ^ (epsilon / 2) * (2 : ℝ) ^ (L + 1)) := by
    simp only [sectorMass, dif_pos hN, sectorMassNat, Nat.cast_sum]
    calc
      _ ≤ ∑ _pair ∈ sectorPairs ⌈(M : ℝ) ^ delta⌉₊ M A L hN 5,
          (M : ℝ) ^ (epsilon / 2) * (2 : ℝ) ^ (L + 1) := Finset.sum_le_sum hw
      _ = _ := by simp
  calc
    _ ≤ _ := hmass
    _ ≤ ((M : ℝ) ^ (epsilon / 2) * Real.sqrt M) *
        ((M : ℝ) ^ (epsilon / 2) * (2 : ℝ) ^ (L + 1)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = ((M : ℝ) ^ (epsilon / 2) * (M : ℝ) ^ (epsilon / 2)) *
        (Real.sqrt M * (2 : ℝ) ^ (L + 1)) := by ring
    _ = _ := by rw [← Real.rpow_add hMpos, show epsilon / 2 + epsilon / 2 = epsilon by ring]

end
end PaperC.V282.SectorSixProfile
