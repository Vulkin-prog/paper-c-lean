import PaperCV282.SizeTwoHostCounting
import PaperCV282.MacroscopicPointwiseDefects

/-!
# The exact rank and component-size bounds in residual sector 5

The strict lower density test supplies a component on at most eleven
occurrences. The upper density test gives the explicit `Q_B^(2/3)`
weight; the corrected-defect factor is subpolynomial on the macroscopic
domain. The arithmetic count of all size-eleven hosts is a separate step.
-/

namespace PaperC.V282.SectorFiveRank

open Affine PropositionSixteenOne ResidualComponentCounts
open ResidualSectorPartition ResidualSectorMass SizeTwoHostCounting
open BoundedRatioComponentHosts MacroscopicGeometry MacroscopicPointwiseDefects
open scoped BigOperators

noncomputable section

/-- The strict `c# > B/6` test yields a component on at most eleven occurrences. -/
theorem sector_five_mem_boundedHosts_eleven
    {N M A L : ℕ} (hN : 2 ≤ N) (pair : SeparatedBoundedRatioPair N M L)
    (hfive : sectorOf A hN pair = 4) :
    pair ∈ boundedComponentHosts N M A L 11 := by
  have hshallow := (sectorOf_eq_five_iff.mp hfive).2.2.1
  unfold shallowCore at hshallow
  apply mem_boundedHosts_of_strict_average hN pair
  omega

/-- The actual fifth-sector mask is contained in the bounded-component population. -/
theorem sector_five_subset_boundedHosts_eleven
    {N M A L : ℕ} (hN : 2 ≤ N) :
    sectorPairs N M A L hN 4 ⊆ boundedComponentHosts N M A L 11 := by
  intro pair hpair
  exact sector_five_mem_boundedHosts_eleven hN pair (mem_sectorPairs.mp hpair)

/-- The actual fifth-sector residual weight has its stated two-thirds word-space factor. -/
theorem residualWeight_cast_le_defect_mul_wordCount_two_thirds
    {N M A L : ℕ} (hN : 2 ≤ N) (pair : SeparatedBoundedRatioPair N M L)
    (hfive : sectorOf A hN pair = 4) :
    (residualWeight A hN pair : ℝ) ≤
      (2 : ℝ) ^ canonicalCorrectedDefectCount A pair.1.1 pair.1.2 L *
        ((2 : ℝ) ^ (L + 1)) ^ (2 / (3 : ℝ)) := by
  have hlate : 4 ≤ (sectorOf A hN pair).val := by rw [hfive]; decide
  have hsigma := sigma_eq_zero_of_sector_at_least_five hN pair hlate
  have hrank := residualTau_add_rank_eq_corrected_add_components hN pair
    (nonaligned_of_sector_at_least_five hN pair hlate)
  have hmoderate := (sectorOf_eq_five_iff.mp hfive).2.2.2.2
  unfold moderateCore at hmoderate
  have hcReal : (canonicalResidualComponentCount A pair.1.1 pair.1.2 L : ℝ) ≤
      (L + 1 : ℝ) * (2 / (3 : ℝ)) := by
    have hh : 3 * (canonicalResidualComponentCount A pair.1.1 pair.1.2 L : ℝ) ≤
        2 * (L + 1 : ℝ) := by exact_mod_cast hmoderate
    linarith
  have hcore : (2 : ℝ) ^ canonicalResidualComponentCount A pair.1.1 pair.1.2 L ≤
      ((2 : ℝ) ^ (L + 1)) ^ (2 / (3 : ℝ)) := by
    calc
      _ = (2 : ℝ) ^ (canonicalResidualComponentCount A pair.1.1 pair.1.2 L : ℝ) :=
        (Real.rpow_natCast _ _).symm
      _ ≤ (2 : ℝ) ^ ((L + 1 : ℝ) * (2 / (3 : ℝ))) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hcReal
      _ = _ := by
        rw [Real.rpow_mul (by norm_num)]
        rw [show (L + 1 : ℝ) = ((L + 1 : ℕ) : ℝ) by norm_cast, Real.rpow_natCast]
  have htau : pairTau A hN pair ≤ canonicalCorrectedDefectCount A pair.1.1 pair.1.2 L +
      canonicalResidualComponentCount A pair.1.1 pair.1.2 L := by omega
  have hw : residualWeight A hN pair ≤
      2 ^ (canonicalCorrectedDefectCount A pair.1.1 pair.1.2 L +
        canonicalResidualComponentCount A pair.1.1 pair.1.2 L) := by
    simp only [residualWeight, hsigma, pow_zero, one_mul]
    exact (Nat.sub_le _ _).trans (Nat.pow_le_pow_right (by omega) htau)
  have hcast : (residualWeight A hN pair : ℝ) ≤
      (2 : ℝ) ^ canonicalCorrectedDefectCount A pair.1.1 pair.1.2 L *
        (2 : ℝ) ^ canonicalResidualComponentCount A pair.1.1 pair.1.2 L := by
    rw [← pow_add]
    exact_mod_cast hw
  exact hcast.trans (mul_le_mul_of_nonneg_left hcore (by positivity))

/-- The corrected-defect factor is absorbed uniformly on all actual fifth-sector pairs. -/
theorem residualWeight_le_word_profile_eventually
    (betaMin betaMax delta epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M → ∀ A : ℕ, ∀ hN : 2 ≤ ⌈(M : ℝ) ^ delta⌉₊,
      ∀ pair ∈ sectorPairs ⌈(M : ℝ) ^ delta⌉₊ M A L hN 4,
      (residualWeight A hN pair : ℝ) ≤
        (M : ℝ) ^ epsilon * ((2 : ℝ) ^ (L + 1)) ^ (2 / (3 : ℝ)) := by
  obtain ⟨Mdefect, hdefect⟩ := two_pow_correctedDefect_le_rpow_eventually
    betaMin betaMax delta epsilon hbetaMin hbeta hdelta hepsilon
  refine ⟨Mdefect, ?_⟩
  intro M hM L hlower hupper A hN pair hpair
  have hgeo := mem_separatedBoundedRatioPairs.mp pair.property
  have hd := hdefect M hM L hlower hupper A pair.1.1 hgeo.1 pair.1.2 hgeo.2.1
  exact (residualWeight_cast_le_defect_mul_wordCount_two_thirds hN pair
    (mem_sectorPairs.mp hpair)).trans (mul_le_mul_of_nonneg_right hd (by positivity))

/-- The weighted sector is reduced to the explicit size-eleven host population. -/
theorem sector_five_mass_le_host_card_eventually
    (betaMin betaMax delta epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M → ∀ A : ℕ,
      sectorMass A 4 ⌈(M : ℝ) ^ delta⌉₊ M L ≤
        ((boundedComponentHosts ⌈(M : ℝ) ^ delta⌉₊ M A L 11).card : ℝ) *
          ((M : ℝ) ^ epsilon * ((2 : ℝ) ^ (L + 1)) ^ (2 / (3 : ℝ))) := by
  obtain ⟨Mweight, hweight⟩ := residualWeight_le_word_profile_eventually
    betaMin betaMax delta epsilon hbetaMin hbeta hdelta hepsilon
  refine ⟨max Mweight 2, ?_⟩
  intro M hM L hlower hupper A
  have hN := two_le_macroscopic_lowerEndpoint ((le_max_right _ _).trans hM) hdelta
  have hw := hweight M ((le_max_left _ _).trans hM) L hlower hupper A hN
  have hcard : ((sectorPairs ⌈(M : ℝ) ^ delta⌉₊ M A L hN 4).card : ℝ) ≤
      ((boundedComponentHosts ⌈(M : ℝ) ^ delta⌉₊ M A L 11).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (sector_five_subset_boundedHosts_eleven (A := A) hN)
  simp only [sectorMass, dif_pos hN, sectorMassNat, Nat.cast_sum]
  calc
    _ ≤ ∑ _pair ∈ sectorPairs ⌈(M : ℝ) ^ delta⌉₊ M A L hN 4,
        (M : ℝ) ^ epsilon * ((2 : ℝ) ^ (L + 1)) ^ (2 / (3 : ℝ)) := Finset.sum_le_sum hw
    _ = ((sectorPairs ⌈(M : ℝ) ^ delta⌉₊ M A L hN 4).card : ℝ) *
        ((M : ℝ) ^ epsilon * ((2 : ℝ) ^ (L + 1)) ^ (2 / (3 : ℝ))) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)

end
end PaperC.V282.SectorFiveRank
