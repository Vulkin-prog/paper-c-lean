import PaperCV282.DyadicRelationProfile
import PaperCV282.FullBandArithmetic
import PaperCV282.DirectionalMarkedCosts

/-! # The full-value dyadic profile at the actual enlarged signed window -/
namespace PaperC.V282.DyadicFullValueProfile

open Affine SectionTwelveMoments WholeRelationProfile MacroscopicGeometry MacroscopicRelationProfile
open TwoWindowParity ProfileMonomials LogarithmicWordPowers DyadicRelationProfile
open RelationProfileRestriction FullBandArithmetic DirectionalMarkedCosts AllStartSoftPoisson

noncomputable section

theorem valueWeightMass_le_macroscopicValueMass {N L : ℕ} (hN : 2 ≤ N)
    {s : Finset (ℕ × ℕ)} (hs : s ⊆ separatedOffDiagPairs N L) :
    valueWeightMass (dyadicCutoff N L) L s ≤ macroscopicValueMassNat (2 * N) L (1 / (2 : ℝ)) := by
  have hsub : s ⊆ separatedPairs (macroscopicStarts (2 * N) (1 / (2 : ℝ))) L := by
    intro p hp
    obtain ⟨hx, hy, _, hd⟩ := mem_separatedOffDiagPairs.mp (hs hp)
    exact (mem_separatedPairs _ _ _ _).mpr
      ⟨dyadicBlock_subset_macroscopic hN hx, dyadicBlock_subset_macroscopic hN hy, hd⟩
  unfold valueWeightMass dyadicCutoff macroscopicValueMassNat
  exact Finset.sum_le_sum_of_subset hsub

theorem valueWeightMass_mask_le_coarse_eventually
    (betaMin betaMax epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ s : Finset (ℕ × ℕ), s ⊆ separatedOffDiagPairs N L →
      (valueWeightMass (dyadicCutoff N L) L s : ℝ) ≤ (N : ℝ) ^ epsilon * coarseProfile N ((2 : ℝ) ^ (L + 1)) := by
  have heps : 0 < epsilon / 2 := by positivity
  obtain ⟨Nmacro, hmacro⟩ := proposition_three_twenty_six_coarse_macroscopic
    (betaMin / 2) betaMax (1 / (2 : ℝ)) (epsilon / 2) (by positivity) (by linarith) (by norm_num) heps
  obtain ⟨Nconstant, hconstant⟩ := polynomial_factor_le_rpow_eventually
    betaMax (hbetaMin.trans hbeta).le (4 * (2 : ℝ) ^ (epsilon / 2)) 0 (epsilon / 2) heps
  refine ⟨max Nmacro (max Nconstant 2), ?_⟩
  intro N hN L hlower hupper s hs
  have hNtwo : 2 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨hl, hu⟩ := logarithmic_band_at_twice hNtwo hbetaMin.le (hbetaMin.trans hbeta).le hlower hupper
  have hm := hmacro (2 * N) (by omega) L hl hu
  have hf : (valueWeightMass (dyadicCutoff N L) L s : ℝ) ≤ (macroscopicValueMassNat (2 * N) L (1 / (2 : ℝ)) : ℝ) := by
    exact_mod_cast valueWeightMass_le_macroscopicValueMass hNtwo hs
  have hc : 4 * (2 : ℝ) ^ (epsilon / 2) ≤ (N : ℝ) ^ (epsilon / 2) := by
    simpa only [pow_zero, mul_one, abs_of_nonneg (by positivity : 0 ≤ 4 * (2 : ℝ) ^ (epsilon / 2))]
      using hconstant N (by omega) L (by simpa using hupper)
  have hscale : ((2 * N : ℕ) : ℝ) ^ (epsilon / 2) =
      (2 : ℝ) ^ (epsilon / 2) * (N : ℝ) ^ (epsilon / 2) := by
    push_cast
    exact Real.mul_rpow (by norm_num) hNpos.le
  have hcoarse : coarseProfile (2 * N : ℕ) ((2 : ℝ) ^ (L + 1)) ≤
      4 * coarseProfile N ((2 : ℝ) ^ (L + 1)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using coarseProfile_twice_le_four hNpos.le
      (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (L + 1))
  have hP := coarseProfile_nonneg hNpos.le (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (L + 1))
  calc
    _ ≤ _ := hf.trans hm
    _ ≤ ((2 * N : ℕ) : ℝ) ^ (epsilon / 2) * (4 * coarseProfile N ((2 : ℝ) ^ (L + 1))) := by gcongr
    _ = (4 * (2 : ℝ) ^ (epsilon / 2)) * (N : ℝ) ^ (epsilon / 2) * coarseProfile N ((2 : ℝ) ^ (L + 1)) := by rw [hscale]; ring
    _ ≤ ((N : ℝ) ^ (epsilon / 2) * (N : ℝ) ^ (epsilon / 2)) * coarseProfile N ((2 : ℝ) ^ (L + 1)) := by gcongr
    _ = _ := by rw [← Real.rpow_add hNpos, show epsilon / 2 + epsilon / 2 = epsilon by ring]

/-- The normalized whole-band estimate for every actual separated submask. -/
theorem normalized_valueWeightMass_le_eventually
    (betaMin betaMax epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ Q : ℕ,
      betaMin * Real.log N ≤ (Q + 1 : ℝ) → (Q + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ mask : Finset ℕ, mask ⊆ dyadicBlock N →
      (valueWeightMass (dyadicCutoff N Q) Q (separatedPairs mask Q) : ℝ)/(2 : ℝ)^(2*Q) ≤
        (N : ℝ)^(-(1/(3 : ℝ))+epsilon)*((fullRate N Q : ℝ)^2+2*(fullRate N Q : ℝ)) := by
  obtain ⟨Nzero,hzero⟩ := valueWeightMass_mask_le_coarse_eventually
    betaMin betaMax epsilon hbetaMin hbeta hepsilon
  refine ⟨max Nzero 1, ?_⟩
  intro N hN Q hlo hhi mask hmask
  have hs : separatedPairs mask Q ⊆ separatedOffDiagPairs N Q := by
    rw [← separatedPairs_block_eq]
    intro xy hxy
    obtain ⟨hx,hy,hd⟩ := (mem_separatedPairs _ _ _ _).mp hxy
    exact (mem_separatedPairs _ _ _ _).mpr ⟨hmask hx,hmask hy,hd⟩
  have h := hzero N (by omega) Q hlo hhi _ hs
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ ((N : ℝ)^epsilon*coarseProfile N ((2 : ℝ)^(Q+1)))/(2 : ℝ)^(2*Q) :=
      div_le_div_of_nonneg_right h (by positivity)
    _ = (N : ℝ)^epsilon*(coarseProfile N ((2 : ℝ)^(Q+1))/(2 : ℝ)^(2*Q)) := by ring
    _ = _ := by
      rw [coarseProfile_div_runSquare_eq (by omega), ← mul_assoc, ← Real.rpow_add hn]
      congr 2
      ring

/-- Longer thresholds have no greater whole-block target intensity. -/
theorem fullRate_mono_length (N : ℕ) {L Q : ℕ} (hLQ : L ≤ Q) :
    (fullRate N Q : ℝ) ≤ (fullRate N L : ℝ) := by
  simp only [fullRate_coe]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (pow_le_pow_right₀ (by norm_num) hLQ)

/-- The enlarged signed profile retains its exact exponential length cost. -/
theorem enlarged_valueWeightMass_le_eventually
    (betaMin betaMax epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L E : ℕ,
      betaMin * Real.log N ≤ (L+E+2 : ℝ) → (L+E+2 : ℝ) ≤ betaMax * Real.log N →
      ∀ mask : Finset ℕ, mask ⊆ dyadicBlock N →
      (1/(2 : ℝ)^L)^2 *
        (valueWeightMass (dyadicCutoff N (L+E+1)) (L+E+1) (separatedPairs mask (L+E+1)) : ℝ) ≤
      (2 : ℝ)^(2*E+2)*(N : ℝ)^(-(1/(3 : ℝ))+epsilon)*
        ((fullRate N L : ℝ)^2+2*(fullRate N L : ℝ)) := by
  obtain ⟨Nzero,hzero⟩ := normalized_valueWeightMass_le_eventually
    betaMin betaMax epsilon hbetaMin hbeta hepsilon
  refine ⟨Nzero, ?_⟩
  intro N hN L E hlo hhi mask hmask
  have h := hzero N hN (L+E+1) (by push_cast; linarith) (by push_cast; linarith) mask hmask
  have hmono := fullRate_mono_length N (show L ≤ L+E+1 by omega)
  have hpoly : (fullRate N (L+E+1) : ℝ)^2+2*(fullRate N (L+E+1) : ℝ) ≤
      (fullRate N L : ℝ)^2+2*(fullRate N L : ℝ) := by
    have ha := (fullRate N (L+E+1)).coe_nonneg
    have hb := (fullRate N L).coe_nonneg
    nlinarith
  have hm := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (2 : ℝ)^(2*E+2))
  have heq : (1/(2 : ℝ)^L)^2 = (2 : ℝ)^(2*E+2)/(2 : ℝ)^(2*(L+E+1)) := by
    rw [show 2*(L+E+1)=2*L+(2*E+2) by omega, pow_add]
    rw [show 2*L=L*2 by omega, pow_mul]
    field_simp
    simp only [pow_add, pow_mul]
    ring
  rw [heq]
  calc
    _ = (2 : ℝ)^(2*E+2)*
        ((valueWeightMass (dyadicCutoff N (L+E+1)) (L+E+1) (separatedPairs mask (L+E+1)) : ℝ)/
          (2 : ℝ)^(2*(L+E+1))) := by ring
    _ ≤ (2 : ℝ)^(2*E+2)*((N : ℝ)^(-(1/(3 : ℝ))+epsilon)*
        ((fullRate N (L+E+1) : ℝ)^2+2*(fullRate N (L+E+1) : ℝ))) := hm
    _ = ((2 : ℝ)^(2*E+2)*(N : ℝ)^(-(1/(3 : ℝ))+epsilon))*
        ((fullRate N (L+E+1) : ℝ)^2+2*(fullRate N (L+E+1) : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpoly (by positivity)

end
end PaperC.V282.DyadicFullValueProfile
