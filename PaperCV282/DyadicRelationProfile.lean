import PaperCV282.WholeRelationProfile
import PaperC.Probability.SectionTwelveMoments

/-!
# The proved relation profile at the genuine dyadic scale

The block [N,2N) lies in the macroscopic domain at scale 2N and exponent
one half. Its historical cylinder is exactly 2N+L, so this restriction
retains the same two-start matrices. Constants from the factor two in
the scale are absorbed before the length and the chosen mask.
-/

namespace PaperC.V282.DyadicRelationProfile

open Affine SectionTwelveMoments WholeRelationProfile MacroscopicGeometry
open MacroscopicRelationProfile TwoWindowParity ProfileMonomials LogarithmicWordPowers

noncomputable section

/-- The dyadic block is inside the exact square-root macroscopic domain. -/
theorem dyadicBlock_subset_macroscopic {N : ℕ} (hN : 2 ≤ N) :
    dyadicBlock N ⊆ macroscopicStarts (2 * N) (1 / (2 : ℝ)) := by
  intro x hx
  have hxrange := Finset.mem_Ico.mp hx
  apply (mem_macroscopicStarts_iff_real _ _ _).mpr
  refine ⟨?_, hxrange.2⟩
  have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : Real.sqrt ((2 * N : ℕ) : ℝ) ≤ (N : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    push_cast
    nlinarith
  rw [← Real.sqrt_eq_rpow]
  exact hs.trans (by exact_mod_cast hxrange.1)

/-- Restriction keeps the exact historical dyadic defect sum and cylinder. -/
theorem jointDefectMass_le_macroscopicStartMass {N L : ℕ} (hN : 2 ≤ N)
    {s : Finset (ℕ × ℕ)} (hs : s ⊆ separatedOffDiagPairs N L) :
    jointDefectMass N L s ≤ macroscopicStartMassNat (2 * N) L (1 / (2 : ℝ)) := by
  have hsub : s ⊆ separatedPairs (macroscopicStarts (2 * N) (1 / (2 : ℝ))) L := by
    intro p hp
    obtain ⟨hx, hy, _, hd⟩ := mem_separatedOffDiagPairs.mp (hs hp)
    exact (mem_separatedPairs _ _ _ _).mpr
      ⟨dyadicBlock_subset_macroscopic hN hx, dyadicBlock_subset_macroscopic hN hy, hd⟩
  unfold jointDefectMass jointDefectWeight jointRho dyadicCutoff macroscopicStartMassNat
  exact Finset.sum_le_sum_of_subset hsub

/-- A fixed band at N transports to a fixed band at 2N. -/
theorem logarithmic_band_at_twice {N L : ℕ} {betaMin betaMax : ℝ}
    (hN : 2 ≤ N) (hbetaMin : 0 ≤ betaMin) (hbetaMax : 0 ≤ betaMax)
    (hlower : betaMin * Real.log N ≤ (L + 1 : ℝ))
    (hupper : (L + 1 : ℝ) ≤ betaMax * Real.log N) :
    (betaMin / 2) * Real.log (2 * N : ℕ) ≤ (L + 1 : ℝ) ∧
      (L + 1 : ℝ) ≤ betaMax * Real.log (2 * N : ℕ) := by
  have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hloglow : Real.log N ≤ Real.log (2 * N : ℕ) :=
    Real.log_le_log (by positivity) (by push_cast; linarith)
  have hloghigh : Real.log (2 * N : ℕ) ≤ 2 * Real.log N := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < (2 * N : ℕ))
      (show ((2 * N : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 by push_cast; nlinarith)
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  constructor
  · exact (mul_le_mul_of_nonneg_left hloghigh (by positivity : 0 ≤ betaMin / 2)).trans
      (by nlinarith : (betaMin / 2) * (2 * Real.log N) ≤ L + 1)
  · exact hupper.trans (mul_le_mul_of_nonneg_left hloglow hbetaMax)

/-- Explicit scale-two comparison of the two interpolation monomials. -/
theorem coarseProfile_twice_le_four {N Q : ℝ} (hN : 0 ≤ N) (hQ : 0 ≤ Q) :
    coarseProfile (2 * N) Q ≤ 4 * coarseProfile N Q := by
  have hp (a : ℝ) (ha : a ≤ 2) : (2 * N) ^ a ≤ 4 * N ^ a := by
    rw [Real.mul_rpow (by norm_num) hN]
    have hh : (2 : ℝ) ^ a ≤ 4 := by
      exact (Real.rpow_le_rpow_of_exponent_le (by norm_num) ha).trans_eq (by norm_num)
    exact mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hN _)
  have ha := hp (5 / (3 : ℝ)) (by norm_num)
  have hb := mul_le_mul_of_nonneg_right (hp (2 / (3 : ℝ)) (by norm_num)) hQ
  unfold coarseProfile
  nlinarith

/-- The actual dyadic separated defect mass, uniformly before every finite submask. -/
theorem jointDefectMass_mask_le_coarse_eventually
    (betaMin betaMax epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ s : Finset (ℕ × ℕ), s ⊆ separatedOffDiagPairs N L →
      (jointDefectMass N L s : ℝ) ≤ (N : ℝ) ^ epsilon * coarseProfile N ((2 : ℝ) ^ (L + 1)) := by
  have heps : 0 < epsilon / 2 := by positivity
  obtain ⟨Nmacro, hmacro⟩ := theorem_three_one_coarse_macroscopic
    (betaMin / 2) betaMax (1 / (2 : ℝ)) (epsilon / 2) (by positivity) (by linarith) (by norm_num) heps
  obtain ⟨Nconstant, hconstant⟩ := polynomial_factor_le_rpow_eventually
    betaMax (hbetaMin.trans hbeta).le (4 * (2 : ℝ) ^ (epsilon / 2)) 0 (epsilon / 2) heps
  refine ⟨max Nmacro (max Nconstant 2), ?_⟩
  intro N hN L hlower hupper s hs
  have hNtwo : 2 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨hl, hu⟩ := logarithmic_band_at_twice hNtwo hbetaMin.le (hbetaMin.trans hbeta).le hlower hupper
  have hm := hmacro (2 * N) (by omega) L hl hu
  have hf : (jointDefectMass N L s : ℝ) ≤ (macroscopicStartMassNat (2 * N) L (1 / (2 : ℝ)) : ℝ) := by
    exact_mod_cast jointDefectMass_le_macroscopicStartMass hNtwo hs
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

/-- The full separated dyadic population needed by the second-moment theorem. -/
theorem jointDefectMass_separated_le_coarse_eventually
    (betaMin betaMax epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      (jointDefectMass N L (separatedOffDiagPairs N L) : ℝ) ≤
        (N : ℝ) ^ epsilon * coarseProfile N ((2 : ℝ) ^ (L + 1)) := by
  obtain ⟨Nzero, hcount⟩ := jointDefectMass_mask_le_coarse_eventually betaMin betaMax epsilon hbetaMin hbeta hepsilon
  exact ⟨Nzero, fun N hN L hl hu => hcount N hN L hl hu _ (Finset.Subset.refl _)⟩

end
end PaperC.V282.DyadicRelationProfile
