import PaperCV282.DyadicRelationProfile
import PaperCV282.CriticalProfileNormalization
import PaperCV282.MacroscopicFirstMoment
import PaperCV282.MaskedBadMass
import PaperCV282.AllStartSoftPoisson
import PaperCV282.TouchingPairMass

/-!
# Actual arithmetic costs with an unrestricted Poisson intensity

The logarithmic band is fixed before the run length. The intensity is
N/2^L throughout; no bounded-intensity or critical-window premise enters
these normalizations. Full defects include the left boundary vertex.
-/

namespace PaperC.V282.FullBandArithmetic

open Affine SectionTwelveMoments TwoWindowParity DyadicRelationProfile
open ProfileMonomials CriticalProfileNormalization MacroscopicFirstMoment
open MaskedArithmeticGeometry MaskedBadMass WindowValues LogarithmicWordPowers
open AllStartSoftPoisson TouchingPairMass
open scoped BigOperators

noncomputable section

/-- The full defective-vertex mass as a real sum, without truncated subtraction. -/
theorem fullDefectMass_cast_real (L : ℕ) (mask : Finset ℕ) :
    (fullDefectMass L mask : ℝ) =
      ∑ x ∈ mask, ((2 : ℝ) ^ (defectIndices (L + 1) x (L + 1)).card - 1) := by
  unfold fullDefectMass
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Nat.cast_sub (one_le_pow₀ (by omega : 1 ≤ (2 : ℕ)))]
  norm_num

/-- The square-root full-defect bound on the literal dyadic block and every submask. -/
theorem fullDefectMass_le_half_power_eventually
    (betaMin betaMax epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ mask : Finset ℕ, mask ⊆ dyadicBlock N →
        (fullDefectMass L mask : ℝ) ≤ (N : ℝ) ^ (1 / (2 : ℝ) + epsilon) := by
  obtain ⟨Nm, hm⟩ := sum_fullDefectWeight_le_half_power_eventually
    (betaMin / 2) betaMax (1 / (2 : ℝ)) (epsilon / 2)
    (by positivity) (by linarith) (by norm_num) (by positivity)
  obtain ⟨Nc, hc⟩ := polynomial_factor_le_rpow_eventually betaMax
    (hbetaMin.trans hbeta).le ((2 : ℝ) ^ (1 / (2 : ℝ) + epsilon / 2)) 0
    (epsilon / 2) (by positivity)
  refine ⟨max Nm (max Nc 2), ?_⟩
  intro N hN L hl hu mask hmask
  have hNtwo : 2 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨hlo,hhi⟩ := logarithmic_band_at_twice hNtwo hbetaMin.le
    (hbetaMin.trans hbeta).le hl hu
  have hs := hm (2 * N) (by omega) L hlo hhi mask
    (fun x hx => dyadicBlock_subset_macroscopic hNtwo (hmask hx))
  have hfactor : (2 : ℝ) ^ (1 / (2 : ℝ) + epsilon / 2) ≤ (N : ℝ) ^ (epsilon / 2) := by
    simpa only [pow_zero, mul_one, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ (1 / (2 : ℝ) + epsilon / 2))] using
      hc N (by omega) L (by simpa using hu)
  rw [fullDefectMass_cast_real]
  calc
    _ ≤ ((2 * N : ℕ) : ℝ) ^ (1 / (2 : ℝ) + epsilon / 2) := hs
    _ = (2 : ℝ) ^ (1 / (2 : ℝ) + epsilon / 2) *
        (N : ℝ) ^ (1 / (2 : ℝ) + epsilon / 2) := by
      push_cast
      exact Real.mul_rpow (by norm_num) hNpos.le
    _ ≤ (N : ℝ) ^ (epsilon / 2) * (N : ℝ) ^ (1 / (2 : ℝ) + epsilon / 2) := by gcongr
    _ = _ := by rw [← Real.rpow_add hNpos]; congr 1; ring

/-- Dividing a real power by the positive block size shifts its exponent exactly. -/
theorem rpow_div_block {N : ℕ} (hN : 0 < N) (a : ℝ) :
    (N : ℝ) ^ a / N = (N : ℝ) ^ (a - 1) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.rpow_sub hn, Real.rpow_one]

/-- The normalized complete-defect mass has a uniform half-power saving. -/
theorem fullDefectMass_div_block_le_eventually
    (betaMin betaMax epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ mask : Finset ℕ, mask ⊆ dyadicBlock N →
        (fullDefectMass L mask : ℝ) / N ≤ (N : ℝ) ^ (-(1 / (2 : ℝ)) + epsilon) := by
  obtain ⟨Nzero,hzero⟩ := fullDefectMass_le_half_power_eventually
    betaMin betaMax epsilon hbetaMin hbeta hepsilon
  refine ⟨max Nzero 1, ?_⟩
  intro N hN L hl hu mask hmask
  have hh := div_le_div_of_nonneg_right (hzero N (by omega) L hl hu mask hmask)
    (show (0 : ℝ) ≤ N by positivity)
  apply hh.trans_eq
  rw [rpow_div_block (by omega)]
  congr 1
  ring

/-- The exact whole-block intensity, including both powers of two in a two-start law. -/
theorem coarseProfile_div_runSquare_eq {N L : ℕ} (hN : 0 < N) :
    coarseProfile N ((2 : ℝ) ^ (L + 1)) / (2 : ℝ) ^ (2 * L) =
      (N : ℝ) ^ (-(1 / (3 : ℝ))) *
        (((fullRate N L : ℝ)) ^ 2 + 2 * (fullRate N L : ℝ)) := by
  have hh := coarseProfile_div_square_eq (by exact_mod_cast hN : (0 : ℝ) < N)
    (by positivity : (0 : ℝ) < (2 : ℝ) ^ L)
  simpa only [fullRate_coe, pow_succ, show 2 * L = L * 2 by omega, pow_mul, mul_comm] using hh

/-- The two separated-pair presentations agree on the actual dyadic block. -/
theorem separatedPairs_block_eq (N L : ℕ) :
    separatedPairs (dyadicBlock N) L = separatedOffDiagPairs N L := by
  ext p
  rcases p with ⟨x,y⟩
  rw [TwoWindowParity.mem_separatedPairs, mem_separatedOffDiagPairs]
  constructor
  · rintro ⟨hx,hy,hd⟩
    refine ⟨hx,hy,?_,hd⟩
    intro h
    change x = y at h
    subst y
    simp at hd
  · rintro ⟨hx,hy,_,hd⟩
    exact ⟨hx,hy,hd⟩

/-- The real relation contribution, uniformly with variable intensity on the whole band. -/
theorem normalized_relation_mass_le_eventually
    (betaMin betaMax epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      (jointDefectMass N L (separatedPairs (dyadicBlock N) L) : ℝ) / (2 : ℝ) ^ (2 * L) ≤
        (N : ℝ) ^ (-(1 / (3 : ℝ)) + epsilon) *
          ((fullRate N L : ℝ) ^ 2 + 2 * (fullRate N L : ℝ)) := by
  obtain ⟨Nzero,hzero⟩ := jointDefectMass_separated_le_coarse_eventually
    betaMin betaMax epsilon hbetaMin hbeta hepsilon
  refine ⟨max Nzero 1, ?_⟩
  intro N hN L hl hu
  rw [separatedPairs_block_eq]
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ ((N : ℝ) ^ epsilon * coarseProfile N ((2 : ℝ) ^ (L + 1))) /
        (2 : ℝ) ^ (2 * L) := div_le_div_of_nonneg_right (hzero N (by omega) L hl hu) (by positivity)
    _ = (N : ℝ) ^ epsilon *
        (coarseProfile N ((2 : ℝ) ^ (L + 1)) / (2 : ℝ) ^ (2 * L)) := by ring
    _ = _ := by rw [coarseProfile_div_runSquare_eq (by omega), ← mul_assoc, ← Real.rpow_add hn]; congr 2; ring

/-- The genuine touching mass uses the same cylinder as the count law. -/
theorem touching_mass_le_eventually
    (betaMin betaMax epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      homogeneousTouchingMass (dyadicCutoff N L) L (dyadicBlock N) ≤ (N : ℝ) ^ (1 + epsilon) := by
  obtain ⟨Nzero,hzero⟩ := dyadic_homogeneousTouchingMass_le_eventually
    betaMin betaMax epsilon hbetaMin hbeta hepsilon
  refine ⟨Nzero, fun N hN L hl hu => hzero N hN L hl hu _ ?_⟩
  intro x hx
  have hr := Finset.mem_Ico.mp hx
  unfold dyadicCutoff
  omega

end
end PaperC.V282.FullBandArithmetic
