import PaperCV282.MacroscopicMaskGeometry
import PaperCV282.FullBandArithmetic

/-! # Actual first-moment and relation costs for closed macroscopic masks -/
namespace PaperC.V282.MacroscopicArithmeticBounds

open Affine TwoWindowParity HostRankMass MacroscopicRelationProfile WholeRelationProfile
open MacroscopicGeometry MacroscopicMaskGeometry FullBandArithmetic MacroscopicFirstMoment
open MaskedArithmeticGeometry DyadicRelationProfile ProfileMonomials LogarithmicWordPowers
open TouchingPairGeometry TouchingPairMass AllStartSoftPoisson
open scoped BigOperators

noncomputable section

theorem closed_macroscopic_subset_Icc {M : ℕ} (hM : 2 ≤ M) {delta : ℝ} (hdelta : 0 < delta) :
    Finset.Icc ⌈(M : ℝ) ^ delta⌉₊ M ⊆ Finset.Icc 2 M := by
  intro x hx
  have h := Finset.mem_Icc.mp hx
  exact Finset.mem_Icc.mpr ⟨(two_le_macroscopic_lowerEndpoint hM hdelta).trans h.1, h.2⟩

theorem relationWeightMass_cutoff_eq {K K' L : ℕ} (s : Finset (ℕ × ℕ))
    (hpos : ∀ xy ∈ s, 2 ≤ xy.1 ∧ 2 ≤ xy.2)
    (hK : ∀ xy ∈ s, xy.1 + L ≤ K ∧ xy.2 + L ≤ K)
    (hK' : ∀ xy ∈ s, xy.1 + L ≤ K' ∧ xy.2 + L ≤ K') :
    relationWeightMass K L s = relationWeightMass K' L s := by
  apply Finset.sum_congr rfl
  intro xy hxy
  rw [relationRho_cutoff_eq (hpos xy hxy).1 (hpos xy hxy).2 (hK xy hxy) (hK' xy hxy)]

theorem relationWeightMass_le_twice_macroscopic {M C L : ℕ} {delta : ℝ}
    (hM : 2 ≤ M) (hdelta : 0 < delta) (hC : M + L ≤ C)
    {mask : Finset ℕ} (hmask : mask ⊆ Finset.Icc ⌈(M : ℝ) ^ delta⌉₊ M)
    {pairs : Finset (ℕ × ℕ)} (hpairs : pairs ⊆ separatedPairs mask L) :
    relationWeightMass C L pairs ≤ macroscopicStartMassNat (2 * M) L (delta / 2) := by
  have hcoords (xy : ℕ × ℕ) (hxy : xy ∈ pairs) : xy.1 ∈ Finset.Icc 2 M ∧ xy.2 ∈ Finset.Icc 2 M := by
    obtain ⟨hx, hy, _⟩ := (mem_separatedPairs _ _ _ _).mp (hpairs hxy)
    exact ⟨closed_macroscopic_subset_Icc hM hdelta (hmask hx),
      closed_macroscopic_subset_Icc hM hdelta (hmask hy)⟩
  rw [relationWeightMass_cutoff_eq pairs (K' := 2 * M + L)
    (fun xy hxy => ⟨(Finset.mem_Icc.mp (hcoords xy hxy).1).1,
      (Finset.mem_Icc.mp (hcoords xy hxy).2).1⟩)
    (by intro xy hxy; obtain ⟨hx, hy⟩ := hcoords xy hxy; simp only [Finset.mem_Icc] at hx hy; constructor <;> omega)
    (by intro xy hxy; obtain ⟨hx, hy⟩ := hcoords xy hxy; simp only [Finset.mem_Icc] at hx hy; constructor <;> omega)]
  apply relationWeightMass_mono
  intro xy hxy
  obtain ⟨hx, hy, hd⟩ := (mem_separatedPairs _ _ _ _).mp (hpairs hxy)
  exact (mem_separatedPairs _ _ _ _).mpr
    ⟨closed_macroscopic_subset_twice hM hdelta (hmask hx),
      closed_macroscopic_subset_twice hM hdelta (hmask hy), hd⟩

/-- The full-defect mass on every closed macroscopic mask, including its upper endpoint. -/
theorem fullDefectMass_le_half_power_eventually
    (betaMin betaMax delta epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ mask : Finset ℕ, mask ⊆ Finset.Icc ⌈(N : ℝ) ^ delta⌉₊ N →
        (fullDefectMass L mask : ℝ) ≤ (N : ℝ) ^ (1 / (2 : ℝ) + epsilon) := by
  obtain ⟨Nm, hm⟩ := sum_fullDefectWeight_le_half_power_eventually
    (betaMin / 2) betaMax (delta / 2) (epsilon / 2)
    (by positivity) (by linarith) (by positivity) (by positivity)
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
    (fun x hx => closed_macroscopic_subset_twice hNtwo hdelta (hmask hx))
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

/-- The actual separated relation mass at any adequate cylinder, uniformly before all masks. -/
theorem relationWeightMass_mask_le_coarse_eventually
    (betaMin betaMax delta epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ C : ℕ, N + L ≤ C → ∀ mask : Finset ℕ, mask ⊆ Finset.Icc ⌈(N : ℝ) ^ delta⌉₊ N →
      ∀ s : Finset (ℕ × ℕ), s ⊆ separatedPairs mask L →
      (relationWeightMass C L s : ℝ) ≤ (N : ℝ) ^ epsilon * coarseProfile N ((2 : ℝ) ^ (L + 1)) := by
  have heps : 0 < epsilon / 2 := by positivity
  obtain ⟨Nmacro, hmacro⟩ := theorem_three_one_coarse_macroscopic
    (betaMin / 2) betaMax (delta / 2) (epsilon / 2) (by positivity) (by linarith) (by positivity) heps
  obtain ⟨Nconstant, hconstant⟩ := polynomial_factor_le_rpow_eventually
    betaMax (hbetaMin.trans hbeta).le (4 * (2 : ℝ) ^ (epsilon / 2)) 0 (epsilon / 2) heps
  refine ⟨max Nmacro (max Nconstant 2), ?_⟩
  intro N hN L hlower hupper C hC mask hmask s hs
  have hNtwo : 2 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨hl, hu⟩ := logarithmic_band_at_twice hNtwo hbetaMin.le (hbetaMin.trans hbeta).le hlower hupper
  have hm := hmacro (2 * N) (by omega) L hl hu
  have hf : (relationWeightMass C L s : ℝ) ≤ (macroscopicStartMassNat (2 * N) L (delta / 2) : ℝ) := by
    exact_mod_cast relationWeightMass_le_twice_macroscopic hNtwo hdelta hC hmask hs
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



/-- Full support defects normalized by the common ambient height. -/
theorem fullDefectMass_div_block_le_eventually
    (betaMin betaMax delta epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ mask : Finset ℕ, mask ⊆ Finset.Icc ⌈(N : ℝ) ^ delta⌉₊ N →
        (fullDefectMass L mask : ℝ) / N ≤ (N : ℝ) ^ (-(1 / (2 : ℝ)) + epsilon) := by
  obtain ⟨Nzero,hzero⟩ := fullDefectMass_le_half_power_eventually
    betaMin betaMax delta epsilon hbetaMin hbeta hdelta hepsilon
  refine ⟨max Nzero 1, ?_⟩
  intro N hN L hl hu mask hmask
  have hh := div_le_div_of_nonneg_right (hzero N (by omega) L hl hu mask hmask)
    (show (0 : ℝ) ≤ N by positivity)
  apply hh.trans_eq
  rw [rpow_div_block (by omega)]
  congr 1
  ring

/-- Normalization uses the ambient intensity M/2^L, with no comparability assumption on a mask. -/
theorem normalized_relation_mass_le_eventually
    (betaMin betaMax delta epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ C : ℕ, N + L ≤ C → ∀ mask : Finset ℕ, mask ⊆ Finset.Icc ⌈(N : ℝ) ^ delta⌉₊ N →
      ∀ s : Finset (ℕ × ℕ), s ⊆ separatedPairs mask L →
      (relationWeightMass C L s : ℝ) / (2 : ℝ) ^ (2 * L) ≤
        (N : ℝ) ^ (-(1 / (3 : ℝ)) + epsilon) *
          ((fullRate N L : ℝ) ^ 2 + 2 * (fullRate N L : ℝ)) := by
  obtain ⟨Nzero,hzero⟩ := relationWeightMass_mask_le_coarse_eventually
    betaMin betaMax delta epsilon hbetaMin hbeta hdelta hepsilon
  refine ⟨max Nzero 1, ?_⟩
  intro N hN L hl hu C hC mask hmask s hs
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ ((N : ℝ) ^ epsilon * coarseProfile N ((2 : ℝ) ^ (L + 1))) /
        (2 : ℝ) ^ (2 * L) := div_le_div_of_nonneg_right
          (hzero N (by omega) L hl hu C hC mask hmask s hs) (by positivity)
    _ = (N : ℝ) ^ epsilon *
        (coarseProfile N ((2 : ℝ) ^ (L + 1)) / (2 : ℝ) ^ (2 * L)) := by ring
    _ = _ := by rw [coarseProfile_div_runSquare_eq (by omega), ← mul_assoc, ← Real.rpow_add hn]; congr 2; ring

/-- The same touching mass at two adequate cylinders. -/
theorem homogeneousTouchingMass_cutoff_eq {K K' L : ℕ} (s : Finset ℕ)
    (hpos : ∀ x ∈ s, 2 ≤ x)
    (hK : ∀ x ∈ s, x + L ≤ K) (hK' : ∀ x ∈ s, x + L ≤ K') :
    homogeneousTouchingMass K L s = homogeneousTouchingMass K' L s := by
  apply Finset.sum_congr rfl
  intro xy hxy
  obtain ⟨hx, hy, _⟩ := mem_touchingPairsOn.mp hxy
  rw [relationRho_cutoff_eq (hpos _ hx) (hpos _ hy) ⟨hK _ hx, hK _ hy⟩ ⟨hK' _ hx, hK' _ hy⟩]

theorem homogeneousTouchingMass_mono {K L : ℕ} {s t : Finset ℕ} (hst : s ⊆ t) :
    homogeneousTouchingMass K L s ≤ homogeneousTouchingMass K L t := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro xy hxy
    obtain ⟨hx, hy, hd⟩ := mem_touchingPairsOn.mp hxy
    exact mem_touchingPairsOn.mpr ⟨hst hx, hst hy, hd⟩
  · intro xy _ _
    positivity

/-- The actual touching pairs on a closed macroscopic mask and every adequate cylinder. -/
theorem touching_mass_le_eventually
    (betaMin betaMax delta epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ C : ℕ, N + L ≤ C → ∀ mask : Finset ℕ, mask ⊆ Finset.Icc ⌈(N : ℝ) ^ delta⌉₊ N →
      homogeneousTouchingMass C L mask ≤ (N : ℝ) ^ (1 + epsilon) := by
  have heps : 0 < epsilon / 2 := by positivity
  obtain ⟨Nmass, hmass⟩ := macroscopic_homogeneousTouchingMass_le_eventually
    (betaMin / 2) betaMax (delta / 2) (epsilon / 2) (by positivity) (by linarith)
    (by positivity) heps
  obtain ⟨Nconstant, hconstant⟩ := polynomial_factor_le_rpow_eventually
    betaMax (hbetaMin.trans hbeta).le ((2 : ℝ) ^ (1 + epsilon / 2)) 0 (epsilon / 2) heps
  refine ⟨max Nmass (max Nconstant 2), ?_⟩
  intro N hN L hlo hhi C hC mask hmask
  have hNtwo : 2 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨hl, hu⟩ := logarithmic_band_at_twice hNtwo hbetaMin.le (hbetaMin.trans hbeta).le hlo hhi
  have hcoords (x : ℕ) (hx : x ∈ mask) : x ∈ Finset.Icc 2 N :=
    closed_macroscopic_subset_Icc hNtwo hdelta (hmask hx)
  have heq := homogeneousTouchingMass_cutoff_eq mask (L := L) (K := C) (K' := 2 * N + L)
    (fun x hx => (Finset.mem_Icc.mp (hcoords x hx)).1)
    (by intro x hx; have := (Finset.mem_Icc.mp (hcoords x hx)).2; omega)
    (by intro x hx; have := (Finset.mem_Icc.mp (hcoords x hx)).2; omega)
  have hm := hmass (2 * N) (by omega) L hl hu (2 * N + L)
    (by intro x hx; have := (Finset.mem_Ico.mp hx).2; omega)
  have hsub : mask ⊆ macroscopicStarts (2 * N) (delta / 2) :=
    fun x hx => closed_macroscopic_subset_twice hNtwo hdelta (hmask hx)
  have hc : (2 : ℝ) ^ (1 + epsilon / 2) ≤ (N : ℝ) ^ (epsilon / 2) := by
    simpa only [pow_zero, mul_one, abs_of_pos (by positivity : 0 < (2 : ℝ) ^ (1 + epsilon / 2))]
      using hconstant N (by omega) L (by simpa using hhi)
  rw [heq]
  calc
    _ ≤ homogeneousTouchingMass (2 * N + L) L (macroscopicStarts (2 * N) (delta / 2)) :=
      homogeneousTouchingMass_mono hsub
    _ ≤ ((2 * N : ℕ) : ℝ) ^ (1 + epsilon / 2) := hm
    _ = (2 : ℝ) ^ (1 + epsilon / 2) * (N : ℝ) ^ (1 + epsilon / 2) := by
      push_cast
      exact Real.mul_rpow (by norm_num) hNpos.le
    _ ≤ (N : ℝ) ^ (epsilon / 2) * (N : ℝ) ^ (1 + epsilon / 2) := by gcongr
    _ = _ := by rw [← Real.rpow_add hNpos]; congr 1; ring

end
end PaperC.V282.MacroscopicArithmeticBounds
