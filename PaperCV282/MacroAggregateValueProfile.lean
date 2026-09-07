import PaperCV282.MacroscopicArithmeticBounds
import PaperCV282.DyadicFullValueProfile
import PaperCV282.MacroAggregateCosts

/-! # Full-value profiles on actual closed macroscopic masks and enlarged marked windows -/
namespace PaperC.V282.MacroAggregateValueProfile

open Affine TwoWindowParity HostRankMass MacroscopicRelationProfile WholeRelationProfile
open MacroscopicGeometry MacroscopicMaskGeometry FullBandArithmetic MacroscopicFirstMoment
open MaskedArithmeticGeometry DyadicRelationProfile ProfileMonomials LogarithmicWordPowers
open MacroscopicArithmeticBounds RelationProfileRestriction AllStartSoftPoisson
open scoped BigOperators

noncomputable section

theorem valueWeightMass_cutoff_eq {K K' L : ℕ} (s : Finset (ℕ × ℕ))
    (hpos : ∀ xy ∈ s, 2 ≤ xy.1 ∧ 2 ≤ xy.2)
    (hK : ∀ xy ∈ s, xy.1 + L ≤ K ∧ xy.2 + L ≤ K)
    (hK' : ∀ xy ∈ s, xy.1 + L ≤ K' ∧ xy.2 + L ≤ K') :
    valueWeightMass K L s = valueWeightMass K' L s := by
  apply Finset.sum_congr rfl
  intro xy hxy
  rw [value_relationRho_cutoff_eq (K := K) (K' := K') (hpos xy hxy).1 (hpos xy hxy).2 (by obtain ⟨hx, hy⟩ := hK xy hxy; constructor <;> omega)
    (by obtain ⟨hx, hy⟩ := hK' xy hxy; constructor <;> omega)]

theorem valueWeightMass_le_twice_macroscopic {M C L : ℕ} {delta : ℝ}
    (hM : 2 ≤ M) (hdelta : 0 < delta) (hC : M + L ≤ C)
    {mask : Finset ℕ} (hmask : mask ⊆ Finset.Icc ⌈(M : ℝ) ^ delta⌉₊ M)
    {pairs : Finset (ℕ × ℕ)} (hpairs : pairs ⊆ separatedPairs mask L) :
    valueWeightMass C L pairs ≤ macroscopicValueMassNat (2 * M) L (delta / 2) := by
  have hcoords (xy : ℕ × ℕ) (hxy : xy ∈ pairs) : xy.1 ∈ Finset.Icc 2 M ∧ xy.2 ∈ Finset.Icc 2 M := by
    obtain ⟨hx, hy, _⟩ := (mem_separatedPairs _ _ _ _).mp (hpairs hxy)
    exact ⟨closed_macroscopic_subset_Icc hM hdelta (hmask hx),
      closed_macroscopic_subset_Icc hM hdelta (hmask hy)⟩
  rw [valueWeightMass_cutoff_eq pairs (K' := 2 * M + L)
    (fun xy hxy => ⟨(Finset.mem_Icc.mp (hcoords xy hxy).1).1,
      (Finset.mem_Icc.mp (hcoords xy hxy).2).1⟩)
    (by intro xy hxy; obtain ⟨hx, hy⟩ := hcoords xy hxy; simp only [Finset.mem_Icc] at hx hy; constructor <;> omega)
    (by intro xy hxy; obtain ⟨hx, hy⟩ := hcoords xy hxy; simp only [Finset.mem_Icc] at hx hy; constructor <;> omega)]
  apply MacroAggregateCosts.valueWeightMass_mono
  intro xy hxy
  obtain ⟨hx, hy, hd⟩ := (mem_separatedPairs _ _ _ _).mp (hpairs hxy)
  exact (mem_separatedPairs _ _ _ _).mpr
    ⟨closed_macroscopic_subset_twice hM hdelta (hmask hx),
      closed_macroscopic_subset_twice hM hdelta (hmask hy), hd⟩

/-- The actual separated relation mass at any adequate cylinder, uniformly before all masks. -/
theorem valueWeightMass_mask_le_coarse_eventually
    (betaMin betaMax delta epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ C : ℕ, N + L ≤ C → ∀ mask : Finset ℕ, mask ⊆ Finset.Icc ⌈(N : ℝ) ^ delta⌉₊ N →
      ∀ s : Finset (ℕ × ℕ), s ⊆ separatedPairs mask L →
      (valueWeightMass C L s : ℝ) ≤ (N : ℝ) ^ epsilon * coarseProfile N ((2 : ℝ) ^ (L + 1)) := by
  have heps : 0 < epsilon / 2 := by positivity
  obtain ⟨Nmacro, hmacro⟩ := proposition_three_twenty_six_coarse_macroscopic
    (betaMin / 2) betaMax (delta / 2) (epsilon / 2) (by positivity) (by linarith) (by positivity) heps
  obtain ⟨Nconstant, hconstant⟩ := polynomial_factor_le_rpow_eventually
    betaMax (hbetaMin.trans hbeta).le (4 * (2 : ℝ) ^ (epsilon / 2)) 0 (epsilon / 2) heps
  refine ⟨max Nmacro (max Nconstant 2), ?_⟩
  intro N hN L hlower hupper C hC mask hmask s hs
  have hNtwo : 2 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨hl, hu⟩ := logarithmic_band_at_twice hNtwo hbetaMin.le (hbetaMin.trans hbeta).le hlower hupper
  have hm := hmacro (2 * N) (by omega) L hl hu
  have hf : (valueWeightMass C L s : ℝ) ≤ (macroscopicValueMassNat (2 * N) L (delta / 2) : ℝ) := by
    exact_mod_cast valueWeightMass_le_twice_macroscopic hNtwo hdelta hC hmask hs
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



/-- Normalization uses the ambient intensity M/2^L, with no comparability assumption on a mask. -/
theorem normalized_value_mass_le_eventually
    (betaMin betaMax delta epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ C : ℕ, N + L ≤ C → ∀ mask : Finset ℕ, mask ⊆ Finset.Icc ⌈(N : ℝ) ^ delta⌉₊ N →
      ∀ s : Finset (ℕ × ℕ), s ⊆ separatedPairs mask L →
      (valueWeightMass C L s : ℝ) / (2 : ℝ) ^ (2 * L) ≤
        (N : ℝ) ^ (-(1 / (3 : ℝ)) + epsilon) *
          ((fullRate N L : ℝ) ^ 2 + 2 * (fullRate N L : ℝ)) := by
  obtain ⟨Nzero,hzero⟩ := valueWeightMass_mask_le_coarse_eventually
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

/-- The enlarged signed profile retains its exact exponential length cost. -/
theorem enlarged_valueWeightMass_le_eventually
    (betaMin betaMax delta epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L E : ℕ,
      betaMin * Real.log N ≤ (L+E+2 : ℝ) → (L+E+2 : ℝ) ≤ betaMax * Real.log N →
      ∀ C : ℕ, N+(L+E+1) ≤ C →
      ∀ mask : Finset ℕ, mask ⊆ Finset.Icc ⌈(N : ℝ)^delta⌉₊ N →
      (1/(2 : ℝ)^L)^2 *
        (valueWeightMass C (L+E+1) (separatedPairs mask (L+E+1)) : ℝ) ≤
      (2 : ℝ)^(2*E+2)*(N : ℝ)^(-(1/(3 : ℝ))+epsilon)*
        ((fullRate N L : ℝ)^2+2*(fullRate N L : ℝ)) := by
  obtain ⟨Nzero,hzero⟩ := normalized_value_mass_le_eventually
    betaMin betaMax delta epsilon hbetaMin hbeta hdelta hepsilon
  refine ⟨Nzero, ?_⟩
  intro N hN L E hlo hhi C hC mask hmask
  have h := hzero N hN (L+E+1) (by push_cast; linarith) (by push_cast; linarith) C hC mask hmask _ (Finset.Subset.refl _)
  have hmono := DyadicFullValueProfile.fullRate_mono_length N (show L ≤ L+E+1 by omega)
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
        ((valueWeightMass C (L+E+1) (separatedPairs mask (L+E+1)) : ℝ)/
          (2 : ℝ)^(2*(L+E+1))) := by ring
    _ ≤ (2 : ℝ)^(2*E+2)*((N : ℝ)^(-(1/(3 : ℝ))+epsilon)*
        ((fullRate N (L+E+1) : ℝ)^2+2*(fullRate N (L+E+1) : ℝ))) := hm
    _ = ((2 : ℝ)^(2*E+2)*(N : ℝ)^(-(1/(3 : ℝ))+epsilon))*
        ((fullRate N (L+E+1) : ℝ)^2+2*(fullRate N (L+E+1) : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpoly (by positivity)

end
end PaperC.V282.MacroAggregateValueProfile
