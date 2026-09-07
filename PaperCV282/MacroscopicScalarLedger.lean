import PaperCV282.MacroscopicArithmeticBounds
import PaperCV282.MacroscopicRetentionBounds
import PaperCV282.FiniteStartMaskTransfer
import PaperCV282.PoissonIntensityBounds
import PaperCV282.HardPoissonRates

/-! # Scalar hard comparison on dense actual macroscopic masks -/
namespace PaperC.V282.MacroscopicScalarLedger

open Affine ArratiaGoldsteinGordonInput ConditionalAGGInstantiation ScalarSteinInput
open ConditionalStartProbability ConditionalAGGAverage SectionThirteenFiniteBound ScalarPoissonBounds
open FiniteStartMaskModel FiniteStartMaskAverages FiniteStartMaskTransfer PoissonIntensityBounds
open MacroscopicMaskGeometry MacroscopicRetentionBounds MacroscopicArithmeticBounds
open MacroscopicCutoffBounds MaskedArithmeticGeometry MaskedPairGeometry HostRankMass TwoWindowParity
open HardPoissonRates SaddleParameters SaddleScales SaddleCutoffAdmissibility PrimeEulerPNT AllStartSoftPoisson
open scoped NNReal

noncomputable section

theorem firstSteinFactor_le_four_of_quarter_le {mu lambda : ℝ≥0}
    (hquarter : (lambda : ℝ) / 4 ≤ (mu : ℝ)) :
    firstSteinFactor mu ≤ 4 * firstSteinFactor lambda := by
  by_cases hsmall : (lambda : ℝ) ≤ 1
  · rw [firstSteinFactor_eq_one_of_le_one hsmall]
    linarith [firstSteinFactor_le_one mu]
  · have hlambda : (0 : ℝ) < lambda := by linarith
    have hmu : (0 : ℝ) < mu := by linarith
    rw [firstSteinFactor_eq_inv_of_one_le (rate := lambda) (by linarith)]
    calc
      firstSteinFactor mu ≤ (mu : ℝ)⁻¹ := firstSteinFactor_le_inv (by exact_mod_cast hmu)
      _ ≤ ((lambda : ℝ) / 4)⁻¹ := inv_anti₀ (by positivity : (0 : ℝ) < (lambda : ℝ) / 4) hquarter
      _ = 4 * (lambda : ℝ)⁻¹ := by simp [div_eq_mul_inv]


/-- Numerical reduction after normalizing the genuine four arithmetic costs. -/
theorem scalar_normalized_budget_le {rate retained : ℝ≥0} {m d e r u b t : ℝ}
    (hquarter : (rate : ℝ) / 4 ≤ retained) (hb : 0 ≤ b) (ht : 0 ≤ t)
    (hm : m ≤ t) (hd : d ≤ b) (he : e ≤ b) (hu : u ≤ t)
    (hr : r ≤ t * ((rate : ℝ) ^ 2 + 2 * (rate : ℝ))) :
    (rate : ℝ) * (m + 2 * d) +
      2 * firstSteinFactor retained * ((rate : ℝ) ^ 2 * (u + e) + r) ≤
        40 * (rate : ℝ) * (b + t) := by
  have hf0 := firstSteinFactor_nonneg retained
  have hrate0 := rate.coe_nonneg
  have hf := firstSteinFactor_le_four_of_quarter_le hquarter
  have hs := firstSteinFactor_mul_square_le rate
  have hrho := firstSteinFactor_mul_square_add_twice_le_three_mul rate
  have hrough : (rate : ℝ) * (m + 2 * d) +
      2 * firstSteinFactor retained * ((rate : ℝ) ^ 2 * (u + e) + r) ≤
      (rate : ℝ) * (t + 2 * b) +
        8 * firstSteinFactor rate *
          ((rate : ℝ) ^ 2 * (t + b) + t * ((rate : ℝ) ^ 2 + 2 * (rate : ℝ))) := by
    calc
      _ ≤ (rate : ℝ) * (t + 2 * b) +
          2 * firstSteinFactor retained *
            ((rate : ℝ) ^ 2 * (t + b) + t * ((rate : ℝ) ^ 2 + 2 * (rate : ℝ))) := by gcongr
      _ ≤ _ := by
        have hbign : 0 ≤ (rate : ℝ) ^ 2 * (t + b) + t * ((rate : ℝ) ^ 2 + 2 * (rate : ℝ)) := by positivity
        have hh := mul_le_mul_of_nonneg_right hf hbign
        nlinarith
  have hs' := mul_le_mul_of_nonneg_right hs (add_nonneg ht hb)
  have hr' := mul_le_mul_of_nonneg_right hrho ht
  have hbt := mul_nonneg hrate0 hb
  have htt := mul_nonneg hrate0 ht
  nlinarith


/-- The actual arithmetic budget with its retained intensity. -/
def scalarLedger (C L Y : ℕ) (mask : Finset ℕ) : ℝ :=
  ((fullDefectMass L mask : ℝ)+2*(badMask L Y mask).card)/(2 : ℝ)^L +
    2*firstSteinFactor (maskRate L (goodMask L Y mask))*
      (((mask.card : ℝ)+(maskedSupportEdges L Y mask).card+
        (relationWeightMass C L (separatedPairs mask L) : ℝ))/(2 : ℝ)^(2*L))

/-- The arbitrary-mask normalization at the common ambient height. -/
theorem scalarLedger_normalization {N : ℕ} (hN : 0 < N) (C L Y : ℕ) (mask : Finset ℕ) :
    scalarLedger C L Y mask =
    (fullRate N L : ℝ) *
        ((fullDefectMass L mask : ℝ) / N + 2 * ((badMask L Y mask).card : ℝ) / N) +
      2 * firstSteinFactor (maskRate L (goodMask L Y mask)) *
        ((fullRate N L : ℝ) ^ 2 *
          ((mask.card : ℝ) / (N : ℝ)^2 + ((maskedSupportEdges L Y mask).card : ℝ) / (N : ℝ)^2) +
          (relationWeightMass C L (separatedPairs mask L) : ℝ) / (2 : ℝ)^(2*L)) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  have hp : (2 : ℝ)^L ≠ 0 := by positivity
  unfold scalarLedger
  rw [fullRate_coe, show 2 * L = L * 2 by omega, pow_mul]
  field_simp

/-- The scalar ledger retains its single ambient intensity throughout the logarithmic band. -/
theorem scalar_ledger_hard_rate_eventually
    (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax delta epsilon eta : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ C : ℕ, N + L ≤ C → ∀ mask : Finset ℕ, mask ⊆ Finset.Icc ⌈(N : ℝ)^delta⌉₊ N →
      (N : ℝ)/2 ≤ mask.card →
      scalarLedger C L (hardCutoff N) mask ≤ 40 * hardRate N L epsilon eta := by
  have hbetaMax := hbetaMin.trans hbeta
  obtain ⟨Nm, hm⟩ := MacroscopicArithmeticBounds.fullDefectMass_div_block_le_eventually
    betaMin betaMax delta epsilon hbetaMin hbeta hdelta hepsilon
  obtain ⟨Nr, hr⟩ := MacroscopicArithmeticBounds.normalized_relation_mass_le_eventually
    betaMin betaMax delta epsilon hbetaMin hbeta hdelta hepsilon
  obtain ⟨Nd, hd⟩ := MacroscopicCutoffBounds.normalized_badMask_saddle_le_eventually
    hPNT 1 betaMax eta (by norm_num) hbetaMax heta
  obtain ⟨Ne, he⟩ := MacroscopicCutoffBounds.normalized_degree_and_edges_saddle_le_eventually
    1 betaMax eta (by norm_num) hbetaMax heta
  obtain ⟨Ng, hg⟩ := card_goodMask_ge_quarter_eventually hPNT 1 betaMax (by norm_num) hbetaMax
  refine ⟨max 2 (max Nm (max Nr (max Nd (max Ne Ng)))), ?_⟩
  intro N hN L hlo hhi C hC mask hmask hdensity
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hone : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hbounded : mask ⊆ Finset.Icc 2 N := fun x hx =>
    closed_macroscopic_subset_Icc (M := N) (by omega) hdelta (hmask hx)
  have hm' : (fullDefectMass L mask : ℝ) / N ≤ (N : ℝ)^(-(1/(3 : ℝ))+epsilon) :=
    (hm N (by omega) L hlo hhi mask hmask).trans
      (Real.rpow_le_rpow_of_exponent_le hone (by linarith))
  have hd' := hd N (by omega) L hhi mask hbounded
  simp only [div_one] at hd'
  have he' := (he N (by omega) L hhi mask hbounded).2
  have hr' := hr N (by omega) L hlo hhi C hC mask hmask (separatedPairs mask L) (Finset.Subset.refl _)
  have hgood := hg N (by omega) L hhi mask hbounded hdensity
  have hquarter : (fullRate N L : ℝ)/4 ≤ maskRate L (goodMask L (hardCutoff N) mask) := by
    change _ ≤ ((goodMask L ⌊Real.exp (saddleCutoff 1 (Real.log N))⌋₊ mask).card : ℝ)/(2 : ℝ)^L
    rw [fullRate_coe]
    calc
      _ = ((N : ℝ)/4)/(2 : ℝ)^L := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hgood (by positivity)
  have hu : (mask.card : ℝ)/(N : ℝ)^2 ≤ (N : ℝ)^(-(1/(3 : ℝ))+epsilon) := by
    have hcard : (mask.card : ℝ) ≤ N := by exact_mod_cast card_mask_le hbounded
    calc
      _ ≤ (N : ℝ)/(N : ℝ)^2 := div_le_div_of_nonneg_right hcard (sq_nonneg _)
      _ = (N : ℝ)^(-1 : ℝ) := by rw [Real.rpow_neg_one]; field_simp
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hone (by linarith)
  rw [scalarLedger_normalization (N := N) (by omega)]
  simpa only [hardRate, hardCutoff, mul_div_assoc, mul_assoc] using
    scalar_normalized_budget_le hquarter (Real.exp_nonneg _)
      (Real.rpow_nonneg (by positivity) _) hm' hd' he' hu hr'

/-- The actual finite count law on every dense macroscopic mask. -/
theorem finite_scalar_hard_rate_eventually
    (hStein : ScalarSteinFactorsStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax delta epsilon eta : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ C : ℕ, N + L ≤ C → ∀ mask : Finset ℕ, mask ⊆ Finset.Icc ⌈(N : ℝ)^delta⌉₊ N →
      (N : ℝ)/2 ≤ mask.card →
      natTotalVariation (finiteLaw C L mask) (poissonMass (maskRate L mask)) ≤
        40 * hardRate N L epsilon eta := by
  obtain ⟨Nb, hb⟩ := scalar_ledger_hard_rate_eventually hPNT betaMin betaMax delta epsilon eta
    hbetaMin hbeta hdelta hepsilon heta
  obtain ⟨Na, ha⟩ := saddleCutoff_nat_admissible_eventually 1 betaMax (by norm_num) (hbetaMin.trans hbeta)
  obtain ⟨Nl, hl⟩ := TouchingPairMass.length_pos_eventually betaMin hbetaMin
  refine ⟨max 2 (max Nb (max Na Nl)), ?_⟩
  intro N hN L hlo hhi C hC mask hmask hdensity
  have hbounded : mask ⊆ Finset.Icc 2 N := fun x hx =>
    closed_macroscopic_subset_Icc (M := N) (by omega) hdelta (hmask hx)
  have hp := finite_scalar_tv_le (C := C) (Y := hardCutoff N) hStein mask
    (hl N (by omega) L hlo) (ha N (by omega) L hhi).2.2.1
    (fun x hx => (Finset.mem_Icc.mp (hbounded hx)).1)
    (by intro x hx; have := (Finset.mem_Icc.mp (hbounded hx)).2; omega)
  exact hp.trans (hb N (by omega) L hlo hhi C hC mask hmask hdensity)

end
end PaperC.V282.MacroscopicScalarLedger
