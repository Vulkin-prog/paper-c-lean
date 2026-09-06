import PaperCV282.DictionaryProfileNormalization
import PaperCV282.BoundedRatioRelationProfiles
import PaperCV282.FullBandArithmetic
import PaperCV282.HardPoissonRates

/-!
# Actual capped relation costs for growing dictionaries

The threshold precedes the cardinality and the pair mask. Each site mass
is m/2^(L+1), and the cap is its reciprocal. These results normalize the
arithmetic ledger; the labelled field comparison is a separate proof.
-/

namespace PaperC.V282.DictionaryArithmeticRates

open DictionaryProfileNormalization BoundedRatioRelationProfiles CappedRelationMass
open TwoWindowParity SectionTwelveMoments MaskedArithmeticGeometry
open FullBandArithmetic ProfileMonomials LogarithmicWordPowers
open ScalarSteinInput PrimeEulerPNT SaddleArithmeticBounds HardPoissonRates
open SaddleParameters SaddleScales MaskedPairGeometry

noncomputable section

/-- The true capped value mass has the three dictionary exponents, uniformly in m. -/
theorem dictionary_capped_mass_le_eventually
    (betaMin betaMax epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ s : Finset (ℕ × ℕ), s ⊆ separatedPairs (dyadicBlock N) L →
      ∀ m : ℝ, 0 < m →
      (m / (2 : ℝ) ^ (L + 1)) ^ 2 *
          cappedValueMass (dyadicCutoff N L) L (1 / (m / (2 : ℝ) ^ (L + 1))) s ≤
        (N : ℝ) ^ (-(1 / (3 : ℝ)) + epsilon) *
          dictionaryPolynomialProfile ((N : ℝ) * (m / (2 : ℝ) ^ (L + 1))) m := by
  obtain ⟨Nzero,hzero⟩ := capped_masses_le_profile_dyadic_eventually
    betaMin betaMax epsilon hbetaMin hbeta hepsilon
  refine ⟨max Nzero 1, ?_⟩
  intro N hN L hlo hhi s hs m hm
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have ha : 0 < m / (2 : ℝ) ^ (L + 1) := by positivity
  have hQ : (2 : ℝ) ^ (L + 1) = m / (m / (2 : ℝ) ^ (L + 1)) := by
    field_simp
  have hcap := (hzero N (by omega) L hlo hhi s hs (1 / (m / (2 : ℝ) ^ (L + 1))) (by positivity)).2
  have hnum := normalized_cappedProfile_le hn ha hm.le hQ
  calc
    _ ≤ (m / (2 : ℝ) ^ (L + 1)) ^ 2 *
        ((N : ℝ) ^ epsilon * cappedProfile N ((2 : ℝ) ^ (L + 1)) (1 / (m / (2 : ℝ) ^ (L + 1)))) :=
      mul_le_mul_of_nonneg_left hcap (sq_nonneg _)
    _ = (N : ℝ) ^ epsilon * ((m / (2 : ℝ) ^ (L + 1)) ^ 2 *
        cappedProfile N ((2 : ℝ) ^ (L + 1)) (1 / (m / (2 : ℝ) ^ (L + 1)))) := by ring
    _ ≤ (N : ℝ) ^ epsilon * ((N : ℝ) ^ (-(1 / (3 : ℝ))) *
        dictionaryPolynomialProfile ((N : ℝ) * (m / (2 : ℝ) ^ (L + 1))) m) := by gcongr
    _ = _ := by rw [← mul_assoc, ← Real.rpow_add hn]; congr 2; ring

/-- The complete-vertex deletion first moment keeps only one intensity factor. -/
theorem dictionary_defect_cost_le_eventually
    (betaMin betaMax epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ mask : Finset ℕ, mask ⊆ dyadicBlock N → ∀ a : ℝ, 0 ≤ a →
        a * (fullDefectMass L mask : ℝ) ≤
          (N : ℝ) ^ (-(1 / (3 : ℝ)) + epsilon) * ((N : ℝ) * a) := by
  obtain ⟨Nzero,hzero⟩ := fullDefectMass_div_block_le_eventually
    betaMin betaMax epsilon hbetaMin hbeta hepsilon
  refine ⟨max Nzero 1, ?_⟩
  intro N hN L hlo hhi mask hmask a ha
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hone : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpow : (N : ℝ) ^ (-(1 / (2 : ℝ)) + epsilon) ≤
      (N : ℝ) ^ (-(1 / (3 : ℝ)) + epsilon) :=
    Real.rpow_le_rpow_of_exponent_le hone (by linarith)
  have hh := (hzero N (by omega) L hlo hhi mask hmask).trans hpow
  have hh' := (div_le_iff₀ hn).mp hh
  calc
    _ ≤ a * ((N : ℝ) ^ (-(1 / (3 : ℝ)) + epsilon) * N) :=
      mul_le_mul_of_nonneg_left hh' ha
    _ = _ := by ring

/-- The extra word-length factor in the first Poisson term is uniformly absorbed. -/
theorem dictionary_diagonal_length_le_eventually
    (betaMax epsilon : ℝ) (hbeta : 0 ≤ betaMax) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      (L + 1 : ℝ) ≤ betaMax * Real.log N → ∀ a m : ℝ,
      0 < a → a ≤ m →
      a ^ 2 * (N : ℝ) * (L + 1 : ℝ) ≤
        (N : ℝ) ^ (-(1 / (3 : ℝ)) + epsilon) *
          (((N : ℝ) * a) ^ (4 / (3 : ℝ)) * m ^ (2 / (3 : ℝ))) := by
  obtain ⟨Nzero,hzero⟩ := polynomial_factor_le_rpow_eventually betaMax hbeta 1 1 epsilon hepsilon
  refine ⟨max Nzero 1, ?_⟩
  intro N hN L hL a m ha ham
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlen : (L + 1 : ℝ) ≤ (N : ℝ) ^ epsilon := by
    simpa only [one_mul,pow_one,abs_of_nonneg (by positivity : (0 : ℝ) ≤ L + 1)] using
      hzero N (by omega) L (by simpa using hL)
  have hd := dictionary_diagonal_le hn ha ham
  have hm : 0 < m := ha.trans_le ham
  calc
    _ ≤ ((N : ℝ) ^ (-(1 / (3 : ℝ))) *
        (((N : ℝ) * a) ^ (4 / (3 : ℝ)) * m ^ (2 / (3 : ℝ)))) * (N : ℝ) ^ epsilon := by gcongr
    _ = _ := by
      rw [mul_right_comm, ← Real.rpow_add hn]

/-- The true hard-cutoff bad-site and graph costs keep lambda and lambda squared separately. -/
theorem dictionary_cutoff_costs_le_eventually
    (hPNT : PrimeNumberTheoremRemainder) (betaMax eta : ℝ)
    (hbeta : 0 < betaMax) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ mask : Finset ℕ, mask ⊆ dyadicBlock N → ∀ a : ℝ, 0 ≤ a →
      a * ((fullBadMask N L (hardCutoff N) mask).card : ℝ) ≤
        ((N : ℝ) * a) * Real.exp (-saddleCutoff 1 (Real.log N) + eta * saddleNu 1 (Real.log N)) ∧
      a ^ 2 * ((maskedSupportEdges L (hardCutoff N) mask).card : ℝ) ≤
        ((N : ℝ) * a) ^ 2 * Real.exp (-saddleCutoff 1 (Real.log N) + eta * saddleNu 1 (Real.log N)) := by
  obtain ⟨Nd,hd⟩ := normalized_fullBadMask_saddle_cost_le_eventually hPNT 1 betaMax eta
    (by norm_num) hbeta heta
  obtain ⟨Ne,he⟩ := normalized_degree_and_edges_saddle_le_eventually 1 betaMax eta
    (by norm_num) hbeta heta
  refine ⟨max Nd (max Ne 1), ?_⟩
  intro N hN L hL mask hmask a ha
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hdn := hd N (by omega) L hL mask
  simp only [div_one] at hdn
  have hd' := (div_le_iff₀ hn).mp hdn
  have he' := (div_le_iff₀ (sq_pos_of_pos hn)).mp (he N (by omega) L hL mask hmask).2
  change a * ((fullBadMask N L ⌊Real.exp (saddleCutoff 1 (Real.log N))⌋₊ mask).card : ℝ) ≤ _ ∧ _
  constructor
  · calc
      _ ≤ a * (Real.exp (-saddleCutoff 1 (Real.log N) + eta * saddleNu 1 (Real.log N)) * N) :=
        mul_le_mul_of_nonneg_left hd' ha
      _ = _ := by ring
  · change a ^ 2 * ((maskedSupportEdges L ⌊Real.exp (saddleCutoff 1 (Real.log N))⌋₊ mask).card : ℝ) ≤ _
    calc
      _ ≤ a ^ 2 * (Real.exp (-saddleCutoff 1 (Real.log N) + eta * saddleNu 1 (Real.log N)) * (N : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left he' (sq_nonneg a)
      _ = _ := by ring

end
end PaperC.V282.DictionaryArithmeticRates
