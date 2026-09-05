import PaperCV282.SizeTwoHostCounting
import PaperCV282.LogarithmicWordPowers
import PaperCV282.MacroscopicCanonicalCode

/-!
# Uniform linear size-two host counts and the seventh-sector profile

The finite harmonic/Euler count is `M^(1+epsilon)` throughout the fixed
logarithmic band. Combined with the actual rank deficit, this closes the
seventh residual sector with the explicit word-space factor `Q_B^(2/3)`.
-/

namespace PaperC.V282.SizeTwoHostAsymptotics

open PropositionSixteenOne BoundedRatioComponentHosts SizeTwoHostCounting
open ResidualSectorPartition ResidualSectorMass SectorSevenRank
open LogarithmicWordPowers MacroscopicGeometry

noncomputable section

/-- Convert the retained reciprocal-integer-power definition to real error exponents. -/
theorem uniformSubpolynomial_le_rpow_eventually
    {admissible : ℕ → ℕ → Prop} {f : ℕ → ℕ → ℝ}
    (hf : UniformSubpolynomialOn admissible f) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ, admissible M L →
      |f M L| ≤ (M : ℝ) ^ epsilon := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hepsilon
  obtain ⟨Mcore, hcore⟩ := hf (n + 1) (by omega)
  refine ⟨max Mcore 1, ?_⟩
  intro M hM L hL
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast (le_max_right Mcore 1).trans hM
  have hroot : |f M L| ≤ (M : ℝ) ^ (1 / (n + 1 : ℝ)) := by
    rw [one_div]
    apply (Real.le_rpow_inv_iff_of_pos (abs_nonneg _) (by positivity)
      (by positivity : (0 : ℝ) < n + 1)).mpr
    have hpower := hcore M ((le_max_left _ _).trans hM) L hL
    rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by norm_cast, Real.rpow_natCast]
    exact hpower
  exact hroot.trans (Real.rpow_le_rpow_of_exponent_le hMone hn.le)

/-- The entire polynomial/Euler factor is subpolynomial under the upper length ceiling. -/
theorem polynomial_euler_le_rpow_eventually
    (C a epsilon : ℝ) (hC : 0 ≤ C) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      ((L + 1 : ℕ) : ℝ) ≤ C * Real.log M →
      |a * (L + 1 : ℝ) ^ 5 * Real.exp (4 * Real.sqrt (L + 1 : ℝ))| ≤
        (M : ℝ) ^ epsilon := by
  have hpoly := polynomial_factor_uniformSubpolynomial C hC a 5
  have hexp := ExpSqrtLog.uniformSubpolynomialOn_exp_sqrt_of_le_log
    (fun M L => ((L + 1 : ℕ) : ℝ) ≤ C * Real.log M)
    (fun _ L => L + 1) 4 C (by norm_num) hC (fun _ _ h => h)
  simpa only [Nat.cast_add, Nat.cast_one] using
    uniformSubpolynomial_le_rpow_eventually (ExpSqrtLog.uniformSubpolynomialOn_mul hpoly hexp)
      epsilon hepsilon

/-- The harmonic logarithm is a linear factor in `B` inside the lower logarithmic band. -/
theorem cutoff_log_le_length_factor
    {M L : ℕ} {betaMin : ℝ} (hM : 2 ≤ M) (hL : L ≤ M)
    (hbetaMin : 0 < betaMin) (hlower : betaMin * Real.log M ≤ (L + 1 : ℝ)) :
    1 + Real.log (M + L : ℝ) ≤ (2 + 1 / betaMin) * (L + 1 : ℝ) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hcut : (M + L : ℝ) ≤ 2 * M := by exact_mod_cast (show M + L ≤ 2 * M by omega)
  have hlog : Real.log (M + L : ℝ) ≤ Real.log 2 + Real.log M := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hMpos.ne']
    exact Real.log_le_log (by positivity) hcut
  have hlogtwo : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hbound : Real.log M ≤ (L + 1 : ℝ) / betaMin := (le_div_iff₀ hbetaMin).mpr (by nlinarith)
  have hB : (1 : ℝ) ≤ L + 1 := by
    have hLnonneg : (0 : ℝ) ≤ L := by positivity
    linarith
  calc
    _ ≤ 2 + (L + 1 : ℝ) / betaMin := by linarith
    _ ≤ 2 * (L + 1 : ℝ) + (L + 1 : ℝ) / betaMin := by linarith
    _ = (2 + 1 / betaMin) * (L + 1 : ℝ) := by ring

/-- Uniform `M^(1+epsilon)` count, with no ratio restriction on the lower endpoint. -/
theorem card_sizeTwoHosts_le_linear_profile_eventually
    (betaMin betaMax epsilon : ℝ)
    (hbetaMin : 0 < betaMin) (hbetaMax : 0 ≤ betaMax) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M → ∀ N A : ℕ, 2 ≤ N →
      ((boundedComponentHosts N M A L 2).card : ℝ) ≤ (M : ℝ) ^ epsilon * M := by
  obtain ⟨Mfactor, hfactor⟩ := polynomial_euler_le_rpow_eventually betaMax
    (18 * (2 + 1 / betaMin)) epsilon hbetaMax hepsilon
  obtain ⟨Mlength, hlength⟩ := MacroscopicCanonicalCode.logarithmic_power_lt_rpow_eventually
    betaMax 1 hbetaMax (by norm_num) 1 (by omega)
  refine ⟨max Mfactor (max Mlength 2), ?_⟩
  intro M hM L hlower hupper N A hN
  have hrest : max Mlength 2 ≤ M := (le_max_right _ _).trans hM
  have hMtwo : 2 ≤ M := (le_max_right _ _).trans hrest
  have hML := hlength M ((le_max_left _ _).trans hrest) (L + 1) (by simpa using hupper)
  have hL : L ≤ M := by
    simp only [pow_one, Real.rpow_one, Nat.cast_add, Nat.cast_one] at hML
    have : (L : ℝ) ≤ M := by linarith
    exact_mod_cast this
  have hcut : (M + L : ℝ) ≤ 2 * M := by exact_mod_cast (show M + L ≤ 2 * M by omega)
  have hlog := cutoff_log_le_length_factor hMtwo hL hbetaMin hlower
  have hcoef : 0 ≤ 18 * (2 + 1 / betaMin) * (L + 1 : ℝ) ^ 5 *
      Real.exp (4 * Real.sqrt (L + 1 : ℝ)) := by positivity
  have hf := hfactor M ((le_max_left _ _).trans hM) L (by simpa using hupper)
  rw [abs_of_nonneg hcoef] at hf
  calc
    _ ≤ 9 * (L + 1 : ℝ) ^ 4 * (M + L : ℝ) *
        (1 + Real.log (M + L : ℝ)) * Real.exp (4 * Real.sqrt (L + 1 : ℝ)) :=
      card_sizeTwoHosts_cast_le_exp_bound hN
    _ ≤ 9 * (L + 1 : ℝ) ^ 4 * (2 * M) *
        ((2 + 1 / betaMin) * (L + 1 : ℝ)) * Real.exp (4 * Real.sqrt (L + 1 : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hlognonneg : 0 ≤ Real.log (M + L : ℝ) :=
          Real.log_nonneg (by exact_mod_cast (show 1 ≤ M + L by omega))
      exact mul_le_mul (mul_le_mul_of_nonneg_left hcut (by positivity)) hlog
        (by linarith) (by positivity)
    _ = (18 * (2 + 1 / betaMin) * (L + 1 : ℝ) ^ 5 *
        Real.exp (4 * Real.sqrt (L + 1 : ℝ))) * M := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hf (by positivity)

/-- The seventh sector's complete profile, uniformly on every positive-start interval. -/
theorem sector_seven_le_profile_eventually
    (betaMin betaMax epsilon : ℝ)
    (hbetaMin : 0 < betaMin) (hbetaMax : 0 ≤ betaMax) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M → ∀ N A : ℕ, 2 ≤ N →
      sectorMass A 6 N M L ≤ (M : ℝ) ^ epsilon *
        ((M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (2 / (3 : ℝ))) := by
  have heps : 0 < epsilon / 2 := by linarith
  obtain ⟨Mhost, hhost⟩ := card_sizeTwoHosts_le_linear_profile_eventually
    betaMin betaMax (epsilon / 2) hbetaMin hbetaMax heps
  obtain ⟨Mconst, hconst⟩ := polynomial_factor_le_rpow_eventually betaMax hbetaMax 8 0
    (epsilon / 2) heps
  refine ⟨max Mhost (max Mconst 1), ?_⟩
  intro M hM L hlower hupper N A hN
  have hrest : max Mconst 1 ≤ M := (le_max_right _ _).trans hM
  have hMpos : (0 : ℝ) < M := by exact_mod_cast
    (show 0 < M by have := (le_max_right _ _).trans hrest; omega)
  have hc := hhost M ((le_max_left _ _).trans hM) L hlower hupper N A hN
  have hcard : ((sectorPairs N M A L hN 6).card : ℝ) ≤
      ((boundedComponentHosts N M A L 2).card : ℝ) := by
    exact_mod_cast Finset.card_le_card
      (late_sectorPairs_subset_sizeTwoHosts (M := M) (A := A) (L := L) hN
        (sector := 6) (by decide))
  have hconstant : (8 : ℝ) ≤ (M : ℝ) ^ (epsilon / 2) := by
    simpa using hconst M ((le_max_left _ _).trans hrest) L (by simpa using hupper)
  calc
    _ ≤ ((sectorPairs N M A L hN 6).card : ℝ) *
        (8 * ((2 : ℝ) ^ (L + 1)) ^ (2 / (3 : ℝ))) :=
      sectorMass_le_card_mul_wordCount_two_thirds hN
    _ ≤ ((M : ℝ) ^ (epsilon / 2) * M) *
        (8 * ((2 : ℝ) ^ (L + 1)) ^ (2 / (3 : ℝ))) :=
      mul_le_mul_of_nonneg_right (hcard.trans hc) (by positivity)
    _ ≤ ((M : ℝ) ^ (epsilon / 2) * M) *
        ((M : ℝ) ^ (epsilon / 2) * ((2 : ℝ) ^ (L + 1)) ^ (2 / (3 : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right hconstant (by positivity)
    _ = _ := by
      calc
        _ = ((M : ℝ) ^ (epsilon / 2) * (M : ℝ) ^ (epsilon / 2)) *
            ((M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (2 / (3 : ℝ))) := by ring
        _ = _ := by rw [← Real.rpow_add hMpos, show epsilon / 2 + epsilon / 2 = epsilon by ring]

/-- Manuscript sector 7 on the literal macroscopic interval, with `Q_B` explicit. -/
theorem macroscopic_sector_seven_le_profile_eventually
    (betaMin betaMax epsilon : ℝ)
    (hbetaMin : 0 < betaMin) (hbetaMax : 0 ≤ betaMax) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M → ∀ delta : ℝ, 0 < delta → ∀ A : ℕ,
      sectorMass A 6 ⌈(M : ℝ) ^ delta⌉₊ M L ≤ (M : ℝ) ^ epsilon *
        ((M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (2 / (3 : ℝ))) := by
  obtain ⟨Mcore, hcore⟩ := sector_seven_le_profile_eventually
    betaMin betaMax epsilon hbetaMin hbetaMax hepsilon
  refine ⟨max Mcore 2, ?_⟩
  intro M hM L hlower hupper delta hdelta A
  exact hcore M ((le_max_left _ _).trans hM) L hlower hupper _ A
    (two_le_macroscopic_lowerEndpoint ((le_max_right _ _).trans hM) hdelta)

end
end PaperC.V282.SizeTwoHostAsymptotics
