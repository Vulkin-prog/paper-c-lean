import PaperCV282.RationalHeightMass
import PaperCV282.RationalGeometryMass
import PaperCV282.LogarithmicWordPowers
import PaperCV282.MacroscopicCanonicalCode

/-!
# The height-filtered and geometry-only rational profiles

The two canonical height populations retain their distinct square-root
and cube-root powers of `Q_B = 2^(L+1)`. The geometry-only sum uses the
binary weight `2^(m-1)`, without a translation factor. Polynomial length
factors are absorbed into an arbitrary `M^ε`, uniformly in the length.
-/

namespace PaperC.V282.RationalProfile

open RationalHeightMass RationalGeometryMass LogarithmicWordPowers MacroscopicGeometry

noncomputable section

/-- Both filtered populations are empty when the lower endpoint reaches the upper one. -/
theorem height_masses_eq_zero_of_upper_le_lower
    {N M A L : ℕ} (hMN : M ≤ N) :
    rationalHeightTwoMass N M A L = 0 ∧ rationalHeightAtLeastThreeMass N M A L = 0 := by
  simp [rationalHeightTwoMass, rationalHeightAtLeastThreeMass,
    BoundedRatioGeometry.separatedBoundedRatioPairs,
    BoundedRatioGeometry.boundedRatioPairs, BoundedRatioGeometry.boundedRatioBlock,
    Finset.Ico_eq_empty (not_lt_of_ge hMN)]

/-- Separate finite profiles for the actual canonical height filters. -/
theorem height_masses_le_word_profiles
    {N M A L : ℕ} (hM : 1 ≤ M) (hA : 1 ≤ A) :
    (rationalHeightTwoMass N M A L : ℝ) ≤
        6 * (M : ℝ) * (L + 1) ^ 4 * ((2 : ℝ) ^ (L + 1)) ^ (1 / (2 : ℝ)) ∧
      (rationalHeightAtLeastThreeMass N M A L : ℝ) ≤
        6 * (M : ℝ) * (L + 1) ^ 4 * ((2 : ℝ) ^ (L + 1)) ^ (1 / (3 : ℝ)) := by
  by_cases hNM : N ≤ M
  · have htwo : (rationalHeightTwoMass N M A L : ℝ) ≤
        6 * (M : ℝ) * (L + 1) * (2 : ℝ) ^ (L / 2) := by
      exact_mod_cast rationalHeightTwoMass_le_interval_profile (A := A) (L := L) hM hNM hA
    have hthree : (rationalHeightAtLeastThreeMass N M A L : ℝ) ≤
        4 * (M : ℝ) * (L + 1) ^ 4 * (2 : ℝ) ^ (L / 3) := by
      exact_mod_cast rationalHeightAtLeastThreeMass_le_interval_profile
        (A := A) (L := L) hM hNM hA
    have hlength : (L + 1 : ℝ) ≤ (L + 1 : ℝ) ^ 4 :=
      le_self_pow₀ (by exact_mod_cast (show 1 ≤ L + 1 by omega)) (by norm_num)
    constructor
    · refine htwo.trans ?_
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hlength (by positivity))
        (two_pow_div_le_word_rpow L 2 (by omega)) (by positivity) (by positivity)
    · refine hthree.trans ?_
      exact mul_le_mul (by gcongr; norm_num)
        (two_pow_div_le_word_rpow L 3 (by omega)) (by positivity) (by positivity)
  · obtain ⟨htwo, hthree⟩ := height_masses_eq_zero_of_upper_le_lower
      (A := A) (L := L) (by omega : M ≤ N)
    rw [htwo, hthree, Nat.cast_zero]
    constructor <;> positivity

/-- The two distinct powers in (3.12), uniformly in arbitrary interval lower endpoints. -/
theorem height_masses_uniform_profiles
    (C : ℝ) (hC : 0 ≤ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ L : ℕ,
      ((L + 1 : ℕ) : ℝ) ≤ C * Real.log M → ∀ N A : ℕ, 1 ≤ A →
      (rationalHeightTwoMass N M A L : ℝ) ≤
          (M : ℝ) ^ ε * ((M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (2 : ℝ))) ∧
        (rationalHeightAtLeastThreeMass N M A L : ℝ) ≤
          (M : ℝ) ^ ε * ((M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (3 : ℝ))) := by
  obtain ⟨Mpoly, hpoly⟩ := polynomial_factor_le_rpow_eventually C hC 6 4 ε hε
  refine ⟨max Mpoly 1, ?_⟩
  intro M hM L hL N A hA
  have hMone : 1 ≤ M := (le_max_right _ _).trans hM
  have hfactor : 6 * (L + 1 : ℝ) ^ 4 ≤ (M : ℝ) ^ ε := by
    have h := hpoly M ((le_max_left _ _).trans hM) L hL
    simpa only [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 6 * (L + 1 : ℝ) ^ 4)] using h
  obtain ⟨htwo, hthree⟩ := height_masses_le_word_profiles (N := N) (L := L) hMone hA
  constructor
  · refine htwo.trans ?_
    calc
      _ = (6 * (L + 1 : ℝ) ^ 4) *
          ((M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (2 : ℝ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hfactor (by positivity)
  · refine hthree.trans ?_
    calc
      _ = (6 * (L + 1 : ℝ) ^ 4) *
          ((M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (3 : ℝ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hfactor (by positivity)

/-- Finite base-two geometry profile, with no translation factor. -/
theorem geometryMass_le_word_profile (L : ℕ) :
    (geometryMass L : ℝ) ≤
      6 * (L + 1 : ℝ) ^ 4 * ((2 : ℝ) ^ (L + 1)) ^ (1 / (2 : ℝ)) := by
  have hfinite : (geometryMass L : ℝ) ≤
      6 * (L + 1 : ℝ) ^ 4 * (2 : ℝ) ^ (L / 2) := by
    exact_mod_cast geometryMass_le_poly_two_pow_half L
  exact hfinite.trans (mul_le_mul_of_nonneg_left
    (two_pow_div_le_word_rpow L 2 (by omega)) (by positivity))

/-- Equation (3.13), in the literal real-exponent formulation. -/
theorem geometryMass_uniform_profile
    (C : ℝ) (hC : 0 ≤ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ L : ℕ,
      ((L + 1 : ℕ) : ℝ) ≤ C * Real.log M →
      (geometryMass L : ℝ) ≤
        (M : ℝ) ^ ε * ((2 : ℝ) ^ (L + 1)) ^ (1 / (2 : ℝ)) := by
  obtain ⟨M₀, hM₀⟩ := polynomial_factor_le_rpow_eventually C hC 6 4 ε hε
  refine ⟨M₀, ?_⟩
  intro M hM L hL
  have hfactor : 6 * (L + 1 : ℝ) ^ 4 ≤ (M : ℝ) ^ ε := by
    have h := hM₀ M hM L hL
    simpa only [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 6 * (L + 1 : ℝ) ^ 4)] using h
  exact (geometryMass_le_word_profile L).trans
    (mul_le_mul_of_nonneg_right hfactor (by positivity))

/-- All three estimates of Proposition 3.8, on the exact macroscopic
domain with `A=3`, beyond a threshold that also guarantees uniqueness
of the candidate channel as in Lemma 3.3. -/
theorem proposition_three_eight
    (C δ : ℝ) (hC : 0 ≤ C) (hδ : 0 < δ) (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ L : ℕ,
      ((L + 1 : ℕ) : ℝ) ≤ C * Real.log M →
      (rationalHeightTwoMass ⌈(M : ℝ) ^ δ⌉₊ M 3 L : ℝ) ≤
          (M : ℝ) ^ ε * ((M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (2 : ℝ))) ∧
      (rationalHeightAtLeastThreeMass ⌈(M : ℝ) ^ δ⌉₊ M 3 L : ℝ) ≤
          (M : ℝ) ^ ε * ((M : ℝ) * ((2 : ℝ) ^ (L + 1)) ^ (1 / (3 : ℝ))) ∧
      (geometryMass L : ℝ) ≤
          (M : ℝ) ^ ε * ((2 : ℝ) ^ (L + 1)) ^ (1 / (2 : ℝ)) ∧
      (∀ x ∈ macroscopicStarts M δ, ∀ y : ℕ,
        (reducedChannelCandidates x y (L + 1) ((L + 1) ^ 3)).card ≤ 1) := by
  obtain ⟨Mh, hh⟩ := height_masses_uniform_profiles C hC ε hε
  obtain ⟨Mg, hg⟩ := geometryMass_uniform_profile C hC ε hε
  obtain ⟨Mc, hc⟩ := MacroscopicCanonicalCode.card_reduced_candidates_le_one_eventually C δ hC hδ
  refine ⟨max Mh (max Mg Mc), ?_⟩
  intro M hM L hL
  have hMh : Mh ≤ M := (le_max_left _ _).trans hM
  have hrest : max Mg Mc ≤ M := (le_max_right _ _).trans hM
  obtain ⟨htwo, hthree⟩ := hh M hMh L hL ⌈(M : ℝ) ^ δ⌉₊ 3 (by omega)
  exact ⟨htwo, hthree, hg M ((le_max_left _ _).trans hrest) L hL,
    hc M ((le_max_right _ _).trans hrest) L hL⟩

end
end PaperC.V282.RationalProfile
