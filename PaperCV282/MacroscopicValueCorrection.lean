import PaperCV282.MacroscopicRelationProfile
import PaperCV282.FullIntervalHostAsymptotics

/-!
# Uniform positive correction for prescribed values

The finite factor-four comparison and the proved macroscopic host bound
control the positive excess of the full-value mass over four times the
start mass. This is an unconditional correction estimate. It does not
assume or prove the raw weighted profile of Theorem 3.1.
-/

namespace PaperC.V282.MacroscopicValueCorrection

open MacroscopicRelationProfile MacroscopicGeometry TwoWindowParity TwoWindowSquareHosts

noncomputable section

/-- Natural subtraction records only the positive part of the correction. -/
def macroscopicValueExcess (M L : ℕ) (δ : ℝ) : ℕ :=
  macroscopicValueMassNat M L δ - 4 * macroscopicStartMassNat M L δ

/-- The excess is bounded by three times the unrestricted host count. -/
theorem macroscopicValueExcess_le_three_hosts
    {M L : ℕ} {δ : ℝ} (hM : 2 ≤ M) (hδ : 0 < δ) :
    macroscopicValueExcess M L δ ≤
      3 * (squareProductHosts L (separatedPairs (macroscopicStarts M δ) L)).card := by
  have hfinite := macroscopicValueMassNat_le_four_start_add_hosts (L := L) hM hδ
  unfold macroscopicValueExcess
  omega

/-- The real representation is a positive part, rather than an absolute difference. -/
theorem macroscopicValueExcess_cast_eq_max (M L : ℕ) (δ : ℝ) :
    (macroscopicValueExcess M L δ : ℝ) =
      max 0 ((macroscopicValueMassNat M L δ : ℝ) -
        4 * (macroscopicStartMassNat M L δ : ℝ)) := by
  rcases le_total (4 * macroscopicStartMassNat M L δ)
      (macroscopicValueMassNat M L δ) with h | h
  · have hreal : 4 * (macroscopicStartMassNat M L δ : ℝ) ≤
        (macroscopicValueMassNat M L δ : ℝ) := by exact_mod_cast h
    rw [macroscopicValueExcess, Nat.cast_sub h, Nat.cast_mul, Nat.cast_ofNat,
      max_eq_right (sub_nonneg.mpr hreal)]
  · have hreal : (macroscopicValueMassNat M L δ : ℝ) ≤
        4 * (macroscopicStartMassNat M L δ : ℝ) := by exact_mod_cast h
    rw [macroscopicValueExcess, Nat.sub_eq_zero_of_le h, Nat.cast_zero,
      max_eq_left (sub_nonpos.mpr hreal)]

/-- Uniform `M^(3/2+o(1))` control of the natural positive excess.
The threshold is chosen before both the window length and the exponent `δ`. -/
theorem macroscopicValueExcess_uniformThreeHalves
    (C : ℝ) (hC : 0 ≤ C) :
    ∀ k : ℕ, 0 < k → ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ L : ℕ,
      ((L + 1 : ℕ) : ℝ) ≤ C * Real.log M → ∀ δ : ℝ, 0 < δ →
      (macroscopicValueExcess M L δ : ℝ) ^ (2 * k) ≤
        (M : ℝ) ^ (3 * k + 1) := by
  intro k hk
  obtain ⟨Mcore, hcore⟩ :=
    FullIntervalHostAsymptotics.proposition_three_seven_full_hosts C hC
      (2 * k) (by omega)
  refine ⟨max Mcore (max 2 (3 ^ (4 * k))), ?_⟩
  intro M hM L hlog δ hδ
  have hMcore : Mcore ≤ M := (le_max_left _ _).trans hM
  have hMrest : max 2 (3 ^ (4 * k)) ≤ M := (le_max_right _ _).trans hM
  have hMtwo : 2 ≤ M := (le_max_left _ _).trans hMrest
  have hthree : (3 : ℝ) ^ (4 * k) ≤ (M : ℝ) := by
    exact_mod_cast (le_max_right 2 (3 ^ (4 * k))).trans hMrest
  have hhosts :
      ((squareProductHosts L (separatedPairs (macroscopicStarts M δ) L)).card : ℝ) ^
        (4 * k) ≤ (M : ℝ) ^ (6 * k + 1) := by
    simpa only [show 2 * (2 * k) = 4 * k by omega,
      show 3 * (2 * k) + 1 = 6 * k + 1 by omega] using
      hcore M hMcore L hlog δ hδ
  have hfinite : (macroscopicValueExcess M L δ : ℝ) ≤
      3 * ((squareProductHosts L
        (separatedPairs (macroscopicStarts M δ) L)).card : ℝ) := by
    exact_mod_cast macroscopicValueExcess_le_three_hosts (L := L) hMtwo hδ
  have hscaled : (macroscopicValueExcess M L δ : ℝ) ^ (4 * k) ≤
      (M : ℝ) ^ (6 * k + 2) := by
    calc
      _ ≤ (3 * ((squareProductHosts L
          (separatedPairs (macroscopicStarts M δ) L)).card : ℝ)) ^ (4 * k) :=
        pow_le_pow_left₀ (by positivity) hfinite _
      _ = (3 : ℝ) ^ (4 * k) *
          ((squareProductHosts L
            (separatedPairs (macroscopicStarts M δ) L)).card : ℝ) ^ (4 * k) :=
        mul_pow _ _ _
      _ ≤ (3 : ℝ) ^ (4 * k) * (M : ℝ) ^ (6 * k + 1) :=
        mul_le_mul_of_nonneg_left hhosts (by positivity)
      _ ≤ (M : ℝ) * (M : ℝ) ^ (6 * k + 1) :=
        mul_le_mul_of_nonneg_right hthree (by positivity)
      _ = (M : ℝ) ^ (6 * k + 2) := by rw [← pow_succ']
  have hsquare : ((macroscopicValueExcess M L δ : ℝ) ^ (2 * k)) ^ 2 ≤
      ((M : ℝ) ^ (3 * k + 1)) ^ 2 := by
    simpa only [← pow_mul, show (2 * k) * 2 = 4 * k by omega,
      show (3 * k + 1) * 2 = 6 * k + 2 by omega] using hscaled
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsquare

/-- Unconditional real positive-part correction underlying the passage to values. -/
theorem prescribed_value_correction_uniform
    (C : ℝ) (hC : 0 ≤ C) :
    ∀ k : ℕ, 0 < k → ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ L : ℕ,
      ((L + 1 : ℕ) : ℝ) ≤ C * Real.log M → ∀ δ : ℝ, 0 < δ →
      (max 0 ((macroscopicValueMassNat M L δ : ℝ) -
        4 * (macroscopicStartMassNat M L δ : ℝ))) ^ (2 * k) ≤
        (M : ℝ) ^ (3 * k + 1) := by
  simpa only [← macroscopicValueExcess_cast_eq_max] using
    macroscopicValueExcess_uniformThreeHalves C hC

end
end PaperC.V282.MacroscopicValueCorrection
