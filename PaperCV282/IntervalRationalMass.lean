import PaperC.Asymptotics.PropositionSixteenOneCore

/-!
# Finite systematic mass on arbitrary intervals

The historical rational-channel mass on `[N, M)` has a volumetric
height-two contribution and a height-at-least-three contribution. The
bounds below retain their distinct powers `2^(L/2)` and `2^(L/3)` without
assuming a fixed endpoint ratio or a critical logarithmic window.
-/

namespace PaperC.V282.IntervalRationalMass

open BoundedRatioGeometry PropositionSixteenOne

/-- The elementary interval-width factor is at most the upper endpoint. -/
theorem one_add_width_div_le {N M d : ℕ} (hM : 1 ≤ M) (hd : 2 ≤ d) :
    1 + (M - N) / d ≤ M := by
  have hdiv : (M - N) / d ≤ M / d :=
    Nat.div_le_div_right (Nat.sub_le M N)
  have hlt : M / d < M := Nat.div_lt_self (by omega) (by omega)
  omega

/-- A finite two-term bound for the base-two rational-channel mass. -/
theorem boundedRationalMass_le_interval_profile
    {N M A L : ℕ} (hM : 1 ≤ M) (hNM : N ≤ M) (hA : 1 ≤ A) :
    boundedRationalMass N M A L 2 ≤
      6 * M * (L + 1) * 2 ^ (L / 2) +
        4 * M * (L + 1) ^ 4 * 2 ^ (L / 3) := by
  have hwidthTwo : 1 + (M - N) / 2 ≤ M :=
    one_add_width_div_le hM (by omega)
  have hwidthThree : 1 + (M - N) / 3 ≤ M :=
    one_add_width_div_le hM (by omega)
  have htwo : 2 * ((3 * L + 1) * (1 + (M - N) / 2)) ≤
      6 * M * (L + 1) := by
    calc
      _ ≤ 2 * ((3 * (L + 1)) * M) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul (by omega) hwidthTwo)
      _ = 6 * M * (L + 1) := by ring
  have hL : L ≤ L + 1 := by omega
  have hquad : (2 * L) * L + 1 ≤ 2 * (L + 1) ^ 2 := by nlinarith
  have hthree : L * (2 * L) * ((2 * L) * L + 1) *
      (1 + (M - N) / 3) ≤ 4 * M * (L + 1) ^ 4 := by
    calc
      _ ≤ (L + 1) * (2 * (L + 1)) * (2 * (L + 1) ^ 2) * M :=
        Nat.mul_le_mul
          (Nat.mul_le_mul (Nat.mul_le_mul hL (Nat.mul_le_mul_left 2 hL)) hquad)
          hwidthThree
      _ = 4 * M * (L + 1) ^ 4 := by ring
  exact (boundedRationalMass_le N M A L 2 hNM hA (by omega)).trans
    (Nat.add_le_add (Nat.mul_le_mul_right _ htwo) (Nat.mul_le_mul_right _ hthree))

/-- The same estimate applies to the actual finite systematic mass. -/
theorem systematicMassNat_le_interval_profile
    {N M A L : ℕ} (hM : 1 ≤ M) (hNM : N ≤ M) (hA : 1 ≤ A) :
    systematicMassNat (N := N) (M := M) (L := L) A ≤
      6 * M * (L + 1) * 2 ^ (L / 2) +
        4 * M * (L + 1) ^ 4 * 2 ^ (L / 3) := by
  rw [systematicMassNat_eq_boundedRationalMass]
  exact boundedRationalMass_le_interval_profile hM hNM hA

/-- Real systematic mass has the same two-term interval bound. For `N < 2`,
the historical real definition is zero, so no extra lower-endpoint
hypothesis is necessary for this upper bound. -/
theorem systematicMass_le_interval_profile
    {N M A L : ℕ} (hM : 1 ≤ M) (hNM : N ≤ M) (hA : 1 ≤ A) :
    systematicMass A N M L ≤
      6 * (M : ℝ) * (L + 1) * (2 : ℝ) ^ (L / 2) +
        4 * (M : ℝ) * (L + 1) ^ 4 * (2 : ℝ) ^ (L / 3) := by
  by_cases hN : 2 ≤ N
  · simp only [systematicMass, dif_pos hN]
    exact_mod_cast systematicMassNat_le_interval_profile (L := L) hM hNM hA
  · simp only [systematicMass, dif_neg hN]
    positivity

/-- A common polynomial envelope, retaining both exponential contributions. -/
theorem systematicMass_le_common_polynomial
    {N M A L : ℕ} (hM : 1 ≤ M) (hNM : N ≤ M) (hA : 1 ≤ A) :
    systematicMass A N M L ≤
      6 * (M : ℝ) * (L + 1) ^ 4 *
        ((2 : ℝ) ^ (L / 2) + (2 : ℝ) ^ (L / 3)) := by
  have hL : (L : ℝ) + 1 ≤ ((L : ℝ) + 1) ^ 4 :=
    le_self_pow₀ (by exact_mod_cast (show 1 ≤ L + 1 by omega)) (by norm_num)
  have htwo : 6 * (M : ℝ) * (L + 1) * (2 : ℝ) ^ (L / 2) ≤
      6 * (M : ℝ) * (L + 1) ^ 4 * (2 : ℝ) ^ (L / 2) := by
    gcongr
  have hthree : 4 * (M : ℝ) * (L + 1) ^ 4 * (2 : ℝ) ^ (L / 3) ≤
      6 * (M : ℝ) * (L + 1) ^ 4 * (2 : ℝ) ^ (L / 3) := by
    gcongr
    norm_num
  calc
    _ ≤ 6 * (M : ℝ) * (L + 1) * (2 : ℝ) ^ (L / 2) +
        4 * (M : ℝ) * (L + 1) ^ 4 * (2 : ℝ) ^ (L / 3) :=
      systematicMass_le_interval_profile hM hNM hA
    _ ≤ 6 * (M : ℝ) * (L + 1) ^ 4 * (2 : ℝ) ^ (L / 2) +
        6 * (M : ℝ) * (L + 1) ^ 4 * (2 : ℝ) ^ (L / 3) :=
      add_le_add htwo hthree
    _ = _ := by ring

end PaperC.V282.IntervalRationalMass
