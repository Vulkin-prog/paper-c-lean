import PaperCV282.SizeTwoHostAsymptotics
import PaperCV282.MacroscopicAlignedRunge
import PaperC.Asymptotics.BoundedRatioTwoSingletonCritical

/-!
# The sharp singleton Euler factor on every macroscopic logarithmic band

The elementary prime-sensitive estimate supplies exp(O(sqrt B / log B)).
This module retains that rate instead of weakening it to M^epsilon.
No prime number theorem or additional literature argument is needed.
-/

namespace PaperC.V282.PreciseSingletonEuler

open BoundedRatioTwoSingletonCritical BoundedRatioTwoSingletonHosts
open PropositionSixteenOne BoundedRatioComponentHosts SizeTwoHostAsymptotics MacroscopicAlignedRunge

noncomputable section

/-- A general polynomial coefficient is absorbed by the genuine sharp scale. -/
theorem polynomial_euler_le_sharp
    {P : ℝ} (hP : 0 ≤ P) {B : ℕ} (hB : 16 ≤ B)
    (he : twoSingletonPrimeExponent B ≤ 676 * twoSingletonCriticalRatio B)
    (hl : Real.log B ≤ twoSingletonCriticalRatio B)
    (hr : 1 ≤ twoSingletonCriticalRatio B) :
    P * (B : ℝ) ^ 5 * Real.exp (twoSingletonPrimeExponent B) ≤
      Real.exp ((P + 681) * twoSingletonCriticalRatio B) := by
  let R := twoSingletonCriticalRatio B
  have hPe : P ≤ Real.exp (P * R) := by
    calc
      P ≤ P + 1 := by linarith
      _ ≤ Real.exp P := Real.add_one_le_exp P
      _ ≤ Real.exp (P * R) := Real.exp_le_exp.mpr (by
        simpa [R] using mul_le_mul_of_nonneg_left hr hP)
  have hBe : (B : ℝ) ≤ Real.exp R := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < B)]
    exact Real.exp_le_exp.mpr hl
  have hpow : (B : ℝ) ^ 5 ≤ Real.exp (5 * R) := by
    calc
      _ ≤ (Real.exp R) ^ 5 := pow_le_pow_left₀ (by positivity) hBe 5
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  calc
    _ ≤ (Real.exp (P * R) * Real.exp (5 * R)) * Real.exp (676 * R) :=
      mul_le_mul (mul_le_mul hPe hpow (by positivity) (by positivity))
        (Real.exp_le_exp.mpr he) (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; dsimp [R]; ring

/-- The exact finite parameter count keeps the prime-sensitive Euler exponent. -/
theorem parameterCount_le_prime_exponent {M L : ℕ} (K : ℕ) (hB : 16 ≤ L + 1) :
    (twoSingletonParameterCount M L K : ℝ) ≤
      (M + L : ℝ) * (1 + Real.log (M + L : ℝ)) *
        Real.exp (twoSingletonPrimeExponent (L + 1)) := by
  simpa only [boundedRatioCutoff, twoSingletonPrimeExponent, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] using
    twoSingletonParameterCount_cast_le_primeSensitive (M := M) (K := K) hB

/-- The finite size-two host count, before any asymptotic absorption. -/
theorem hostCount_le_prime_exponent {N M A L : ℕ} (hN : 2 ≤ N) (hB : 16 ≤ L + 1) :
    ((boundedComponentHosts N M A L 2).card : ℝ) ≤
      9 * (L + 1 : ℝ) ^ 4 * (M + L : ℝ) *
        (1 + Real.log (M + L : ℝ)) *
          Real.exp (twoSingletonPrimeExponent (L + 1)) := by
  have h := card_boundedComponentHosts_two_cast_le_primeSensitive
    (M := M) (A := A) hN hB
  convert h using 1
  simp only [boundedRatioCutoff, twoSingletonPrimeExponent, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, Nat.cast_pow]
  ring

/-- A uniform threshold supplies the exact band and all sharp Euler absorptions. -/
theorem sharp_band_eventually (betaMin betaMax : ℝ)
    (hmin : 0 < betaMin) (hmax : 0 ≤ betaMax) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M →
      2 ≤ M ∧ L ≤ M ∧ 16 ≤ L + 1 ∧
      twoSingletonPrimeExponent (L + 1) ≤ 676 * twoSingletonCriticalRatio (L + 1) ∧
      Real.log (L + 1 : ℝ) ≤ twoSingletonCriticalRatio (L + 1) ∧
      1 ≤ twoSingletonCriticalRatio (L + 1) := by
  obtain ⟨Bzero, hsharp⟩ := twoSingletonPrimeExponent_le_criticalRatio_eventually
  obtain ⟨Mheight, hheight⟩ := height_ge_eventually betaMin hmin Bzero
  obtain ⟨Mlength, hlength⟩ := MacroscopicCanonicalCode.logarithmic_power_lt_rpow_eventually
    betaMax 1 hmax (by norm_num) 1 (by omega)
  refine ⟨max 2 (max Mheight Mlength), ?_⟩
  intro M hM L hlo hhi
  have htail := (le_max_right 2 (max Mheight Mlength)).trans hM
  have hBL := hheight M ((le_max_left _ _).trans htail) (L + 1) (by simpa using hlo)
  have hML := hlength M ((le_max_right _ _).trans htail) (L + 1) (by simpa using hhi)
  have hLM : L ≤ M := by
    simp only [pow_one, Real.rpow_one, Nat.cast_add, Nat.cast_one] at hML
    have : (L : ℝ) ≤ M := by linarith
    exact_mod_cast this
  exact ⟨(le_max_left _ _).trans hM, hLM, by simpa only [Nat.cast_add, Nat.cast_one] using hsharp (L + 1) hBL⟩

end
end PaperC.V282.PreciseSingletonEuler
