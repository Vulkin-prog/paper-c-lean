import PaperCV282.PreciseSingletonEuler

/-!
# The printed sharp rate for singleton hosts

The threshold is uniform in the interval's lower endpoint and the channel
height exponent. In particular no bounded ratio between the endpoints is
assumed. The coefficient depends only on the fixed lower logarithmic band.
-/

namespace PaperC.V282.PreciseSingletonHosts

open PreciseSingletonEuler SizeTwoHostAsymptotics BoundedRatioTwoSingletonCritical
open BoundedRatioTwoSingletonHosts BoundedRatioComponentHosts

noncomputable section

/-- An explicit constant for the source-shaped sharp envelope. -/
def singletonConstant (betaMin : ℝ) : ℝ := 18 * (2 + 1 / betaMin) + 681

theorem singletonConstant_pos {betaMin : ℝ} (hmin : 0 < betaMin) :
    0 < singletonConstant betaMin := by unfold singletonConstant; positivity

/-- Uniform absorption of the complete finite harmonic/Euler expression. -/
theorem raw_bound_eventually (betaMin betaMax : ℝ)
    (hmin : 0 < betaMin) (hmax : 0 ≤ betaMax) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M →
      16 ≤ L + 1 ∧
      9 * (L + 1 : ℝ) ^ 4 * (M + L : ℝ) * (1 + Real.log (M + L : ℝ)) *
          Real.exp (twoSingletonPrimeExponent (L + 1)) ≤
        (M : ℝ) * Real.exp (singletonConstant betaMin *
          (Real.sqrt (L + 1 : ℝ) / Real.log (L + 1 : ℝ))) := by
  obtain ⟨Mzero, hall⟩ := sharp_band_eventually betaMin betaMax hmin hmax
  refine ⟨Mzero, ?_⟩
  intro M hM L hlo hhi
  obtain ⟨hMtwo, hLM, hB, he, hl, hr⟩ := hall M hM L hlo hhi
  have hcut : (M + L : ℝ) ≤ 2 * M := by exact_mod_cast (show M + L ≤ 2 * M by omega)
  have hlog := cutoff_log_le_length_factor hMtwo hLM hmin hlo
  have hf := polynomial_euler_le_sharp
    (P := 18 * (2 + 1 / betaMin)) (by positivity) hB he
    (by simpa only [Nat.cast_add, Nat.cast_one] using hl) hr
  refine ⟨hB, ?_⟩
  calc
    _ ≤ 9 * (L + 1 : ℝ) ^ 4 * (2 * M) *
        ((2 + 1 / betaMin) * (L + 1 : ℝ)) *
          Real.exp (twoSingletonPrimeExponent (L + 1)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hlognonneg : 0 ≤ Real.log (M + L : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ M + L by omega))
      exact mul_le_mul (mul_le_mul_of_nonneg_left hcut (by positivity)) hlog
        (by linarith) (by positivity)
    _ = (18 * (2 + 1 / betaMin) * ((L + 1 : ℕ) : ℝ) ^ 5 *
          Real.exp (twoSingletonPrimeExponent (L + 1))) * M := by push_cast; ring
    _ ≤ Real.exp ((18 * (2 + 1 / betaMin) + 681) *
        twoSingletonCriticalRatio (L + 1)) * M :=
      mul_le_mul_of_nonneg_right hf (by positivity)
    _ = _ := by simp only [singletonConstant, twoSingletonCriticalRatio, Nat.cast_add,
      Nat.cast_one]; ring

/-- The sharp size-two clause of article Lemma 3.18, with actual component hosts. -/
theorem lemma_three_eighteen_size_two (betaMin betaMax : ℝ)
    (hmin : 0 < betaMin) (hmax : 0 ≤ betaMax) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M → ∀ N A : ℕ, 2 ≤ N →
      ((boundedComponentHosts N M A L 2).card : ℝ) ≤
        (M : ℝ) * Real.exp (singletonConstant betaMin *
          (Real.sqrt (L + 1 : ℝ) / Real.log (L + 1 : ℝ))) := by
  obtain ⟨Mzero, hraw⟩ := raw_bound_eventually betaMin betaMax hmin hmax
  refine ⟨Mzero, ?_⟩
  intro M hM L hlo hhi N A hN
  obtain ⟨hB, hbound⟩ := hraw M hM L hlo hhi
  exact (hostCount_le_prime_exponent hN hB).trans hbound

/-- The same sharp bound controls the explicit summed singleton parameters. -/
theorem parameterCount_le_sharp_eventually (betaMin betaMax : ℝ)
    (hmin : 0 < betaMin) (hmax : 0 ≤ betaMax) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M → ∀ K : ℕ,
      (twoSingletonParameterCount M L K : ℝ) ≤
        (M : ℝ) * Real.exp (singletonConstant betaMin *
          (Real.sqrt (L + 1 : ℝ) / Real.log (L + 1 : ℝ))) := by
  obtain ⟨Mzero, hraw⟩ := raw_bound_eventually betaMin betaMax hmin hmax
  refine ⟨Mzero, ?_⟩
  intro M hM L hlo hhi K
  obtain ⟨hB, hbound⟩ := hraw M hM L hlo hhi
  have hfactor : (1 : ℝ) ≤ 9 * (L + 1 : ℝ) ^ 4 := by
    have hone : (1 : ℝ) ≤ L + 1 := by have : (0 : ℝ) ≤ L := Nat.cast_nonneg L; linarith
    have hh := one_le_pow₀ hone (n := 4)
    linarith
  have hlog : 0 ≤ 1 + Real.log (M + L : ℝ) := by
    have hL : (1 : ℝ) ≤ M + L := by exact_mod_cast (show 1 ≤ M + L by omega)
    have := Real.log_nonneg hL
    linarith
  calc
    _ ≤ (M + L : ℝ) * (1 + Real.log (M + L : ℝ)) *
        Real.exp (twoSingletonPrimeExponent (L + 1)) := parameterCount_le_prime_exponent K hB
    _ ≤ (9 * (L + 1 : ℝ) ^ 4) * ((M + L : ℝ) * (1 + Real.log (M + L : ℝ)) *
        Real.exp (twoSingletonPrimeExponent (L + 1))) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hfactor
        (mul_nonneg (mul_nonneg (by positivity) hlog) (by positivity))
    _ ≤ _ := by simpa only [mul_assoc] using hbound

end
end PaperC.V282.PreciseSingletonHosts
