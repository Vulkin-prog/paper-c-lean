import PaperC.Arithmetic.SquarefreeSmoothCount
import PaperC.Arithmetic.ChebyshevPrimeCount
import PaperC.Arithmetic.PrimeCountBridge
import PaperCV282.MacroscopicShallowSigma

/-!
# Uniform counts of squarefree smooth coefficients

The cardinality is bounded by the number of subsets of the small primes.
The elementary Chebyshev inequality suffices for subpolynomiality on a
fixed positive logarithmic band, uniformly in every coefficient cutoff.
-/

namespace PaperC.V282.MacroscopicSmoothKernels

open MacroscopicShallowSigma

noncomputable section

/-- A fixed lower bound on the binary logarithm controls the small-prime count. -/
theorem primeCount_le_fraction_of_pow_le {B T : ℕ}
    (hB : 4 ≤ B) (hT : 0 < T) (hpower : 2 ^ T ≤ B) :
    (PrimesUpTo.count B : ℝ) ≤ (7 / (T : ℝ)) * B := by
  have hlog : T ≤ Nat.log 2 B := Nat.le_log_of_pow_le (by omega) hpower
  have hcount := ChebyshevPrimeCount.log_mul_count_le_seven_mul hB
  have hscaled : T * PrimesUpTo.count B ≤ 7 * B :=
    (Nat.mul_le_mul_right _ hlog).trans hcount
  have hreal : (T : ℝ) * (PrimesUpTo.count B : ℝ) ≤ 7 * (B : ℝ) := by exact_mod_cast hscaled
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hdiv : (PrimesUpTo.count B : ℝ) ≤ 7 * (B : ℝ) / T := (le_div_iff₀ hTpos).mpr (by nlinarith)
  exact hdiv.trans_eq (by ring)

/-- Small-prime counts are little-oh of the word length on any positive lower band. -/
theorem primeCount_le_epsilon_length_eventually
    (betaMin eta : ℝ) (hbetaMin : 0 < betaMin) (heta : 0 < eta) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (PrimesUpTo.count (L + 1) : ℝ) ≤ eta * (L + 1 : ℝ) := by
  obtain ⟨T : ℕ, hT⟩ := exists_nat_gt (7 / eta)
  have hTpos : (0 : ℝ) < T := (by positivity : (0 : ℝ) < 7 / eta).trans hT
  have hTnat : 0 < T := by exact_mod_cast hTpos
  obtain ⟨Mzero, hMzero⟩ := length_ge_eventually_of_logarithmic_lower
    betaMin hbetaMin ((max 4 (2 ^ T) : ℕ) : ℝ)
  refine ⟨Mzero, ?_⟩
  intro M hM L hlower
  have hB : max 4 (2 ^ T) ≤ L + 1 := by exact_mod_cast hMzero M hM L (by simpa using hlower)
  have hcount := primeCount_le_fraction_of_pow_le
    (by omega : 4 ≤ L + 1) hTnat (by omega : 2 ^ T ≤ L + 1)
  have hfrac : 7 / (T : ℝ) ≤ eta := by
    apply (div_le_iff₀ hTpos).mpr
    have h := (div_lt_iff₀ heta).mp hT
    linarith
  have hcount' : (PrimesUpTo.count (L + 1) : ℝ) ≤ (7 / (T : ℝ)) * (L + 1 : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hcount
  exact hcount'.trans (mul_le_mul_of_nonneg_right hfrac (by positivity : (0 : ℝ) ≤ L + 1))

/-- The full small-prime squareclass space has a subpolynomial cardinality. -/
theorem two_pow_primeCount_le_rpow_eventually
    (betaMin betaMax epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbetaMax : 0 < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M →
      (2 : ℝ) ^ PrimesUpTo.count (L + 1) ≤ (M : ℝ) ^ epsilon := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let eta : ℝ := epsilon / (betaMax * Real.log 2)
  have heta : 0 < eta := by dsimp [eta]; positivity
  obtain ⟨Mcount, hcount⟩ := primeCount_le_epsilon_length_eventually betaMin eta hbetaMin heta
  refine ⟨max Mcount 1, ?_⟩
  intro M hM L hlower hupper
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hc := hcount M ((le_max_left _ _).trans hM) L hlower
  have hexp : (PrimesUpTo.count (L + 1) : ℝ) * Real.log 2 ≤ epsilon * Real.log M := by
    calc
      _ ≤ (eta * (L + 1 : ℝ)) * Real.log 2 := mul_le_mul_of_nonneg_right hc hlogTwo.le
      _ ≤ (eta * (betaMax * Real.log M)) * Real.log 2 := by gcongr
      _ = _ := by dsimp [eta]; field_simp
  calc
    _ = Real.exp ((PrimesUpTo.count (L + 1) : ℝ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ Real.exp (epsilon * Real.log M) := Real.exp_le_exp.mpr hexp
    _ = _ := by rw [Real.rpow_def_of_pos hMpos]; congr 1; ring

/-- All squarefree smooth coefficients, uniformly before the chosen height cutoff. -/
theorem card_squarefreeSmoothUpTo_le_rpow_eventually
    (betaMin betaMax epsilon : ℝ) (hbetaMin : 0 < betaMin)
    (hbetaMax : 0 < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ (L + 1 : ℝ) →
      (L + 1 : ℝ) ≤ betaMax * Real.log M → ∀ X : ℕ,
      ((SquarefreeSmoothCount.squarefreeSmoothUpTo (L + 1) X).card : ℝ) ≤ (M : ℝ) ^ epsilon := by
  obtain ⟨Mzero, hMzero⟩ := two_pow_primeCount_le_rpow_eventually
    betaMin betaMax epsilon hbetaMin hbetaMax hepsilon
  refine ⟨Mzero, ?_⟩
  intro M hM L hlower hupper X
  have hfinite := SquarefreeSmoothCount.card_squarefreeSmoothUpTo_le_two_pow (L + 1) X
  rw [← PrimeCountBridge.count_eq_card_smallPrimesUpTo] at hfinite
  have hreal : ((SquarefreeSmoothCount.squarefreeSmoothUpTo (L + 1) X).card : ℝ) ≤
      (2 : ℝ) ^ PrimesUpTo.count (L + 1) := by exact_mod_cast hfinite
  exact hreal.trans (hMzero M hM L hlower hupper)

end
end PaperC.V282.MacroscopicSmoothKernels
