import PaperCV282.MacroscopicShallowSigma
import PaperC.Combinatorics.SmallHeightResidualComponentEnvelope
import PaperC.Arithmetic.ChebyshevPrimeCount

/-!
# Residual components of positive small canonical channels

The finite prime-support bound is independent of the ambient interval.
Chebyshev's estimate makes its component envelope uniformly little-oh of
the length on any positive logarithmic band. The final binary weight is
therefore uniformly subpolynomial without a critical-window hypothesis.
-/

namespace PaperC.V282.MacroscopicSmallHeightComponents

open Affine.CanonicalRationalCode RationalMassFinite ResidualComponentCounts
open SmallHeightResidualComponentEnvelope SmallHeightResidualPrimeSupport
open MacroscopicShallowSigma

noncomputable section

/-- The genuine positive small-height test gives the finite component envelope. -/
theorem canonicalResidualComponentCount_le_envelope
    {A L x y : ℕ} (hB : 8 ≤ L + 1) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hsmall : hasSmallPositiveCanonicalHeight A L x y) :
    canonicalResidualComponentCount A x y L ≤ smallHeightResidualComponentEnvelope L := by
  obtain ⟨c, hchoice, _⟩ := exists_canonical_candidate_of_two_le_multiplicity
    (two_le_canonicalMultiplicity_of_sigma_pos hsmall.1)
  have hqReal : (Nat.max c.1.1 c.1.2 : ℝ) ≤
      Real.sqrt (Real.log ((L + 1 : ℕ) : ℝ)) := by
    simpa only [canonicalPairHeight_eq_of_choice hchoice] using hsmall.2
  have hqNat := height_le_natSqrt_natLog_of_le_realSqrt_realLog hB hqReal
  have hcomponent := canonicalResidualComponentCount_le_two_add_primeCount_of_choice
    hx hy c hchoice
  have hcutoff : 4 * Nat.max c.1.1 c.1.2 * (L + 1) ≤ smallHeightPrimeCutoff L :=
    Nat.mul_le_mul_right (L + 1) (Nat.mul_le_mul_left 4 hqNat)
  exact hcomponent.trans (Nat.add_le_add_left (primeCount_mono hcutoff) 2)

/-- Elementary prime-count control, before choosing an ambient scale. -/
theorem sqrtLog_mul_primeCount_le (L : ℕ)
    (hqpos : 0 < Nat.sqrt (Nat.log 2 (L + 1))) :
    Nat.sqrt (Nat.log 2 (L + 1)) * PrimesUpTo.count (smallHeightPrimeCutoff L) ≤
      28 * (L + 1) := by
  let B := L + 1
  let q := Nat.sqrt (Nat.log 2 B)
  let X := smallHeightPrimeCutoff L
  have hqOne : 1 ≤ q := by dsimp [q, B]; omega
  have hX : X = 4 * q * B := rfl
  have hBOne : 1 ≤ B := by dsimp [B]; omega
  have hXfour : 4 ≤ X := by
    rw [hX]
    have hfirst : 4 ≤ 4 * q := by simpa using Nat.mul_le_mul_left 4 hqOne
    have hsecond : 4 * q ≤ 4 * q * B := by simpa using Nat.mul_le_mul_left (4 * q) hBOne
    exact hfirst.trans hsecond
  have hBLeX : B ≤ X := by
    rw [hX]
    have hOne : 1 ≤ 4 * q := by omega
    simpa using Nat.mul_le_mul_right B hOne
  have hlogMono : Nat.log 2 B ≤ Nat.log 2 X := Nat.log_mono_right hBLeX
  have hqSquare : q * q ≤ Nat.log 2 B := by simpa [q] using Nat.sqrt_le (Nat.log 2 B)
  have hchebyshev : Nat.log 2 X * PrimesUpTo.count X ≤ 7 * X :=
    ChebyshevPrimeCount.log_mul_count_le_seven_mul hXfour
  have hwithFactor : q * (q * PrimesUpTo.count X) ≤ q * (28 * B) := by
    calc
      _ = (q * q) * PrimesUpTo.count X := by ring
      _ ≤ Nat.log 2 B * PrimesUpTo.count X := Nat.mul_le_mul_right _ hqSquare
      _ ≤ Nat.log 2 X * PrimesUpTo.count X := Nat.mul_le_mul_right _ hlogMono
      _ ≤ 7 * X := hchebyshev
      _ = q * (28 * B) := by rw [hX]; ring
  exact Nat.le_of_mul_le_mul_left hwithFactor hqpos

/-- A concrete power threshold forces the integral square-root logarithm. -/
theorem le_sqrtLog_of_pow_sq_le {T B : ℕ} (hB : 2 ^ (T ^ 2) ≤ B) :
    T ≤ Nat.sqrt (Nat.log 2 B) := by
  apply (Nat.le_sqrt').2
  exact Nat.le_log_of_pow_le (by omega) hB

/-- The small-height component envelope is little-oh of the full length,
uniformly under a positive logarithmic lower bound. -/
theorem componentEnvelope_le_epsilon_length_eventually
    (betaMin : ℝ) (hbetaMin : 0 < betaMin) (eta : ℝ) (heta : 0 < eta) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ ((L + 1 : ℕ) : ℝ) →
      (smallHeightResidualComponentEnvelope L : ℝ) ≤ eta * ((L + 1 : ℕ) : ℝ) := by
  obtain ⟨T : ℕ, hT⟩ := exists_nat_gt (56 / eta)
  obtain ⟨K : ℕ, hK⟩ := exists_nat_gt (4 / eta)
  have hTposReal : (0 : ℝ) < T := (by positivity : (0 : ℝ) < 56 / eta).trans hT
  have hTpos : 0 < T := by exact_mod_cast hTposReal
  obtain ⟨Mzero, hMzero⟩ := length_ge_eventually_of_logarithmic_lower
    betaMin hbetaMin ((max (2 ^ (T ^ 2)) K : ℕ) : ℝ)
  refine ⟨Mzero, ?_⟩
  intro M hM L hL
  have hheight : max (2 ^ (T ^ 2)) K ≤ L + 1 := by
    exact_mod_cast hMzero M hM L hL
  have hpower : 2 ^ (T ^ 2) ≤ L + 1 := (le_max_left _ _).trans hheight
  have hKheight : K ≤ L + 1 := (le_max_right _ _).trans hheight
  have hTq := le_sqrtLog_of_pow_sq_le hpower
  have hqpos : 0 < Nat.sqrt (Nat.log 2 (L + 1)) := hTpos.trans_le hTq
  have hprime := sqrtLog_mul_primeCount_le L hqpos
  have hTprime : T * PrimesUpTo.count (smallHeightPrimeCutoff L) ≤ 28 * (L + 1) :=
    (Nat.mul_le_mul_right _ hTq).trans hprime
  have hTprimeReal : (T : ℝ) * (PrimesUpTo.count (smallHeightPrimeCutoff L) : ℝ) ≤
      28 * ((L + 1 : ℕ) : ℝ) := by exact_mod_cast hTprime
  have hprimeReal : (PrimesUpTo.count (smallHeightPrimeCutoff L) : ℝ) ≤
      (28 / (T : ℝ)) * ((L + 1 : ℕ) : ℝ) := by
    calc
      _ ≤ (28 * ((L + 1 : ℕ) : ℝ)) / T := by
        apply (le_div_iff₀ hTposReal).2
        simpa only [mul_comm] using hTprimeReal
      _ = _ := by ring
  have hratio : 28 / (T : ℝ) < eta / 2 := by
    apply (div_lt_iff₀ hTposReal).2
    have hscaled := (div_lt_iff₀ heta).mp hT
    nlinarith
  have hprimeHalf : (PrimesUpTo.count (smallHeightPrimeCutoff L) : ℝ) ≤
      (eta / 2) * ((L + 1 : ℕ) : ℝ) :=
    hprimeReal.trans (mul_le_mul_of_nonneg_right hratio.le (by positivity))
  have hKcast : (K : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by exact_mod_cast hKheight
  have hconstantHalf : (2 : ℝ) ≤ (eta / 2) * ((L + 1 : ℕ) : ℝ) := by
    have hscaled := (div_lt_iff₀ heta).mp (hK.trans_le hKcast)
    nlinarith only [hscaled]
  unfold smallHeightResidualComponentEnvelope
  push_cast
  have h := add_le_add hconstantHalf hprimeHalf
  push_cast at h
  nlinarith only [h]

/-- Conversion of a natural binary exponent from its logarithmic bound. -/
theorem two_pow_le_rpow_of_log_bound {M n : ℕ} {epsilon : ℝ}
    (hM : 0 < M) (hlog : (n : ℝ) * Real.log 2 ≤ epsilon * Real.log M) :
    (2 : ℝ) ^ n ≤ (M : ℝ) ^ epsilon := by
  calc
    (2 : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ Real.exp (epsilon * Real.log M) := Real.exp_le_exp.mpr hlog
    _ = (M : ℝ) ^ epsilon := by
      rw [Real.rpow_def_of_pos (by exact_mod_cast hM : (0 : ℝ) < M)]
      congr 1
      ring

/-- The common component envelope has uniformly subpolynomial binary weight
on a full logarithmic band. -/
theorem two_pow_componentEnvelope_le_rpow_eventually
    (betaMin betaMax : ℝ) (hbetaMin : 0 < betaMin) (hbetaMax : 0 < betaMax)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ ((L + 1 : ℕ) : ℝ) →
      ((L + 1 : ℕ) : ℝ) ≤ betaMax * Real.log M →
      (2 : ℝ) ^ smallHeightResidualComponentEnvelope L ≤ (M : ℝ) ^ epsilon := by
  let eta : ℝ := epsilon / (betaMax * Real.log 2)
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have heta : 0 < eta := div_pos hepsilon (mul_pos hbetaMax hlogTwo)
  obtain ⟨Mcomponent, hcomponent⟩ := componentEnvelope_le_epsilon_length_eventually
    betaMin hbetaMin eta heta
  refine ⟨max Mcomponent 1, ?_⟩
  intro M hM L hlower hupper
  have hMone : 1 ≤ M := (le_max_right _ _).trans hM
  have hdim := hcomponent M ((le_max_left _ _).trans hM) L hlower
  apply two_pow_le_rpow_of_log_bound (by omega : 0 < M)
  calc
    _ ≤ (eta * ((L + 1 : ℕ) : ℝ)) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hdim hlogTwo.le
    _ ≤ (eta * (betaMax * Real.log M)) * Real.log 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hupper heta.le) hlogTwo.le
    _ = epsilon * Real.log M := by dsimp [eta]; field_simp

end
end PaperC.V282.MacroscopicSmallHeightComponents
