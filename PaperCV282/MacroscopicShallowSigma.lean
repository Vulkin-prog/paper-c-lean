import PaperCV282.MacroscopicGeometry
import PaperC.Arithmetic.RationalMassFinite
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Canonical sigma after the positive small-height test

The second sector test in version 2.8.2 is `sigma > 0` together with
`q <= sqrt(log B)`, where `B = L + 1`. In particular a zero-dimensional
channel fails this test, even when a small-height candidate exists.

Height packing gives `q * sigma <= L`. After failure of the test this
makes sigma uniformly small compared with `B`, and makes `2^sigma`
uniformly subpolynomial throughout a full logarithmic band. The pointwise
bound is independent of both starts and of the coding parameter. A finite
maximum on the exact macroscopic separated-pair mask is also provided.
No critical-window endpoint or bounded endpoint ratio is assumed.
-/

namespace PaperC.V282.MacroscopicShallowSigma

open Affine.CanonicalRationalCode RationalMassFinite MacroscopicGeometry TwoWindowParity
open Filter

noncomputable section

/-- The literal positive-sigma small-height test in sector two. -/
def hasSmallPositiveCanonicalHeight (A L x y : ℕ) : Prop :=
  0 < canonicalPairSigma A L x y ∧
    (canonicalPairHeight A L x y : ℝ) ≤ Real.sqrt (Real.log ((L + 1 : ℕ) : ℝ))

/-- Failure of the test includes every zero-dimensional canonical channel. -/
theorem not_small_positive_height_iff (A L x y : ℕ) :
    ¬ hasSmallPositiveCanonicalHeight A L x y ↔
      canonicalPairSigma A L x y = 0 ∨
        Real.sqrt (Real.log ((L + 1 : ℕ) : ℝ)) < (canonicalPairHeight A L x y : ℝ) := by
  unfold hasSmallPositiveCanonicalHeight
  by_cases hsigma : canonicalPairSigma A L x y = 0
  · simp [hsigma]
  · simp [Nat.pos_of_ne_zero hsigma, hsigma, not_le]

/-- The canonical height and dimension satisfy the exact finite packing bound. -/
theorem canonicalPairHeight_mul_sigma_le (A L x y : ℕ) :
    canonicalPairHeight A L x y * canonicalPairSigma A L x y ≤ L := by
  by_cases hsigma : canonicalPairSigma A L x y = 0
  · simp [hsigma]
  have hm : 2 ≤ canonicalMultiplicity A L x y :=
    two_le_canonicalMultiplicity_of_sigma_pos (Nat.pos_of_ne_zero hsigma)
  obtain ⟨c, hchoice, _⟩ := exists_canonical_candidate_of_two_le_multiplicity hm
  rw [canonicalPairHeight_eq_of_choice hchoice,
    canonicalPairSigma_eq_channelSigma_of_choice hchoice]
  exact maxStep_mul_channelSigma_le L c.1.1 c.1.2
    (candidate_fst_pos c) (candidate_snd_pos c) (candidate_coprime c)
    (pairChannelError x y c.1.1 c.1.2)

/-- An explicit exponential length threshold places a fixed real number
below the logarithmic square root. -/
theorem le_sqrt_log_of_exp_sq_le {T B : ℝ} (hB : Real.exp (T ^ 2) ≤ B) :
    T ≤ Real.sqrt (Real.log B) := by
  apply Real.le_sqrt_of_sq_le
  calc
    T ^ 2 = Real.log (Real.exp (T ^ 2)) := (Real.log_exp _).symm
    _ ≤ Real.log B := Real.log_le_log (Real.exp_pos _) hB

/-- Pointwise dimension bound after the exact test fails. Its only scale
hypothesis is an explicit lower bound on the window length. -/
theorem canonicalPairSigma_cast_le_epsilon_length
    {A L x y : ℕ} {eta : ℝ} (heta : 0 < eta)
    (hB : Real.exp ((1 / eta) ^ 2) ≤ ((L + 1 : ℕ) : ℝ))
    (hnot : ¬ hasSmallPositiveCanonicalHeight A L x y) :
    (canonicalPairSigma A L x y : ℝ) ≤ eta * ((L + 1 : ℕ) : ℝ) := by
  rcases (not_small_positive_height_iff A L x y).mp hnot with hsigma | hheight
  · rw [hsigma, Nat.cast_zero]
    positivity
  · have hthreshold : 1 / eta ≤ (canonicalPairHeight A L x y : ℝ) :=
      (le_sqrt_log_of_exp_sq_le hB).trans hheight.le
    have hpacking : (canonicalPairHeight A L x y : ℝ) *
        (canonicalPairSigma A L x y : ℝ) ≤ (L : ℝ) := by
      exact_mod_cast canonicalPairHeight_mul_sigma_le A L x y
    have hscaled : (1 / eta) * (canonicalPairSigma A L x y : ℝ) ≤
        ((L + 1 : ℕ) : ℝ) := by
      calc
        _ ≤ (canonicalPairHeight A L x y : ℝ) * (canonicalPairSigma A L x y : ℝ) :=
          mul_le_mul_of_nonneg_right hthreshold (by positivity)
        _ ≤ (L : ℝ) := hpacking
        _ ≤ ((L + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ L
    calc
      (canonicalPairSigma A L x y : ℝ) =
          eta * ((1 / eta) * (canonicalPairSigma A L x y : ℝ)) := by
        field_simp
      _ ≤ eta * ((L + 1 : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hscaled heta.le

/-- A positive logarithmic lower bound forces every fixed length threshold,
uniformly before the length is selected. -/
theorem length_ge_eventually_of_logarithmic_lower
    (betaMin : ℝ) (hbetaMin : 0 < betaMin) (R : ℝ) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ ((L + 1 : ℕ) : ℝ) → R ≤ ((L + 1 : ℕ) : ℝ) := by
  have hlog : ∀ᶠ M : ℕ in atTop, R / betaMin ≤ Real.log (M : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (R / betaMin))
  obtain ⟨Mzero, hMzero⟩ := eventually_atTop.mp hlog
  refine ⟨Mzero, ?_⟩
  intro M hM L hL
  have hR : R ≤ betaMin * Real.log M := by
    simpa only [mul_comm] using (div_le_iff₀ hbetaMin).mp (hMzero M hM)
  exact hR.trans hL

/-- Sigma is uniformly little-oh of the length after the second test fails.
This estimate already holds for all starts and all coding parameters. -/
theorem canonicalPairSigma_le_epsilon_length_eventually
    (betaMin : ℝ) (hbetaMin : 0 < betaMin) (eta : ℝ) (heta : 0 < eta) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ ((L + 1 : ℕ) : ℝ) → ∀ A x y : ℕ,
      ¬ hasSmallPositiveCanonicalHeight A L x y →
      (canonicalPairSigma A L x y : ℝ) ≤ eta * ((L + 1 : ℕ) : ℝ) := by
  obtain ⟨Mzero, hMzero⟩ := length_ge_eventually_of_logarithmic_lower
    betaMin hbetaMin (Real.exp ((1 / eta) ^ 2))
  refine ⟨Mzero, ?_⟩
  intro M hM L hL A x y hnot
  exact canonicalPairSigma_cast_le_epsilon_length heta (hMzero M hM L hL) hnot

/-- The true binary sigma factor is uniformly subpolynomial on the full
logarithmic band, with the threshold before `L`, `A`, `x`, and `y`. -/
theorem two_pow_sigma_le_rpow_eventually
    (betaMin betaMax : ℝ) (hbetaMin : 0 < betaMin) (hbetaMax : 0 < betaMax)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ ((L + 1 : ℕ) : ℝ) →
      ((L + 1 : ℕ) : ℝ) ≤ betaMax * Real.log M → ∀ A x y : ℕ,
      ¬ hasSmallPositiveCanonicalHeight A L x y →
      (2 : ℝ) ^ canonicalPairSigma A L x y ≤ (M : ℝ) ^ epsilon := by
  let eta : ℝ := epsilon / (betaMax * Real.log 2)
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have heta : 0 < eta := div_pos hepsilon (mul_pos hbetaMax hlogTwo)
  obtain ⟨Msigma, hsigma⟩ := canonicalPairSigma_le_epsilon_length_eventually
    betaMin hbetaMin eta heta
  refine ⟨max Msigma 1, ?_⟩
  intro M hM L hlower hupper A x y hnot
  have hMone : 1 ≤ M := (le_max_right _ _).trans hM
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hdim := hsigma M ((le_max_left _ _).trans hM) L hlower A x y hnot
  have hlog : (canonicalPairSigma A L x y : ℝ) * Real.log 2 ≤
      epsilon * Real.log M := by
    calc
      _ ≤ (eta * ((L + 1 : ℕ) : ℝ)) * Real.log 2 :=
        mul_le_mul_of_nonneg_right hdim hlogTwo.le
      _ ≤ (eta * (betaMax * Real.log M)) * Real.log 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hupper heta.le) hlogTwo.le
      _ = epsilon * Real.log M := by
        dsimp [eta]
        field_simp
  calc
    (2 : ℝ) ^ canonicalPairSigma A L x y =
        Real.exp ((canonicalPairSigma A L x y : ℝ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ Real.exp (epsilon * Real.log M) := Real.exp_le_exp.mpr hlog
    _ = (M : ℝ) ^ epsilon := by rw [Real.rpow_def_of_pos hMpos]; congr 1; ring

/-- The exact macroscopic separated pairs which fail the positive small-height test. -/
def nonSmallSigmaPairs (M A L : ℕ) (delta : ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact (separatedPairs (macroscopicStarts M delta) L).filter
    (fun pair => ¬ hasSmallPositiveCanonicalHeight A L pair.1 pair.2)

/-- Membership retains precisely the macroscopic mask and the failed test. -/
theorem mem_nonSmallSigmaPairs (M A L : ℕ) (delta : ℝ) (pair : ℕ × ℕ) :
    pair ∈ nonSmallSigmaPairs M A L delta ↔
      pair ∈ separatedPairs (macroscopicStarts M delta) L ∧
        ¬ hasSmallPositiveCanonicalHeight A L pair.1 pair.2 := by
  classical
  simp [nonSmallSigmaPairs]

/-- A finite envelope for the canonical dimensions after the failed test. -/
def maxNonSmallSigma (M A L : ℕ) (delta : ℝ) : ℕ :=
  (nonSmallSigmaPairs M A L delta).sup (fun pair => canonicalPairSigma A L pair.1 pair.2)

/-- Every pair in this exact mask is dominated by the finite envelope. -/
theorem canonicalPairSigma_le_max_of_mem {M A L x y : ℕ} {delta : ℝ}
    (hpair : (x, y) ∈ nonSmallSigmaPairs M A L delta) :
    canonicalPairSigma A L x y ≤ maxNonSmallSigma M A L delta := by
  unfold maxNonSmallSigma
  exact Finset.le_sup (f := fun pair => canonicalPairSigma A L pair.1 pair.2) hpair

/-- The finite envelope also has a uniformly subpolynomial binary weight.
The threshold precedes the coding parameter and the macroscopic exponent,
and empty macroscopic populations are included. -/
theorem two_pow_maxNonSmallSigma_le_rpow_eventually
    (betaMin betaMax : ℝ) (hbetaMin : 0 < betaMin) (hbetaMax : 0 < betaMax)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ L : ℕ,
      betaMin * Real.log M ≤ ((L + 1 : ℕ) : ℝ) →
      ((L + 1 : ℕ) : ℝ) ≤ betaMax * Real.log M → ∀ A : ℕ, ∀ delta : ℝ,
      (2 : ℝ) ^ maxNonSmallSigma M A L delta ≤ (M : ℝ) ^ epsilon := by
  obtain ⟨Mpoint, hpoint⟩ := two_pow_sigma_le_rpow_eventually
    betaMin betaMax hbetaMin hbetaMax epsilon hepsilon
  refine ⟨max Mpoint 1, ?_⟩
  intro M hM L hlower hupper A delta
  classical
  by_cases hnonempty : (nonSmallSigmaPairs M A L delta).Nonempty
  · obtain ⟨pair, hpair, hmax⟩ := Finset.exists_mem_eq_sup
      (nonSmallSigmaPairs M A L delta) hnonempty
      (fun pair => canonicalPairSigma A L pair.1 pair.2)
    unfold maxNonSmallSigma
    rw [hmax]
    exact hpoint M ((le_max_left _ _).trans hM) L hlower hupper A pair.1 pair.2
      ((mem_nonSmallSigmaPairs M A L delta pair).mp hpair).2
  · have hempty : nonSmallSigmaPairs M A L delta = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnonempty
    simp only [maxNonSmallSigma, hempty, Finset.sup_empty, bot_eq_zero, pow_zero]
    have hMone : (1 : ℝ) ≤ M := by exact_mod_cast (le_max_right Mpoint 1).trans hM
    exact Real.one_le_rpow hMone hepsilon.le

end
end PaperC.V282.MacroscopicShallowSigma
