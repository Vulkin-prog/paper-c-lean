import PaperC.Arithmetic.LowZonePrimePivots
import PaperC.Arithmetic.PrimeNumberTheoremInput
import PaperC.Asymptotics.Uniform
import PaperC.Probability.BadStartMass
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Real.Sqrt

set_option maxHeartbeats 1200000

/-!
# The low-zone sum in Lemma 15.1

This file packages the finite prime-pivot theorem into the summed and
uniform form used in Paper C, Lemma 15.1.

The manuscript's real-power restriction `x ≤ L^(2-ε)` is reduced here,
without any bridge, to the elementary finite inequality
`2 * sqrt (x-1) + 1 ≤ L`.

The only remaining input is `PrimeNumberTheoremStatement`, the source-level
prime number theorem `π(L) log L / L → 1`.  Its uniform specialization to
`π(L) - π(sqrt (x+L))`, as well as the elementary exponential-decay
consequence, are proved in Lean.

It is an ordinary theorem hypothesis, never an axiom.  Everything between
that input and the final `o(1)` conclusion is proved here.
-/

namespace PaperC
namespace LowZoneCritical

open scoped BigOperators

open LowZonePrimePivots
open PrimeNumberTheoremInput
open Filter

noncomputable section

/-! ## Exact finite mass bounds -/

/-- The finite low-zone set `{2, ..., X}`. -/
def lowZoneStarts (X : ℕ) : Finset ℕ :=
  Finset.Icc 2 X

@[simp]
theorem mem_lowZoneStarts {x X : ℕ} :
    x ∈ lowZoneStarts X ↔ 2 ≤ x ∧ x ≤ X := by
  simp [lowZoneStarts]

/-- The exact rational probability mass over the finite low zone. -/
noncomputable def lowZoneProbabilityMassQ (L X : ℕ) : ℚ :=
  ∑ x ∈ lowZoneStarts X, startProbability x L x

/-- Real-valued form used by the uniform asymptotic interface. -/
noncomputable def lowZoneProbabilityMass (L X : ℕ) : ℝ :=
  ((lowZoneProbabilityMassQ L X : ℚ) : ℝ)

/-- There are at most `X` starts in `{2, ..., X}`. -/
theorem card_lowZoneStarts_le (X : ℕ) :
    (lowZoneStarts X).card ≤ X := by
  simp [lowZoneStarts]

/-- The exact low-zone mass is nonnegative. -/
theorem lowZoneProbabilityMassQ_nonneg (L X : ℕ) :
    0 ≤ lowZoneProbabilityMassQ L X := by
  unfold lowZoneProbabilityMassQ
  exact Finset.sum_nonneg fun x _ ↦
    BadStartMass.startProbability_nonneg x L x

/-- The real low-zone mass is nonnegative. -/
theorem lowZoneProbabilityMass_nonneg (L X : ℕ) :
    0 ≤ lowZoneProbabilityMass L X := by
  unfold lowZoneProbabilityMass
  exact Rat.cast_nonneg.mpr
    (lowZoneProbabilityMassQ_nonneg L X)

/--
Summing the pointwise prime-pivot estimate gives the exact finite bound

`Σ_{2≤x≤X} P(J_{x,L}=1) ≤ Σ_{2≤x≤X} 2^{-r(x)}`.
-/
theorem lowZoneProbabilityMassQ_le_primeSum
    {L X : ℕ}
    (hgap : ∀ x ∈ lowZoneStarts X,
      2 * Nat.sqrt (x - 1) + 1 ≤ L) :
    lowZoneProbabilityMassQ L X ≤
      ∑ x ∈ lowZoneStarts X,
        (1 : ℚ) /
          (2 : ℚ) ^ (intermediatePrimes x L).card := by
  unfold lowZoneProbabilityMassQ
  apply Finset.sum_le_sum
  intro x hx
  exact
    startProbability_le_inv_two_pow_card_intermediatePrimes
      (mem_lowZoneStarts.mp hx).1 (hgap x hx)

/--
The same finite bound with the exponent written exactly as in the manuscript:

`r(x) = π(L) - π(sqrt (x+L))`.
-/
theorem lowZoneProbabilityMassQ_le_primeCountSum
    {L X : ℕ}
    (hgap : ∀ x ∈ lowZoneStarts X,
      2 * Nat.sqrt (x - 1) + 1 ≤ L) :
    lowZoneProbabilityMassQ L X ≤
      ∑ x ∈ lowZoneStarts X,
        (1 : ℚ) /
          (2 : ℚ) ^
            (PrimesUpTo.count L -
              PrimesUpTo.count (Nat.sqrt (x + L))) := by
  have hfinite :=
    lowZoneProbabilityMassQ_le_primeSum hgap
  apply hfinite.trans_eq
  apply Finset.sum_congr rfl
  intro x hx
  rw [card_intermediatePrimes_eq_primeCount_sub_of_gap
    (mem_lowZoneStarts.mp hx).1 (hgap x hx)]

/-- Reciprocal powers of two reverse inequalities between exponents. -/
private theorem inv_two_pow_anti
    {a b : ℕ} (hab : a ≤ b) :
    (1 : ℚ) / (2 : ℚ) ^ b ≤
      (1 : ℚ) / (2 : ℚ) ^ a := by
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_right₀ (by norm_num) hab

/--
If a common exponent `R` is below every `r(x)`, the complete mass is at most
`X / 2^R`.
-/
theorem lowZoneProbabilityMassQ_le_envelope
    {L X R : ℕ}
    (hgap : ∀ x ∈ lowZoneStarts X,
      2 * Nat.sqrt (x - 1) + 1 ≤ L)
    (hR : ∀ x ∈ lowZoneStarts X,
      R ≤ (intermediatePrimes x L).card) :
    lowZoneProbabilityMassQ L X ≤
      (X : ℚ) / (2 : ℚ) ^ R := by
  calc
    lowZoneProbabilityMassQ L X ≤
        ∑ x ∈ lowZoneStarts X,
          (1 : ℚ) /
            (2 : ℚ) ^ (intermediatePrimes x L).card :=
      lowZoneProbabilityMassQ_le_primeSum hgap
    _ ≤
        ∑ _x ∈ lowZoneStarts X,
          (1 : ℚ) / (2 : ℚ) ^ R := by
      apply Finset.sum_le_sum
      intro x hx
      exact inv_two_pow_anti (hR x hx)
    _ =
        ((lowZoneStarts X).card : ℚ) *
          ((1 : ℚ) / (2 : ℚ) ^ R) := by
      simp
    _ ≤
        (X : ℚ) * ((1 : ℚ) / (2 : ℚ) ^ R) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast card_lowZoneStarts_le X
      · positivity
    _ = (X : ℚ) / (2 : ℚ) ^ R := by ring

/--
Prime-count form of the common-exponent bound.  This is the direct finite
consumer of a uniform PNT lower bound.
-/
theorem lowZoneProbabilityMassQ_le_primeCountEnvelope
    {L X R : ℕ}
    (hgap : ∀ x ∈ lowZoneStarts X,
      2 * Nat.sqrt (x - 1) + 1 ≤ L)
    (hR : ∀ x ∈ lowZoneStarts X,
      R ≤ PrimesUpTo.count L -
        PrimesUpTo.count (Nat.sqrt (x + L))) :
    lowZoneProbabilityMassQ L X ≤
      (X : ℚ) / (2 : ℚ) ^ R := by
  apply lowZoneProbabilityMassQ_le_envelope hgap
  intro x hx
  rw [card_intermediatePrimes_eq_primeCount_sub_of_gap
    (mem_lowZoneStarts.mp hx).1 (hgap x hx)]
  exact hR x hx

/-- Real-cast form of the finite prime-count envelope. -/
theorem lowZoneProbabilityMass_le_primeCountEnvelope
    {L X R : ℕ}
    (hgap : ∀ x ∈ lowZoneStarts X,
      2 * Nat.sqrt (x - 1) + 1 ≤ L)
    (hR : ∀ x ∈ lowZoneStarts X,
      R ≤ PrimesUpTo.count L -
        PrimesUpTo.count (Nat.sqrt (x + L))) :
    lowZoneProbabilityMass L X ≤
      (X : ℝ) / (2 : ℝ) ^ R := by
  have hq :=
    lowZoneProbabilityMassQ_le_primeCountEnvelope hgap hR
  have hcast := (Rat.cast_le (K := ℝ)).2 hq
  push_cast at hcast
  simpa only [lowZoneProbabilityMass] using hcast

/-! ## The manuscript power zone and its square gap -/

/--
Every start in an admissible low-zone cutoff eventually satisfies the
elementary square-gap inequality used by the finite theorem.

This is a reusable interface, not a bridge: the exact manuscript family is
defined and proved to satisfy it below.
-/
def LowZoneSquareGapOn
    (admissible : ℕ → ℕ → Prop) : Prop :=
  ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ X, admissible L X →
    ∀ x ∈ lowZoneStarts X,
      2 * Nat.sqrt (x - 1) + 1 ≤ L

/-!
The restrictions on `ε` are part of the family.  Thus the definition is total
in `ε`, while exactly recording the manuscript range when the family is
inhabited.
-/

/-- The precise low-zone cutoff from Lemma 15.1. -/
def LowZonePowerAdmissible
    (ε : ℝ) (L X : ℕ) : Prop :=
  0 < ε ∧ ε < 1 ∧
    (X : ℝ) ≤ (L : ℝ) ^ (2 - ε)

/--
If `4x ≤ L²`, then the first square strictly above `x-1` fits in a window of
length `L`.
-/
private theorem squareGap_of_four_mul_le_square
    {x L : ℕ} (hx : 1 ≤ x) (hfour : 4 * x ≤ L ^ 2) :
    2 * Nat.sqrt (x - 1) + 1 ≤ L := by
  have hsqrt :
      Nat.sqrt (x - 1) ^ 2 ≤ x - 1 :=
    Nat.sqrt_le' (x - 1)
  by_contra hgap
  have hL :
      L ≤ 2 * Nat.sqrt (x - 1) := by
    omega
  have hLSquare :
      L ^ 2 ≤ (2 * Nat.sqrt (x - 1)) ^ 2 :=
    Nat.pow_le_pow_left hL 2
  have hsqrtFour :
      4 * Nat.sqrt (x - 1) ^ 2 ≤ 4 * (x - 1) :=
    Nat.mul_le_mul_left 4 hsqrt
  have hstrict : L ^ 2 < 4 * x := by
    calc
      L ^ 2 ≤ (2 * Nat.sqrt (x - 1)) ^ 2 := hLSquare
      _ = 4 * Nat.sqrt (x - 1) ^ 2 := by ring
      _ ≤ 4 * (x - 1) := hsqrtFour
      _ < 4 * x := by omega
  omega

/--
The square-gap condition is unconditional on the manuscript power zone.

Indeed, `L^ε → ∞`; hence eventually `4 ≤ L^ε`, and
`x ≤ L^(2-ε)` gives `4x ≤ L²`.
-/
theorem lowZoneSquareGapOn_power (ε : ℝ) :
    LowZoneSquareGapOn (LowZonePowerAdmissible ε) := by
  by_cases hε : 0 < ε
  · have heventually :
        ∀ᶠ L : ℕ in atTop, (4 : ℝ) ≤ (L : ℝ) ^ ε := by
      exact
        ((tendsto_rpow_atTop hε).comp
          tendsto_natCast_atTop_atTop).eventually
            (eventually_ge_atTop 4)
    obtain ⟨Lpow, hLpow⟩ := eventually_atTop.mp heventually
    refine ⟨max 1 Lpow, ?_⟩
    intro L hL X hAdmissible x hx
    have hLone : 1 ≤ L :=
      (le_max_left 1 Lpow).trans hL
    have hLpowBound : (4 : ℝ) ≤ (L : ℝ) ^ ε :=
      hLpow L ((le_max_right 1 Lpow).trans hL)
    have hxPower :
        (x : ℝ) ≤ (L : ℝ) ^ (2 - ε) := by
      exact
        (Nat.cast_le.mpr (mem_lowZoneStarts.mp hx).2).trans
          hAdmissible.2.2
    have hLpos : (0 : ℝ) < (L : ℝ) :=
      Nat.cast_pos.mpr (by omega)
    have hfourReal :
        (4 : ℝ) * (x : ℝ) ≤ (L : ℝ) ^ (2 : ℕ) := by
      calc
        (4 : ℝ) * (x : ℝ) ≤
            4 * (L : ℝ) ^ (2 - ε) :=
          mul_le_mul_of_nonneg_left hxPower (by norm_num)
        _ ≤ (L : ℝ) ^ ε * (L : ℝ) ^ (2 - ε) :=
          mul_le_mul_of_nonneg_right hLpowBound
            (Real.rpow_nonneg (Nat.cast_nonneg L) _)
        _ = (L : ℝ) ^ (2 : ℕ) := by
          rw [← Real.rpow_add hLpos]
          rw [show ε + (2 - ε) = (2 : ℝ) by ring,
            Real.rpow_two]
    have hfourNat : 4 * x ≤ L ^ 2 := by
      exact_mod_cast hfourReal
    exact squareGap_of_four_mul_le_square
      (by have := (mem_lowZoneStarts.mp hx).1; omega) hfourNat
  · refine ⟨0, ?_⟩
    intro L _hL X hAdmissible
    exact (hε hAdmissible.1).elim

/--
A fixed logarithmic rank sufficient for the low-zone envelope.  The factor
three is deliberately coarse: `X ≤ L^(2-ε)` while
`2^(3 log₂ L)` has cubic size.
-/
def lowZonePrimeRank (L : ℕ) : ℕ :=
  3 * Nat.log 2 L

/--
The exponential-decay consequence formerly bundled into the PNT bridge is
elementary and unconditional on the manuscript power zone.
-/
theorem lowZonePowerEnvelope_uniformLittleOOne (ε : ℝ) :
    UniformLittleOOn (LowZonePowerAdmissible ε)
      (fun L _X ↦
        (_X : ℝ) / (2 : ℝ) ^ lowZonePrimeRank L)
      (fun _ _ ↦ 1) := by
  intro δ hδ
  by_cases hε : 0 < ε
  · have hdecay :
        Tendsto
          (fun L : ℕ ↦
            8 * (L : ℝ) ^ (-(1 + ε)))
          atTop (nhds 0) := by
      have hrpow :
          Tendsto
            (fun L : ℕ ↦
              (L : ℝ) ^ (-(1 + ε)))
            atTop (nhds 0) :=
        (tendsto_rpow_neg_atTop (by linarith : 0 < 1 + ε)).comp
          tendsto_natCast_atTop_atTop
      simpa using Tendsto.const_mul 8 hrpow
    have heventually :
        ∀ᶠ L : ℕ in atTop,
          8 * (L : ℝ) ^ (-(1 + ε)) < δ :=
      hdecay.eventually (Iio_mem_nhds hδ)
    obtain ⟨Ldecay, hLdecay⟩ :=
      eventually_atTop.mp heventually
    refine ⟨max 1 Ldecay, ?_⟩
    intro L hL X hAdmissible
    have hLone : 1 ≤ L :=
      (le_max_left 1 Ldecay).trans hL
    have hLpos : (0 : ℝ) < (L : ℝ) :=
      Nat.cast_pos.mpr (by omega)
    have hXPower :
        (X : ℝ) ≤ (L : ℝ) ^ (2 - ε) :=
      hAdmissible.2.2
    have hlog :
        L < 2 ^ (Nat.log 2 L).succ :=
      Nat.lt_pow_succ_log_self (by norm_num) L
    have hLdouble :
        L ≤ 2 * 2 ^ Nat.log 2 L := by
      calc
        L ≤ 2 ^ (Nat.log 2 L).succ :=
          Nat.le_of_lt hlog
        _ = 2 * 2 ^ Nat.log 2 L := by
          rw [pow_succ']
    have hcubeNat :
        L ^ 3 ≤ 8 * 2 ^ lowZonePrimeRank L := by
      calc
        L ^ 3 ≤ (2 * 2 ^ Nat.log 2 L) ^ 3 :=
          Nat.pow_le_pow_left hLdouble 3
        _ = 8 * (2 ^ Nat.log 2 L) ^ 3 := by ring
        _ = 8 * 2 ^ lowZonePrimeRank L := by
          simp only [lowZonePrimeRank]
          rw [← pow_mul]
          congr 2
          omega
    have hcubeReal :
        (L : ℝ) ^ 3 ≤
          8 * (2 : ℝ) ^ lowZonePrimeRank L := by
      exact_mod_cast hcubeNat
    have hdenPos :
        0 < (2 : ℝ) ^ lowZonePrimeRank L := by
      positivity
    have hinvDen :
        (1 : ℝ) / (2 : ℝ) ^ lowZonePrimeRank L ≤
          8 / (L : ℝ) ^ 3 := by
      rw [div_le_div_iff₀ hdenPos (pow_pos hLpos 3)]
      simpa using hcubeReal
    have henvelope :
        (X : ℝ) / (2 : ℝ) ^ lowZonePrimeRank L ≤
          8 * (L : ℝ) ^ (-(1 + ε)) := by
      calc
        (X : ℝ) / (2 : ℝ) ^ lowZonePrimeRank L =
            (X : ℝ) *
              ((1 : ℝ) /
                (2 : ℝ) ^ lowZonePrimeRank L) := by ring
        _ ≤ (L : ℝ) ^ (2 - ε) *
              ((1 : ℝ) /
                (2 : ℝ) ^ lowZonePrimeRank L) :=
          mul_le_mul_of_nonneg_right hXPower
            (by positivity)
        _ ≤ (L : ℝ) ^ (2 - ε) *
              (8 / (L : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_left hinvDen
            (Real.rpow_nonneg (Nat.cast_nonneg L) _)
        _ = 8 * (L : ℝ) ^ (-(1 + ε)) := by
          calc
            (L : ℝ) ^ (2 - ε) *
                  (8 / (L : ℝ) ^ 3) =
                8 *
                  ((L : ℝ) ^ (2 - ε) /
                    (L : ℝ) ^ 3) := by ring
            _ = 8 *
                  (L : ℝ) ^ ((2 - ε) - 3) := by
              congr 1
              calc
                (L : ℝ) ^ (2 - ε) / (L : ℝ) ^ (3 : ℕ) =
                    (L : ℝ) ^ (2 - ε) /
                      (L : ℝ) ^ (3 : ℝ) := by
                  exact congrArg
                    (fun z : ℝ ↦
                      (L : ℝ) ^ (2 - ε) / z)
                    (Real.rpow_natCast (L : ℝ) 3).symm
                _ = (L : ℝ) ^ ((2 - ε) - 3) :=
                  (Real.rpow_sub hLpos
                    (2 - ε) (3 : ℝ)).symm
            _ = 8 * (L : ℝ) ^ (-(1 + ε)) := by
              congr 2
              ring
    have hsmall :
        8 * (L : ℝ) ^ (-(1 + ε)) < δ :=
      hLdecay L ((le_max_right 1 Ldecay).trans hL)
    simp only [abs_one, mul_one]
    rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg X) hdenPos.le)]
    exact henvelope.trans hsmall.le
  · refine ⟨0, ?_⟩
    intro L _hL X hAdmissible
    exact (hε hAdmissible.1).elim

/-! ## Uniform specialization of the source-level PNT -/

/--
Reusable, derived interface: `R L X` is eventually a uniform lower bound for
`π(L)-π(sqrt(x+L))` throughout an admissible low zone.

This is not a bridge.  The manuscript instance with
`R = 3 * log₂ L` is proved below from `PrimeNumberTheoremStatement`.
-/
def LowZonePrimeGrowthOn
    (admissible : ℕ → ℕ → Prop)
    (R : ℕ → ℕ → ℕ) : Prop :=
  ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ X, admissible L X →
    ∀ x ∈ lowZoneStarts X,
      R L X ≤ PrimesUpTo.count L -
        PrimesUpTo.count (Nat.sqrt (x + L))

/-- The number of primes at most `H` is at most `H + 1`. -/
private theorem primeCount_le_succ (H : ℕ) :
    PrimesUpTo.count H ≤ H + 1 := by
  calc
    PrimesUpTo.count H =
        (DefectCounting.smallPrimesUpTo H).card :=
      PrimeCountBridge.count_eq_card_smallPrimesUpTo H
    _ ≤ (Finset.range (H + 1)).card := by
      exact Finset.card_filter_le _ _
    _ = H + 1 := by simp

/--
The integer logarithm in base two is bounded by the corresponding real
logarithm.
-/
private theorem natLogTwo_cast_le_log_div
    {L : ℕ} (hL : 1 ≤ L) :
    (Nat.log 2 L : ℝ) ≤
      Real.log (L : ℝ) / Real.log 2 := by
  have hpowNat :
      2 ^ Nat.log 2 L ≤ L :=
    Nat.pow_log_le_self 2 (by omega)
  have hpowReal :
      ((2 ^ Nat.log 2 L : ℕ) : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast hpowNat
  have hlogs :=
    Real.log_le_log
      (by positivity :
        (0 : ℝ) < ((2 ^ Nat.log 2 L : ℕ) : ℝ))
      hpowReal
  rw [Nat.cast_pow, Real.log_pow] at hlogs
  have hlogTwoPos : 0 < Real.log 2 :=
    Real.log_pos one_lt_two
  rw [le_div_iff₀ hlogTwoPos]
  simpa [mul_comm] using hlogs

/--
The source-level PNT implies the exact uniform prime-rank estimate consumed
in Lemma 15.1.

The proof deliberately uses the weak rank `3 log₂ L`.  PNT gives a lower
bound of order `L / log L`, whereas uniformly for
`x ≤ L^(2-ε)` the subtracted count is at most
`O(L^(1-ε/2))`; the logarithmic rank is smaller still.
-/
theorem primeNumberTheorem_implies_lowZonePrimeGrowth_power
    {ε : ℝ}
    (hpnt : PrimeNumberTheoremStatement) :
    LowZonePrimeGrowthOn (LowZonePowerAdmissible ε)
      (fun L _X ↦ lowZonePrimeRank L) := by
  by_cases hε : 0 < ε
  · have hpntEvent :
        ∀ᶠ L : ℕ in atTop,
          (1 / 2 : ℝ) <
            (PrimesUpTo.count L : ℝ) *
              Real.log (L : ℝ) / (L : ℝ) :=
      hpnt.eventually (Ioi_mem_nhds (by norm_num))
    have hquarter : 0 < ε / 4 := by positivity
    have heighth : 0 < ε / 8 := by positivity
    have hlogQuarterRaw :
        ∀ᶠ L : ℕ in atTop,
          ‖Real.log (L : ℝ)‖ ≤
            (1 / 2 : ℝ) * ‖(L : ℝ) ^ (ε / 4)‖ :=
      tendsto_natCast_atTop_atTop.eventually
        ((isLittleO_log_rpow_atTop hquarter).bound
          (by norm_num))
    have hlogEighthRaw :
        ∀ᶠ L : ℕ in atTop,
          ‖Real.log (L : ℝ)‖ ≤
            (1 : ℝ) * ‖(L : ℝ) ^ (ε / 8)‖ :=
      tendsto_natCast_atTop_atTop.eventually
        ((isLittleO_log_rpow_atTop heighth).bound
          zero_lt_one)
    let C : ℝ := 3 + 3 / Real.log 2
    have hCEvent :
        ∀ᶠ L : ℕ in atTop,
          C < (L : ℝ) ^ (ε / 4) :=
      ((tendsto_rpow_atTop hquarter).comp
        tendsto_natCast_atTop_atTop).eventually
          (eventually_gt_atTop C)
    have hgrowth :
        ∀ᶠ L : ℕ in atTop,
          ∀ X, LowZonePowerAdmissible ε L X →
            ∀ x ∈ lowZoneStarts X,
              lowZonePrimeRank L ≤
                PrimesUpTo.count L -
                  PrimesUpTo.count (Nat.sqrt (x + L)) := by
      filter_upwards
        [hpntEvent, hlogQuarterRaw, hlogEighthRaw,
          hCEvent, eventually_ge_atTop 2] with
          L hpntL hlogQuarterNorm hlogEighthNorm hCL hLtwo
      intro X hAdmissible x hx
      have hLone : (1 : ℝ) ≤ (L : ℝ) := by
        exact_mod_cast (show 1 ≤ L by omega)
      have hLpos : (0 : ℝ) < (L : ℝ) :=
        lt_of_lt_of_le zero_lt_one hLone
      have hlogPos : 0 < Real.log (L : ℝ) :=
        Real.log_pos (by exact_mod_cast hLtwo)
      have hlogQuarter :
          2 * Real.log (L : ℝ) ≤ (L : ℝ) ^ (ε / 4) := by
        rw [Real.norm_eq_abs,
          abs_of_pos hlogPos,
          Real.norm_eq_abs,
          abs_of_nonneg
            (Real.rpow_nonneg (Nat.cast_nonneg L) _)] at hlogQuarterNorm
        nlinarith
      have hlogEighth :
          Real.log (L : ℝ) ≤ (L : ℝ) ^ (ε / 8) := by
        rw [Real.norm_eq_abs,
          abs_of_pos hlogPos,
          Real.norm_eq_abs,
          abs_of_nonneg
            (Real.rpow_nonneg (Nat.cast_nonneg L) _)] at hlogEighthNorm
        simpa using hlogEighthNorm
      let a : ℝ := 1 - ε / 2
      let b : ℝ := 1 - ε / 4
      have ha : 0 < a := by
        dsimp only [a]
        linarith [hAdmissible.2.1]
      have heighth_le_a : ε / 8 ≤ a := by
        dsimp only [a]
        linarith [hAdmissible.2.1]
      have hone_le_mainExponent : (1 : ℝ) ≤ 2 - ε := by
        linarith [hAdmissible.2.1]
      have hL_le_mainPower :
          (L : ℝ) ≤ (L : ℝ) ^ (2 - ε) := by
        calc
          (L : ℝ) = (L : ℝ) ^ (1 : ℝ) := by
            rw [Real.rpow_one]
          _ ≤ (L : ℝ) ^ (2 - ε) :=
            Real.rpow_le_rpow_of_exponent_le
              hLone hone_le_mainExponent
      have hxPower :
          (x : ℝ) ≤ (L : ℝ) ^ (2 - ε) := by
        exact
          (Nat.cast_le.mpr (mem_lowZoneStarts.mp hx).2).trans
            hAdmissible.2.2
      have hxL :
          ((x + L : ℕ) : ℝ) ≤
            2 * (L : ℝ) ^ (2 - ε) := by
        push_cast
        linarith
      have hpowerSquare :
          ((L : ℝ) ^ a) ^ (2 : ℕ) =
            (L : ℝ) ^ (2 - ε) := by
        rw [← Real.rpow_two,
          ← Real.rpow_mul (Nat.cast_nonneg L)]
        congr 1
        dsimp only [a]
        ring
      have hsqrtReal :
          Real.sqrt (((x + L : ℕ) : ℝ)) ≤
            2 * (L : ℝ) ^ a := by
        rw [Real.sqrt_le_iff]
        constructor
        · positivity
        · calc
            ((x + L : ℕ) : ℝ) ≤
                2 * (L : ℝ) ^ (2 - ε) := hxL
            _ ≤ 4 * (L : ℝ) ^ (2 - ε) := by
              have :=
                Real.rpow_nonneg
                  (Nat.cast_nonneg L) (2 - ε)
              nlinarith
            _ = 4 * ((L : ℝ) ^ a) ^ 2 := by
              rw [hpowerSquare]
            _ = (2 * (L : ℝ) ^ a) ^ 2 := by ring
      have hsqrtNat :
          (Nat.sqrt (x + L) : ℝ) ≤
            2 * (L : ℝ) ^ a :=
        Real.nat_sqrt_le_real_sqrt.trans hsqrtReal
      have hlogTwo :
          (Nat.log 2 L : ℝ) ≤
            Real.log (L : ℝ) / Real.log 2 :=
        natLogTwo_cast_le_log_div (by omega)
      have hrankLog :
          (lowZonePrimeRank L : ℝ) ≤
            (3 / Real.log 2) * Real.log (L : ℝ) := by
        calc
          (lowZonePrimeRank L : ℝ) =
              3 * (Nat.log 2 L : ℝ) := by
            simp [lowZonePrimeRank]
          _ ≤ 3 *
              (Real.log (L : ℝ) / Real.log 2) :=
            mul_le_mul_of_nonneg_left hlogTwo (by norm_num)
          _ = (3 / Real.log 2) *
              Real.log (L : ℝ) := by ring
      have hlogPowerA :
          Real.log (L : ℝ) ≤ (L : ℝ) ^ a := by
        calc
          Real.log (L : ℝ) ≤
              (L : ℝ) ^ (ε / 8) := hlogEighth
          _ ≤ (L : ℝ) ^ a :=
            Real.rpow_le_rpow_of_exponent_le
              hLone heighth_le_a
      have hcLogNonneg : 0 ≤ 3 / Real.log 2 := by
        positivity
      have hrankPower :
          (lowZonePrimeRank L : ℝ) ≤
            (3 / Real.log 2) * (L : ℝ) ^ a :=
        hrankLog.trans
          (mul_le_mul_of_nonneg_left hlogPowerA hcLogNonneg)
      have hpowerOne : 1 ≤ (L : ℝ) ^ a :=
        Real.one_le_rpow hLone ha.le
      have hsmallBound :
          ((Nat.sqrt (x + L) + 1 +
              lowZonePrimeRank L : ℕ) : ℝ) ≤
            C * (L : ℝ) ^ a := by
        push_cast
        dsimp only [C]
        nlinarith
      have hsmallTarget :
          ((Nat.sqrt (x + L) + 1 +
              lowZonePrimeRank L : ℕ) : ℝ) <
            (L : ℝ) ^ b := by
        apply hsmallBound.trans_lt
        calc
          C * (L : ℝ) ^ a <
              (L : ℝ) ^ (ε / 4) *
                (L : ℝ) ^ a :=
            mul_lt_mul_of_pos_right hCL
              (Real.rpow_pos_of_pos hLpos _)
          _ = (L : ℝ) ^ b := by
            rw [← Real.rpow_add hLpos]
            congr 1
            dsimp only [a, b]
            ring
      have htargetProduct :
          (L : ℝ) ^ (ε / 4) * (L : ℝ) ^ b =
            (L : ℝ) := by
        rw [← Real.rpow_add hLpos]
        rw [show ε / 4 + b = (1 : ℝ) by
          dsimp only [b]
          ring, Real.rpow_one]
      have htargetScaled :
          (L : ℝ) ^ b *
              (Real.log (L : ℝ) / (L : ℝ)) ≤
            (1 / 2 : ℝ) := by
        rw [show
          (L : ℝ) ^ b *
              (Real.log (L : ℝ) / (L : ℝ)) =
            ((L : ℝ) ^ b * Real.log (L : ℝ)) /
              (L : ℝ) by ring]
        rw [div_le_iff₀ hLpos]
        have hmul :=
          mul_le_mul_of_nonneg_right hlogQuarter
            (Real.rpow_nonneg (Nat.cast_nonneg L) b)
        rw [mul_assoc, mul_left_comm,
          mul_comm (2 : ℝ)] at hmul
        rw [htargetProduct] at hmul
        nlinarith
      have hscalePos :
          0 < Real.log (L : ℝ) / (L : ℝ) :=
        div_pos hlogPos hLpos
      have hpntScaled :
          (1 / 2 : ℝ) <
            (PrimesUpTo.count L : ℝ) *
              (Real.log (L : ℝ) / (L : ℝ)) := by
        simpa only [div_eq_mul_inv, mul_assoc] using hpntL
      have hsmallScaled :
          ((Nat.sqrt (x + L) + 1 +
              lowZonePrimeRank L : ℕ) : ℝ) *
                (Real.log (L : ℝ) / (L : ℝ)) <
            (L : ℝ) ^ b *
                (Real.log (L : ℝ) / (L : ℝ)) :=
        mul_lt_mul_of_pos_right hsmallTarget hscalePos
      have hsmallPrimeReal :
          ((Nat.sqrt (x + L) + 1 +
              lowZonePrimeRank L : ℕ) : ℝ) <
            (PrimesUpTo.count L : ℝ) := by
        exact lt_of_mul_lt_mul_right
          (hsmallScaled.trans_le htargetScaled |>.trans hpntScaled)
          hscalePos.le
      have hsmallPrimeNat :
          Nat.sqrt (x + L) + 1 + lowZonePrimeRank L <
            PrimesUpTo.count L := by
        exact_mod_cast hsmallPrimeReal
      have hcountSmall :
          PrimesUpTo.count (Nat.sqrt (x + L)) ≤
            Nat.sqrt (x + L) + 1 :=
        primeCount_le_succ _
      omega
    obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp hgrowth
    exact ⟨L₀, fun L hL ↦ hL₀ L hL⟩
  · refine ⟨0, ?_⟩
    intro L _hL X hAdmissible
    exact (hε hAdmissible.1).elim

/--
Generic closure theorem: a square-gap interface, a prime-growth interface,
and its envelope imply that the total low-zone start probability is uniformly
`o(1)`.
-/
theorem lowZoneProbabilityMass_uniformLittleOOne
    {admissible : ℕ → ℕ → Prop}
    {R : ℕ → ℕ → ℕ}
    (hgap : LowZoneSquareGapOn admissible)
    (hprime : LowZonePrimeGrowthOn admissible R)
    (henvelope :
      UniformLittleOOn admissible
        (fun L X ↦ (X : ℝ) / (2 : ℝ) ^ (R L X))
        (fun _ _ ↦ 1)) :
    UniformLittleOOn admissible
      lowZoneProbabilityMass (fun _ _ ↦ 1) := by
  obtain ⟨Lgap, hgapEventually⟩ := hgap
  obtain ⟨Lprime, hprimeEventually⟩ := hprime
  intro ε hε
  obtain ⟨Lenv, henvEventually⟩ := henvelope ε hε
  refine ⟨max Lgap (max Lprime Lenv), ?_⟩
  intro L hL X hAdmissible
  have hLgap : Lgap ≤ L :=
    (le_max_left Lgap (max Lprime Lenv)).trans hL
  have hLtail : max Lprime Lenv ≤ L :=
    (le_max_right Lgap (max Lprime Lenv)).trans hL
  have hLprime : Lprime ≤ L :=
    (le_max_left Lprime Lenv).trans hLtail
  have hLenv : Lenv ≤ L :=
    (le_max_right Lprime Lenv).trans hLtail
  have hgapFinite :=
    hgapEventually L hLgap X hAdmissible
  have hprimeFinite :=
    hprimeEventually L hLprime X hAdmissible
  have hfinite :=
    lowZoneProbabilityMass_le_primeCountEnvelope
      hgapFinite hprimeFinite
  have henvelopeBound :=
    henvEventually L hLenv X hAdmissible
  have hmassNonneg :=
    lowZoneProbabilityMass_nonneg L X
  have henvelopeNonneg :
      0 ≤ (X : ℝ) / (2 : ℝ) ^ (R L X) := by
    positivity
  simp only [abs_one, mul_one] at henvelopeBound ⊢
  rw [abs_of_nonneg hmassNonneg]
  rw [abs_of_nonneg henvelopeNonneg] at henvelopeBound
  exact hfinite.trans henvelopeBound

/--
Lemma 15.1 on its exact power zone.  Its square-gap part has been discharged
in Lean, so the only bridge hypothesis left is the external PNT input.
-/
theorem lowZoneProbabilityMass_uniformLittleOOne_power
    {ε : ℝ}
    (hpnt : PrimeNumberTheoremStatement) :
    UniformLittleOOn (LowZonePowerAdmissible ε)
      lowZoneProbabilityMass (fun _ _ ↦ 1) :=
  lowZoneProbabilityMass_uniformLittleOOne
    (lowZoneSquareGapOn_power ε)
    (primeNumberTheorem_implies_lowZonePrimeGrowth_power hpnt)
    (lowZonePowerEnvelope_uniformLittleOOne ε)

end

end LowZoneCritical
end PaperC
