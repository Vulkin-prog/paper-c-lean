import PaperC.Analysis.PrimeReciprocalSqrtSum
import PaperC.Analysis.TerminalPrimeCutoff
import PaperC.Analysis.CriticalWindowScale
import PaperC.Probability.BadStartCount

/-!
# Lemma 13.3 at the terminal prime cutoff

This file assembles the finite ingredients of Lemma 13.3 at the manuscript's
literal cutoff

`Y = floor (B^2 * log B)`.

`BadStartCount` reduces the number of `Y`-defective starts to the exact
small-prime Euler product.  `PrimeReciprocalSqrtSum` supplies the missing
prime-sensitive Chebyshev estimate for that product, and
`TerminalPrimeCutoff` supplies the literal value of `Y` and its elementary
comparisons.

For `B >= 16` the resulting unconditional finite bound is

`#D_Y <= 2 L sqrt(2N+L) *
  exp(2 sqrt(rootCutoff Y) +
    56 sqrt(2Y) / floor(log_2 Y / 2))`.

The second form below replaces `Y` in the large square-root numerator by
the exact real scale `B^2 log B` and freezes the denominator at `B`.  This
displays, without introducing an asymptotic bridge, the two contributions
used in the paper's summation-by-parts argument.

No asymptotic conclusion is asserted here: turning this explicit envelope
into `N^(1/2+o_C(1))` additionally uses the critical-window relation
`B = L + 1 = log_2 N + O_C(1)`.  The finite estimate itself is fully
certified and has no hypotheses beyond the displayed numerical lower
bounds.
-/

namespace PaperC
namespace TerminalBadStartBound

open BadStartCount
open PrimeReciprocalSqrtSum
open TerminalPrimeCutoff

noncomputable section

/--
The exponent in the prime-sensitive Euler-product bound at the literal
terminal cutoff `Y = floor(B^2 log B)`.
-/
def terminalBadStartPrimeExponent (B : ℕ) : ℝ :=
  let Y := terminalPrimeCutoff B
  2 * Real.sqrt (rootCutoff Y) +
    56 * Real.sqrt (2 * Y) /
      ((Nat.log 2 Y / 2 : ℕ) : ℝ)

/--
The same exponent with the large square-root numerator replaced by the
defining real terminal scale and its logarithmic denominator frozen at `B`.
-/
def terminalBadStartScaleExponent (B : ℕ) : ℝ :=
  let Y := terminalPrimeCutoff B
  2 * Real.sqrt (rootCutoff Y) +
    56 * Real.sqrt (2 * terminalPrimeScale B) /
      ((Nat.log 2 B / 2 : ℕ) : ℝ)

/--
A readable envelope for the exponent.  Its two summands have the finite
shapes `(B^2 log B)^(1/4)` and `B / sqrt(log B)`, respectively.
-/
def terminalBadStartReadableExponent (B : ℕ) : ℝ :=
  2 * Real.sqrt (Real.sqrt (terminalPrimeScale B)) +
    168 * Real.sqrt 2 * B / Real.sqrt (Real.log B)

/--
For `B >= 16`, the terminal cutoff itself is at least `16`, so the global
prime-sensitive Chebyshev estimate applies at `Y`.
-/
theorem sixteen_le_terminalPrimeCutoff
    {B : ℕ} (hB : 16 ≤ B) :
    16 ≤ terminalPrimeCutoff B := by
  exact hB.trans (le_terminalPrimeCutoff (by omega))

/--
Finite, unconditional assembly of Lemma 13.3 at
`Y = floor(B^2 log B)`.

The factor `L` is exact: it is the maximum number of starts in whose
length-`L` window a fixed defective integer can occur.
-/
theorem card_terminalBadStarts_terminalPrimeCutoff_le
    {N L B : ℕ} (hN : 1 ≤ N) (hB : 16 ≤ B) :
    ((terminalBadStarts N L (terminalPrimeCutoff B)).card : ℝ) ≤
      2 * L * Real.sqrt (dyadicCutoff N L) *
        Real.exp (terminalBadStartPrimeExponent B) := by
  let Y := terminalPrimeCutoff B
  have hY : 16 ≤ Y := by
    simpa only [Y] using sixteen_le_terminalPrimeCutoff hB
  have hcount :=
    card_terminalBadStarts_cast_le_eulerProduct
      (N := N) (L := L) (B := Y) hN
  have hproduct :=
    prod_smallPrimesUpTo_one_add_inv_sqrt_le_primeSensitive_two_mul hY
  have hprefactor :
      0 ≤ 2 * (L : ℝ) * Real.sqrt (dyadicCutoff N L) := by
    positivity
  calc
    ((terminalBadStarts N L (terminalPrimeCutoff B)).card : ℝ) =
        ((terminalBadStarts N L Y).card : ℝ) := rfl
    _ ≤ 2 * L * Real.sqrt (dyadicCutoff N L) *
          ∏ p ∈ DefectCounting.smallPrimesUpTo Y,
            (1 + (Real.sqrt p)⁻¹) :=
      hcount
    _ ≤ 2 * L * Real.sqrt (dyadicCutoff N L) *
          Real.exp
            (2 * Real.sqrt (rootCutoff Y) +
              56 * Real.sqrt (2 * Y) /
                ((Nat.log 2 Y / 2 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hproduct hprefactor
    _ = 2 * L * Real.sqrt (dyadicCutoff N L) *
          Real.exp (terminalBadStartPrimeExponent B) := by
      simp only [terminalBadStartPrimeExponent, Y]

/--
The exact terminal-cutoff exponent is bounded by the version expressed with
the real scale `B^2 log B`.
-/
theorem terminalBadStartPrimeExponent_le_scaleExponent
    {B : ℕ} (hB : 16 ≤ B) :
    terminalBadStartPrimeExponent B ≤
      terminalBadStartScaleExponent B := by
  let Y := terminalPrimeCutoff B
  have hBY : B ≤ Y := by
    simpa only [Y] using le_terminalPrimeCutoff (show 2 ≤ B by omega)
  have hlog :
      Nat.log 2 B ≤ Nat.log 2 Y :=
    Nat.log_mono_right hBY
  have hhalf :
      Nat.log 2 B / 2 ≤ Nat.log 2 Y / 2 :=
    Nat.div_le_div_right hlog
  have hlogB : 4 ≤ Nat.log 2 B := by
    apply Nat.le_log_of_pow_le (by norm_num)
    norm_num
    exact hB
  have hhalfPosNat : 0 < Nat.log 2 B / 2 := by omega
  have hhalfYPos :
      (0 : ℝ) < ((Nat.log 2 Y / 2 : ℕ) : ℝ) := by
    exact_mod_cast lt_of_lt_of_le hhalfPosNat hhalf
  have hhalfBPos :
      (0 : ℝ) < ((Nat.log 2 B / 2 : ℕ) : ℝ) := by
    exact_mod_cast hhalfPosNat
  have hscale :
      ((Y : ℕ) : ℝ) ≤ terminalPrimeScale B := by
    simpa only [Y] using cast_terminalPrimeCutoff_le_scale B
  have hsqrt :
      Real.sqrt (((2 * Y : ℕ) : ℝ)) ≤
        Real.sqrt (2 * terminalPrimeScale B) := by
    apply Real.sqrt_le_sqrt
    norm_num at hscale ⊢
    linarith
  have hnum :
      56 * Real.sqrt (((2 * Y : ℕ) : ℝ)) ≤
        56 * Real.sqrt (2 * terminalPrimeScale B) :=
    mul_le_mul_of_nonneg_left hsqrt (by norm_num)
  have hnumNonneg :
      0 ≤ 56 * Real.sqrt (2 * terminalPrimeScale B) := by
    positivity
  have hratio :
      56 * Real.sqrt (((2 * Y : ℕ) : ℝ)) /
          ((Nat.log 2 Y / 2 : ℕ) : ℝ) ≤
        56 * Real.sqrt (2 * terminalPrimeScale B) /
          ((Nat.log 2 B / 2 : ℕ) : ℝ) := by
    calc
      56 * Real.sqrt (((2 * Y : ℕ) : ℝ)) /
            ((Nat.log 2 Y / 2 : ℕ) : ℝ) ≤
          56 * Real.sqrt (2 * terminalPrimeScale B) /
            ((Nat.log 2 Y / 2 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right hnum hhalfYPos.le
      _ ≤ 56 * Real.sqrt (2 * terminalPrimeScale B) /
            ((Nat.log 2 B / 2 : ℕ) : ℝ) := by
        apply div_le_div_of_nonneg_left hnumNonneg hhalfBPos
        exact_mod_cast hhalf
  change
    2 * Real.sqrt (rootCutoff Y) +
          56 * Real.sqrt (2 * Y) /
            ((Nat.log 2 Y / 2 : ℕ) : ℝ) ≤
      2 * Real.sqrt (rootCutoff Y) +
          56 * Real.sqrt (2 * terminalPrimeScale B) /
            ((Nat.log 2 B / 2 : ℕ) : ℝ)
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    (add_le_add_right hratio (2 * Real.sqrt (rootCutoff Y)))

/--
The scale exponent admits a completely real-variable envelope in which the
Chebyshev term is visibly `O(B / sqrt(log B))`.  This is still a finite
inequality, not asymptotic notation.
-/
theorem terminalBadStartScaleExponent_le_readableExponent
    {B : ℕ} (hB : 16 ≤ B) :
    terminalBadStartScaleExponent B ≤
      terminalBadStartReadableExponent B := by
  let Y := terminalPrimeCutoff B
  have hBY : B ≤ Y := by
    simpa only [Y] using le_terminalPrimeCutoff (show 2 ≤ B by omega)
  have hYone : 1 ≤ Y := by omega
  have hscale :
      ((Y : ℕ) : ℝ) ≤ terminalPrimeScale B := by
    simpa only [Y] using cast_terminalPrimeCutoff_le_scale B
  have hrootSqNat :
      rootCutoff Y ^ 2 ≤ Y :=
    rootCutoff_sq_le hYone
  have hrootSq :
      ((rootCutoff Y : ℕ) : ℝ) ^ 2 ≤ (Y : ℝ) := by
    exact_mod_cast hrootSqNat
  have hroot :
      (rootCutoff Y : ℝ) ≤
        Real.sqrt (terminalPrimeScale B) := by
    exact Real.le_sqrt_of_sq_le (hrootSq.trans hscale)
  have hfirst :
      2 * Real.sqrt (rootCutoff Y) ≤
        2 * Real.sqrt (Real.sqrt (terminalPrimeScale B)) := by
    exact mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt hroot) (by norm_num)
  have hlogBpos : 0 < Real.log (B : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hlogFour : 4 ≤ Nat.log 2 B := by
    apply Nat.le_log_of_pow_le (by norm_num)
    norm_num
    exact hB
  have hhalfPosNat : 0 < Nat.log 2 B / 2 := by omega
  have hhalfPos :
      (0 : ℝ) < ((Nat.log 2 B / 2 : ℕ) : ℝ) := by
    exact_mod_cast hhalfPosNat
  have hrealLogLeNat :
      Real.log (B : ℝ) ≤ (Nat.log 2 B : ℝ) :=
    CriticalWindowScale.real_log_le_nat_log_two (show 8 ≤ B by omega)
  have hnatLogLeThreeHalf :
      Nat.log 2 B ≤ 3 * (Nat.log 2 B / 2) := by
    omega
  have hrealLogLeThreeHalf :
      Real.log (B : ℝ) ≤
        3 * ((Nat.log 2 B / 2 : ℕ) : ℝ) := by
    calc
      Real.log (B : ℝ) ≤ (Nat.log 2 B : ℝ) :=
        hrealLogLeNat
      _ ≤ (3 * (Nat.log 2 B / 2) : ℕ) := by
        exact_mod_cast hnatLogLeThreeHalf
      _ = 3 * ((Nat.log 2 B / 2 : ℕ) : ℝ) := by
        push_cast
        ring
  have hsqrtScale :
      Real.sqrt (2 * terminalPrimeScale B) =
        (B : ℝ) * Real.sqrt (2 * Real.log B) := by
    rw [terminalPrimeScale]
    calc
      Real.sqrt (2 * ((B : ℝ) ^ 2 * Real.log B)) =
          Real.sqrt (((B : ℝ) ^ 2 * (2 * Real.log B))) := by
        congr 1
        ring
      _ = Real.sqrt ((B : ℝ) ^ 2) *
          Real.sqrt (2 * Real.log B) := by
        rw [Real.sqrt_mul (sq_nonneg (B : ℝ))]
      _ = (B : ℝ) * Real.sqrt (2 * Real.log B) := by
        rw [Real.sqrt_sq (Nat.cast_nonneg B)]
  have hsqrtTwoLog :
      Real.sqrt (2 * Real.log (B : ℝ)) =
        Real.sqrt 2 * Real.sqrt (Real.log B) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hsqrtLogPos :
      0 < Real.sqrt (Real.log (B : ℝ)) :=
    Real.sqrt_pos.2 hlogBpos
  have hsecond :
      56 * Real.sqrt (2 * terminalPrimeScale B) /
          ((Nat.log 2 B / 2 : ℕ) : ℝ) ≤
        168 * Real.sqrt 2 * B /
          Real.sqrt (Real.log B) := by
    calc
      56 * Real.sqrt (2 * terminalPrimeScale B) /
            ((Nat.log 2 B / 2 : ℕ) : ℝ) =
          168 * Real.sqrt (2 * terminalPrimeScale B) /
            (3 * ((Nat.log 2 B / 2 : ℕ) : ℝ)) := by
        field_simp
        ring
      _ ≤ 168 * Real.sqrt (2 * terminalPrimeScale B) /
            Real.log B := by
        apply div_le_div_of_nonneg_left
        · positivity
        · exact hlogBpos
        · exact hrealLogLeThreeHalf
      _ = 168 * Real.sqrt 2 * B /
            Real.sqrt (Real.log B) := by
        rw [hsqrtScale, hsqrtTwoLog]
        field_simp [hlogBpos.ne', hsqrtLogPos.ne']
        ring_nf
        rw [Real.sq_sqrt (x := Real.log (B : ℝ)) hlogBpos.le]
  change
    2 * Real.sqrt (rootCutoff Y) +
          56 * Real.sqrt (2 * terminalPrimeScale B) /
            ((Nat.log 2 B / 2 : ℕ) : ℝ) ≤
      2 * Real.sqrt (Real.sqrt (terminalPrimeScale B)) +
          168 * Real.sqrt 2 * B / Real.sqrt (Real.log B)
  exact add_le_add hfirst hsecond

/--
Scale-explicit finite form of Lemma 13.3.  Its exponential factor now
contains the literal real quantity `B^2 log B`.
-/
theorem card_terminalBadStarts_terminalPrimeCutoff_le_scale
    {N L B : ℕ} (hN : 1 ≤ N) (hB : 16 ≤ B) :
    ((terminalBadStarts N L (terminalPrimeCutoff B)).card : ℝ) ≤
      2 * L * Real.sqrt (dyadicCutoff N L) *
        Real.exp (terminalBadStartScaleExponent B) := by
  calc
    ((terminalBadStarts N L (terminalPrimeCutoff B)).card : ℝ) ≤
        2 * L * Real.sqrt (dyadicCutoff N L) *
          Real.exp (terminalBadStartPrimeExponent B) :=
      card_terminalBadStarts_terminalPrimeCutoff_le hN hB
    _ ≤ 2 * L * Real.sqrt (dyadicCutoff N L) *
          Real.exp (terminalBadStartScaleExponent B) := by
      apply mul_le_mul_of_nonneg_left
      · exact Real.exp_le_exp.mpr
          (terminalBadStartPrimeExponent_le_scaleExponent hB)
      · positivity

/--
Readable finite terminal estimate.  This is the strongest assembled form in
this file and is the direct certified analogue of the calculation in the
proof of Lemma 13.3.
-/
theorem card_terminalBadStarts_terminalPrimeCutoff_le_readable
    {N L B : ℕ} (hN : 1 ≤ N) (hB : 16 ≤ B) :
    ((terminalBadStarts N L (terminalPrimeCutoff B)).card : ℝ) ≤
      2 * L * Real.sqrt (dyadicCutoff N L) *
        Real.exp (terminalBadStartReadableExponent B) := by
  calc
    ((terminalBadStarts N L (terminalPrimeCutoff B)).card : ℝ) ≤
        2 * L * Real.sqrt (dyadicCutoff N L) *
          Real.exp (terminalBadStartScaleExponent B) :=
      card_terminalBadStarts_terminalPrimeCutoff_le_scale hN hB
    _ ≤ 2 * L * Real.sqrt (dyadicCutoff N L) *
          Real.exp (terminalBadStartReadableExponent B) := by
      apply mul_le_mul_of_nonneg_left
      · exact Real.exp_le_exp.mpr
          (terminalBadStartScaleExponent_le_readableExponent hB)
      · positivity

/--
At the manuscript choice `B = L + 1`—and, more generally, whenever
`L ≤ B`—the incidence factor can be enlarged from `L` to `B`.  This is the
finite counterpart of the sentence that each defective integer belongs to
`O(B)` start windows.
-/
theorem card_terminalBadStarts_terminalPrimeCutoff_le_with_B
    {N L B : ℕ} (hN : 1 ≤ N) (hB : 16 ≤ B) (hLB : L ≤ B) :
    ((terminalBadStarts N L (terminalPrimeCutoff B)).card : ℝ) ≤
      2 * B * Real.sqrt (dyadicCutoff N L) *
        Real.exp (terminalBadStartScaleExponent B) := by
  calc
    ((terminalBadStarts N L (terminalPrimeCutoff B)).card : ℝ) ≤
        2 * L * Real.sqrt (dyadicCutoff N L) *
          Real.exp (terminalBadStartScaleExponent B) :=
      card_terminalBadStarts_terminalPrimeCutoff_le_scale hN hB
    _ ≤ 2 * B * Real.sqrt (dyadicCutoff N L) *
          Real.exp (terminalBadStartScaleExponent B) := by
      have hcast : (L : ℝ) ≤ (B : ℝ) := by exact_mod_cast hLB
      gcongr

end

end TerminalBadStartBound
end PaperC
