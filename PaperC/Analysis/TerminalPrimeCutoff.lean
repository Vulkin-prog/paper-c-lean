import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Complex.ExponentialBounds

/-!
# The terminal prime cutoff

Section 13 of the paper fixes the integer cutoff

`Y = floor (B^2 * log B)`.

This file records that definition literally, using the natural-valued floor,
and proves only the elementary finite comparisons needed when the cutoff is
passed to the terminal-kernel and bad-start estimates.  In particular, no
asymptotic assertion is hidden in the definition.
-/

namespace PaperC
namespace TerminalPrimeCutoff

noncomputable section

/-- The real quantity whose natural floor is the cutoff from Section 13. -/
def terminalPrimeScale (B : ℕ) : ℝ :=
  (B : ℝ) ^ 2 * Real.log (B : ℝ)

/--
The terminal prime cutoff from Section 13:
`Y = floor (B^2 * log B)`.
-/
def terminalPrimeCutoff (B : ℕ) : ℕ :=
  ⌊terminalPrimeScale B⌋₊

/-- The real quantity defining the cutoff is nonnegative for every natural `B`. -/
theorem terminalPrimeScale_nonneg (B : ℕ) :
    0 ≤ terminalPrimeScale B := by
  exact
    mul_nonneg (sq_nonneg (B : ℝ))
      (Real.log_natCast_nonneg B)

/-- The natural floor lies below the real quantity that defines it. -/
theorem cast_terminalPrimeCutoff_le_scale (B : ℕ) :
    (terminalPrimeCutoff B : ℝ) ≤ terminalPrimeScale B := by
  exact Nat.floor_le (terminalPrimeScale_nonneg B)

/-- The defining real quantity is strictly below one plus its natural floor. -/
theorem terminalPrimeScale_lt_cutoff_add_one (B : ℕ) :
    terminalPrimeScale B < (terminalPrimeCutoff B : ℝ) + 1 := by
  exact Nat.lt_floor_add_one (terminalPrimeScale B)

/-- At the two degenerate natural inputs, the cutoff is exactly known. -/
@[simp] theorem terminalPrimeCutoff_zero :
    terminalPrimeCutoff 0 = 0 := by
  simp [terminalPrimeCutoff, terminalPrimeScale]

/-- At the two degenerate natural inputs, the cutoff is exactly known. -/
@[simp] theorem terminalPrimeCutoff_one :
    terminalPrimeCutoff 1 = 0 := by
  simp [terminalPrimeCutoff, terminalPrimeScale]

/--
For `B ≥ 2`, the Section 13 cutoff is at least `B`.

The only numerical input is Mathlib's certified lower bound for `log 2`;
there is no asymptotic argument here.
-/
theorem le_terminalPrimeCutoff {B : ℕ} (hB : 2 ≤ B) :
    B ≤ terminalPrimeCutoff B := by
  rw [terminalPrimeCutoff,
    Nat.le_floor_iff (terminalPrimeScale_nonneg B)]
  have hcastB : (2 : ℝ) ≤ (B : ℝ) := by
    exact_mod_cast hB
  have hlogMono :
      Real.log (2 : ℝ) ≤ Real.log (B : ℝ) := by
    exact Real.log_le_log (by norm_num) hcastB
  have hhalfLog :
      (1 / 2 : ℝ) ≤ Real.log (B : ℝ) := by
    have hhalfTwo : (1 / 2 : ℝ) < Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    exact hhalfTwo.le.trans hlogMono
  have hone :
      (1 : ℝ) ≤ (B : ℝ) * Real.log (B : ℝ) := by
    calc
      (1 : ℝ) = 2 * (1 / 2) := by norm_num
      _ ≤ (B : ℝ) * Real.log (B : ℝ) :=
        mul_le_mul hcastB hhalfLog (by norm_num) (by norm_num)
  have hBnonneg : (0 : ℝ) ≤ (B : ℝ) := by positivity
  calc
    (B : ℝ) = (B : ℝ) * 1 := by ring
    _ ≤ (B : ℝ) * ((B : ℝ) * Real.log (B : ℝ)) :=
      mul_le_mul_of_nonneg_left hone hBnonneg
    _ = terminalPrimeScale B := by
      simp only [terminalPrimeScale]
      ring

/-- In particular, the cutoff is positive as soon as `B ≥ 2`. -/
theorem terminalPrimeCutoff_pos {B : ℕ} (hB : 2 ≤ B) :
    0 < terminalPrimeCutoff B := by
  exact
    lt_of_lt_of_le (by omega : 0 < B)
      (le_terminalPrimeCutoff hB)

/--
The cutoff has the uniform polynomial upper bound `Y ≤ B^3`.

This follows directly from `log B ≤ B` and the defining floor inequality.
-/
theorem terminalPrimeCutoff_le_cube (B : ℕ) :
    terminalPrimeCutoff B ≤ B ^ 3 := by
  have hlog :
      Real.log (B : ℝ) ≤ (B : ℝ) :=
    Real.log_le_self (by positivity)
  have hscale :
      terminalPrimeScale B ≤ (B : ℝ) ^ 3 := by
    calc
      terminalPrimeScale B =
          (B : ℝ) ^ 2 * Real.log (B : ℝ) := rfl
      _ ≤ (B : ℝ) ^ 2 * (B : ℝ) :=
        mul_le_mul_of_nonneg_left hlog (sq_nonneg (B : ℝ))
      _ = (B : ℝ) ^ 3 := by ring
  have hcast :
      (terminalPrimeCutoff B : ℝ) ≤ ((B ^ 3 : ℕ) : ℝ) := by
    calc
      (terminalPrimeCutoff B : ℝ) ≤ terminalPrimeScale B :=
        cast_terminalPrimeCutoff_le_scale B
      _ ≤ (B : ℝ) ^ 3 := hscale
      _ = ((B ^ 3 : ℕ) : ℝ) := by norm_num
  exact_mod_cast hcast

/-- The two finite comparisons used together in later cutoff estimates. -/
theorem cutoff_between_linear_and_cubic {B : ℕ} (hB : 2 ≤ B) :
    B ≤ terminalPrimeCutoff B ∧ terminalPrimeCutoff B ≤ B ^ 3 :=
  ⟨le_terminalPrimeCutoff hB, terminalPrimeCutoff_le_cube B⟩

/--
If a base cutoff already dominates the non-root window, then its terminal
cutoff dominates both.  These are precisely the two numerical inequalities
used by the finite two-cutoff bad-start mass estimate.
-/
theorem badStart_cutoff_comparisons
    {L B : ℕ} (hL : 0 < L) (hLB : L + 1 ≤ B) :
    L + 1 ≤ B ∧ B ≤ terminalPrimeCutoff B := by
  refine ⟨hLB, le_terminalPrimeCutoff ?_⟩
  omega

/-- The terminal cutoff itself dominates the non-root window. -/
theorem window_succ_le_terminalPrimeCutoff
    {L B : ℕ} (hL : 0 < L) (hLB : L + 1 ≤ B) :
    L + 1 ≤ terminalPrimeCutoff B :=
  hLB.trans (badStart_cutoff_comparisons hL hLB).2

/--
The real scale is monotone on positive natural inputs.

This is convenient when a later finite argument enlarges its auxiliary
parameter before taking the cutoff.
-/
theorem terminalPrimeScale_mono {B C : ℕ}
    (hB : 1 ≤ B) (hBC : B ≤ C) :
    terminalPrimeScale B ≤ terminalPrimeScale C := by
  have hBpos : (0 : ℝ) < (B : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hB)
  have hcastBC : (B : ℝ) ≤ (C : ℝ) := by
    exact_mod_cast hBC
  have hlog :
      Real.log (B : ℝ) ≤ Real.log (C : ℝ) :=
    Real.log_le_log hBpos hcastBC
  have hlogNonneg :
      0 ≤ Real.log (B : ℝ) :=
    Real.log_natCast_nonneg B
  have hsq :
      (B : ℝ) ^ 2 ≤ (C : ℝ) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) hcastBC 2
  exact
    mul_le_mul hsq hlog hlogNonneg
      (by positivity : (0 : ℝ) ≤ (C : ℝ) ^ 2)

/-- Consequently, the natural cutoff is monotone on positive inputs. -/
theorem terminalPrimeCutoff_mono {B C : ℕ}
    (hB : 1 ≤ B) (hBC : B ≤ C) :
    terminalPrimeCutoff B ≤ terminalPrimeCutoff C := by
  exact Nat.floor_mono (terminalPrimeScale_mono hB hBC)

end

end TerminalPrimeCutoff
end PaperC
