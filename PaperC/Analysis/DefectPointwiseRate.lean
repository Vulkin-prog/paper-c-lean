import PaperC.Coding.IntervalDefectBound

/-!
# Explicit pointwise rate for interval defects

The finite coding theorem bounds the interval cardinality by a constant
multiple of the floored Runge radius.  This file converts that radius back to
the real quotient `log N / log H`, without invoking asymptotic notation.
-/

namespace PaperC
namespace DefectPointwiseRate

/--
The explicit floored radius is bounded above by `log N / (8 log H)`.
The larger denominator used in its definition only improves this estimate.
-/
theorem cappedRadius_cast_le_log_div
    {N H T : ℕ}
    (hN : 1 ≤ N)
    (hH : 2 ≤ H)
    (hT : 1 ≤ T) :
    (RungeLogarithmicGrowth.cappedRadius N H T : ℝ) ≤
      Real.log N / (8 * Real.log H) := by
  have hHpos : 0 < (H : ℝ) := by positivity
  have hlogHpos : 0 < Real.log (H : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < H by omega)
  have hHcapNat : H ≤ 256 * T * H := by
    have hfactor : 1 ≤ 256 * T := by omega
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      Nat.mul_le_mul_right H hfactor
  have hlogMono :
      Real.log (H : ℝ) ≤ Real.log (256 * T * H : ℝ) := by
    apply Real.log_le_log hHpos
    exact_mod_cast hHcapNat
  have hscaleNonneg :
      0 ≤ (8 * RungeLogarithmicGrowth.cappedRadius N H T : ℝ) := by
    positivity
  have hsmallLog :
      (8 * RungeLogarithmicGrowth.cappedRadius N H T : ℝ) *
          Real.log H ≤
        (8 * RungeLogarithmicGrowth.cappedRadius N H T : ℝ) *
          Real.log (256 * T * H) :=
    mul_le_mul_of_nonneg_left hlogMono hscaleNonneg
  have hdef :
      (8 * RungeLogarithmicGrowth.cappedRadius N H T : ℝ) *
          Real.log (256 * T * H) ≤
        Real.log N :=
    RungeLogarithmicGrowth.cappedRadius_log_condition hN
      (by omega) hT
  apply (le_div_iff₀ (mul_pos (by norm_num) hlogHpos)).2
  calc
    (RungeLogarithmicGrowth.cappedRadius N H T : ℝ) *
          (8 * Real.log H)
        =
        (8 * RungeLogarithmicGrowth.cappedRadius N H T : ℝ) *
          Real.log H := by ring
    _ ≤ Real.log N := hsmallLog.trans hdef

/--
Explicit real pointwise rate for the represented `H`-defects in `[N,N+H]`.

The natural constant `2 * 2^(A+1)` is the finite Hamming loss.  All remaining
hypotheses are the named side conditions of the capped-radius theorem.
-/
theorem card_defectsInInterval_cast_lt_log_div
    {N H T A : ℕ}
    (hH : 4 ≤ H)
    (hN : 2 * H ≤ N)
    (hT : 1 ≤ T)
    (hpositive :
      1 ≤ RungeLogarithmicGrowth.cappedRadius N H T)
    (hbelow :
      RungeLogarithmicGrowth.cappedRadius N H T ≤ T)
    (hbudget :
      (7 * H) / Nat.log 2 H + 1 ≤
        A * RungeLogarithmicGrowth.cappedRadius N H T) :
    ((IntervalDefectBound.defectsInInterval H N).card : ℝ) <
      ((2 * 2 ^ (A + 1) : ℕ) : ℝ) *
        (Real.log N / (8 * Real.log H)) := by
  have hcard :=
    IntervalDefectBound.card_defectsInInterval_lt_of_cappedRadius
      hH hN hT hpositive hbelow hbudget
  have hcardCast :
      ((IntervalDefectBound.defectsInInterval H N).card : ℝ) <
        ((2 * RungeLogarithmicGrowth.cappedRadius N H T *
          2 ^ (A + 1) : ℕ) : ℝ) := by
    exact_mod_cast hcard
  have hradius :=
    cappedRadius_cast_le_log_div (N := N) (H := H) (T := T)
      (by omega) (by omega) hT
  calc
    ((IntervalDefectBound.defectsInInterval H N).card : ℝ)
        <
        ((2 * RungeLogarithmicGrowth.cappedRadius N H T *
          2 ^ (A + 1) : ℕ) : ℝ) := hcardCast
    _ = ((2 * 2 ^ (A + 1) : ℕ) : ℝ) *
          (RungeLogarithmicGrowth.cappedRadius N H T : ℝ) := by
      norm_num
      ring
    _ ≤ ((2 * 2 ^ (A + 1) : ℕ) : ℝ) *
          (Real.log N / (8 * Real.log H)) :=
      mul_le_mul_of_nonneg_left hradius (by positivity)

end DefectPointwiseRate
end PaperC
