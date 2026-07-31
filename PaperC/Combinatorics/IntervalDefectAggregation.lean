import Mathlib.Algebra.BigOperators.Ring.Finset
import PaperC.Arithmetic.DefectCounting

/-!
# Aggregating defect counts over sliding intervals

This file records the elementary double-counting step at the end of (3.4).
For a finite set `defects`, the local count at the starting point `u` is the
number of defects in the integer interval `[u, u + H]`.  Summing those local
counts over `starts` is the same as summing, over the defects, the number of
intervals that contain each one.

Together with the overlap bound from `DefectCounting`, this also controls the
weighted mass `∑ (2 ^ localCount - 1)` whenever all local counts have a common
upper bound.
-/

namespace PaperC
namespace IntervalDefectAggregation

open scoped BigOperators

/-- Defects lying in the integer interval `[u, u + H]`. -/
def defectsInInterval (defects : Finset ℕ) (H u : ℕ) : Finset ℕ :=
  defects.filter (fun n ↦ u ≤ n ∧ n ≤ u + H)

/-- Number of defects lying in the integer interval `[u, u + H]`. -/
def localCount (defects : Finset ℕ) (H u : ℕ) : ℕ :=
  (defectsInInterval defects H u).card

@[simp]
theorem mem_defectsInInterval
    {defects : Finset ℕ} {H u n : ℕ} :
    n ∈ defectsInInterval defects H u ↔
      n ∈ defects ∧ u ≤ n ∧ n ≤ u + H := by
  simp [defectsInInterval]

/--
Double counting the incidence relation
`u ∈ starts ∧ n ∈ defects ∧ u ≤ n ≤ u + H`.
-/
theorem sum_localCount_eq_sum_intervalStartsContaining
    (defects starts : Finset ℕ) (H : ℕ) :
    ∑ u ∈ starts, localCount defects H u =
      ∑ n ∈ defects,
        (DefectCounting.intervalStartsContaining starts H n).card := by
  classical
  simp only [localCount, defectsInInterval, Finset.card_eq_sum_ones,
    DefectCounting.intervalStartsContaining]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]

/--
The total local defect count is at most `H + 1` times the global number of
defects.
-/
theorem sum_localCount_le
    (defects starts : Finset ℕ) (H : ℕ) :
    ∑ u ∈ starts, localCount defects H u ≤
      (H + 1) * defects.card := by
  rw [sum_localCount_eq_sum_intervalStartsContaining]
  calc
    ∑ n ∈ defects,
        (DefectCounting.intervalStartsContaining starts H n).card
        ≤ ∑ _n ∈ defects, (H + 1) := by
          exact Finset.sum_le_sum fun n _hn ↦
            DefectCounting.card_intervalStartsContaining_le starts H n
    _ = (H + 1) * defects.card := by
      simp [Nat.mul_comm]

/--
For `m ≤ M`, the shifted dyadic weight `2^m - 1` is bounded by
`m * 2^M`.  The factor `m` is what lets the overlap estimate, rather than the
number of possible starting points, control the weighted sum.
-/
theorem two_pow_sub_one_le_mul
    {m M : ℕ} (hmM : m ≤ M) :
    2 ^ m - 1 ≤ m * 2 ^ M := by
  cases m with
  | zero => simp
  | succ m =>
      calc
        2 ^ (m + 1) - 1 ≤ 2 ^ (m + 1) := Nat.sub_le _ _
        _ ≤ 2 ^ M := Nat.pow_le_pow_right (by omega) hmM
        _ = 1 * 2 ^ M := by simp
        _ ≤ (m + 1) * 2 ^ M := by
          simpa [Nat.succ_eq_add_one] using
            Nat.le_mul_of_pos_left (2 ^ M) (Nat.succ_pos m)

/--
Weighted form of the interval aggregation estimate.  If each interval
contains at most `M` defects, then

`∑_{u ∈ starts} (2 ^ localCount(u) - 1)
  ≤ (H + 1) * defects.card * 2 ^ M`.
-/
theorem sum_two_pow_localCount_sub_one_le
    (defects starts : Finset ℕ) (H M : ℕ)
    (hlocal : ∀ u ∈ starts, localCount defects H u ≤ M) :
    ∑ u ∈ starts, (2 ^ localCount defects H u - 1) ≤
      (H + 1) * defects.card * 2 ^ M := by
  calc
    ∑ u ∈ starts, (2 ^ localCount defects H u - 1)
        ≤ ∑ u ∈ starts, localCount defects H u * 2 ^ M := by
          exact Finset.sum_le_sum fun u hu ↦
            two_pow_sub_one_le_mul (hlocal u hu)
    _ = (∑ u ∈ starts, localCount defects H u) * 2 ^ M := by
      rw [Finset.sum_mul]
    _ ≤ ((H + 1) * defects.card) * 2 ^ M :=
      Nat.mul_le_mul_right (2 ^ M) (sum_localCount_le defects starts H)

end IntervalDefectAggregation
end PaperC
