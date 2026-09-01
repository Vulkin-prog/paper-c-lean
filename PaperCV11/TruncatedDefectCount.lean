import PaperC.Arithmetic.TerminalKernelCount

/-!
# Paper C v1.1: exact truncation in the defect count

The retained v1.0 envelope extended the squarefree-support sum to a full Euler
product at exponent `1/2`. Proposition 3.3 keeps the natural restriction that
the product of the selected small primes is at most the height `X` before
applying Rankin's trick.

This file isolates that exact finite statement from the already formalized
canonical kernel decomposition. No asymptotic estimate and no new external
input is used here.
-/

namespace PaperC
namespace V11
namespace TruncatedDefectCount

open scoped BigOperators

open DefectCounting
open TerminalKernelCount

/-- Small-prime supports whose squarefree product can occur below `X`. -/
noncomputable def admissibleSmallSupports
    (B X : ℕ) : Finset (Finset ℕ) :=
  (smallPrimesUpTo B).powerset.filter fun small ↦
    small.prod id ≤ X

@[simp]
theorem mem_admissibleSmallSupports
    {B X : ℕ} {small : Finset ℕ} :
    small ∈ admissibleSmallSupports B X ↔
      small ⊆ smallPrimesUpTo B ∧ small.prod id ≤ X := by
  simp [admissibleSmallSupports]

/-- At terminal-kernel threshold `1`, the existing sigma count has one fibre. -/
theorem card_kernel_one_le_unfiltered_sqrt_sum
    (B X : ℕ) :
    (boundedLargeKernelValues B 1 X).card ≤
      ∑ small ∈ (smallPrimesUpTo B).powerset,
        Nat.sqrt (X / small.prod id) := by
  simpa using card_boundedLargeKernelValues_le_sqrt_sum B 1 X

/-- Supports of product greater than `X` contribute a zero square-root fibre. -/
theorem sqrt_div_prod_eq_zero_of_not_admissible
    {B X : ℕ} {small : Finset ℕ}
    (hsmall : small ∈ (smallPrimesUpTo B).powerset)
    (hnot : small ∉ admissibleSmallSupports B X) :
    Nat.sqrt (X / small.prod id) = 0 := by
  have hle : ¬ small.prod id ≤ X := by
    intro hprod
    exact hnot (by
      simp only [admissibleSmallSupports, Finset.mem_filter]
      exact ⟨hsmall, hprod⟩)
  have hlt : X < small.prod id := Nat.lt_of_not_ge hle
  rw [Nat.div_eq_of_lt hlt]
  simp

/-- The unfiltered square-root sum is exactly its admissible restriction. -/
theorem sqrt_sum_eq_admissible_sum
    (B X : ℕ) :
    (∑ small ∈ (smallPrimesUpTo B).powerset,
        Nat.sqrt (X / small.prod id)) =
      ∑ small ∈ admissibleSmallSupports B X,
        Nat.sqrt (X / small.prod id) := by
  classical
  rw [admissibleSmallSupports, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro small hsmall
  by_cases hprod : small.prod id ≤ X
  · rw [if_pos hprod]
  · rw [if_neg hprod]
    have hlt : X < small.prod id := Nat.lt_of_not_ge hprod
    rw [Nat.div_eq_of_lt hlt]
    simp

/--
Exact truncated finite reduction for the defective-integer count. The set on
the left consists of positive integers at most `X` whose large odd kernel
above `B` is `1`.
-/
theorem sharpKernelDefectFiniteReduction
    (B X : ℕ) :
    (boundedLargeKernelValues B 1 X).card ≤
      ∑ small ∈ admissibleSmallSupports B X,
        Nat.sqrt (X / small.prod id) := by
  rw [← sqrt_sum_eq_admissible_sum B X]
  exact card_kernel_one_le_unfiltered_sqrt_sum B X

end TruncatedDefectCount
end V11
end PaperC
