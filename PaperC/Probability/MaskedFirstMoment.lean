import PaperC.Probability.BadStartMass

/-!
# First moment under a deterministic mask

This is the exact finite-cylinder core of Proposition 14.1.  For every
deterministic mask `A ⊆ I_N`, the error in the masked first moment is bounded
by the same full-block defect mass as in the unmasked problem.  Restricting
the set of starts cannot increase the nonnegative error majorant.

No asymptotic notation is used here.  Inserting Proposition 3.2 at
`B = L+1` supplies the uniform masked estimate from the manuscript.
-/

namespace PaperC
namespace MaskedFirstMoment

open scoped BigOperators

open Affine
open BadStartMass

noncomputable section

/-- Expected number of starts whose index belongs to a deterministic mask. -/
def maskedDyadicExpectation
    (N L : ℕ) (mask : Finset ℕ) : ℚ :=
  ∑ x ∈ mask, startProbability N L x

/-- The baseline sum over a mask is its cardinality times `2^-L`. -/
theorem sum_baseline_over_mask
    (L : ℕ) (mask : Finset ℕ) :
    (∑ _x ∈ mask, (1 : ℚ) / (2 : ℚ) ^ L) =
      (mask.card : ℚ) / (2 : ℚ) ^ L := by
  rw [Finset.sum_const, nsmul_eq_mul]
  ring

/--
Uniform finite masked first-moment estimate.  The right-hand side is the
full-block cutoff-`B` defect mass, independent of the chosen mask.
-/
theorem abs_maskedDyadicExpectation_sub_baseline_le
    {N L B : ℕ} {mask : Finset ℕ}
    (hN : 2 ≤ N) (hL : 0 < L)
    (hLB : L + 1 ≤ B)
    (hmask : mask ⊆ dyadicBlock N) :
    |maskedDyadicExpectation N L mask -
        (mask.card : ℚ) / (2 : ℚ) ^ L| ≤
      terminalDefectWeightMass N L B / (2 : ℚ) ^ L := by
  let w : ℕ → ℚ := fun x ↦
    (((2 : ℕ) ^ (startDefectIndicesAt B x L).card - 1 : ℕ) : ℚ)
  have hpoint :
      ∀ x ∈ mask,
        |startProbability N L x - (1 : ℚ) / (2 : ℚ) ^ L| ≤
          w x / (2 : ℚ) ^ L := by
    intro x hx
    apply DefectFirstMoment.abs_startProbability_sub_baseline_le
      N L x (startDefectIndicesAt B x L).card hL
    exact relationRho_startSystem_le_card_startDefectIndicesAt
      hN (hmask hx) hL hLB
  have hsubset :
      (∑ x ∈ mask, w x / (2 : ℚ) ^ L) ≤
        ∑ x ∈ dyadicBlock N, w x / (2 : ℚ) ^ L := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hmask
    intro x hx hnot
    exact div_nonneg (by
      dsimp only [w]
      positivity) (by positivity)
  calc
    |maskedDyadicExpectation N L mask -
        (mask.card : ℚ) / (2 : ℚ) ^ L| =
        |∑ x ∈ mask,
          (startProbability N L x - (1 : ℚ) / (2 : ℚ) ^ L)| := by
      rw [maskedDyadicExpectation, ← sum_baseline_over_mask,
        Finset.sum_sub_distrib]
    _ ≤ ∑ x ∈ mask,
        |startProbability N L x - (1 : ℚ) / (2 : ℚ) ^ L| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ mask, w x / (2 : ℚ) ^ L := by
      exact Finset.sum_le_sum hpoint
    _ ≤ ∑ x ∈ dyadicBlock N, w x / (2 : ℚ) ^ L :=
      hsubset
    _ = terminalDefectWeightMass N L B / (2 : ℚ) ^ L := by
      simp only [terminalDefectWeightMass, w]
      rw [Finset.sum_div]

end

end MaskedFirstMoment
end PaperC
