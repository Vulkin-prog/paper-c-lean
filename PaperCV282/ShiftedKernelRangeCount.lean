import PaperCV282.ShiftedKernelBoxCount
import PaperCV282.ShiftedKernelQuotients

/-!
# A finite shifted-kernel count in two dyadic ranges

The two kernels are counted together through `q*r+h=q'*s`.
Quotients are counted by the square-times-small-prime container, and
the affine fibre supplies the essential gain in the two kernel ranges.
No asymptotic energy bound or terminal population estimate is assumed.
-/

namespace PaperC.V282.ShiftedKernelRangeCount

open LargeOddKernel DefectCounting ShiftedKernelBoxCount ShiftedKernelQuotients
open scoped BigOperators

noncomputable section

/-- Values whose two shifted kernels lie in the specified dyadic ranges. -/
def shiftedKernelRangeValues (B h X R S : ℕ) : Finset ℕ :=
  (Finset.Ico X (2 * X)).filter fun n =>
    (R ≤ largeOddKernel B n ∧ largeOddKernel B n < 2 * R) ∧
      (S ≤ largeOddKernel B (n + h) ∧ largeOddKernel B (n + h) < 2 * S)

theorem mem_shiftedKernelRangeValues {B h X R S n : ℕ} :
    n ∈ shiftedKernelRangeValues B h X R S ↔
      (X ≤ n ∧ n < 2 * X) ∧
      (R ≤ largeOddKernel B n ∧ largeOddKernel B n < 2 * R) ∧
      (S ≤ largeOddKernel B (n + h) ∧ largeOddKernel B (n + h) < 2 * S) := by
  simp [shiftedKernelRangeValues]

/-- Only second quotients with the correct lower-scale constraint can occur. -/
def admissibleSecondQuotients (B X S : ℕ) : Finset ℕ :=
  (kernelQuotients B (3 * X) S).filter fun q' => 0 < q' ∧ X ≤ 2 * q' * S

/-- A finite overcount by quotient pairs and their affine kernel fibres. -/
def quotientBoxCover (B h X R S : ℕ) : Finset ℕ :=
  (kernelQuotients B (3 * X) R).biUnion fun q =>
    (admissibleSecondQuotients B X S).biUnion fun q' =>
      (boxSolutions q q' h R (2 * R) S (2 * S)).image fun rs => q * rs.1

/-- Every true shifted pair enters the affine cover with its canonical two quotients. -/
theorem shiftedKernelRangeValues_subset_quotientBoxCover
    (B h X R S : ℕ) (hX : 0 < X) (hhX : h ≤ X) :
    shiftedKernelRangeValues B h X R S ⊆ quotientBoxCover B h X R S := by
  intro n hn
  obtain ⟨hnX, hr, hs⟩ := mem_shiftedKernelRangeValues.mp hn
  have hnpos : 0 < n := hX.trans_le hnX.1
  have hnshift : 0 < n + h := by omega
  have hq : kernelQuotient B n ∈ kernelQuotients B (3 * X) R := by
    apply Finset.mem_image.mpr
    exact ⟨n, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hnpos, by omega⟩, hr.1⟩, rfl⟩
  have hq' : kernelQuotient B (n + h) ∈ admissibleSecondQuotients B X S := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, kernelQuotient_pos hnshift, ?_⟩
    · apply Finset.mem_image.mpr
      exact ⟨n + h, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hnshift, by omega⟩, hs.1⟩, rfl⟩
    · calc
        X ≤ n + h := by omega
        _ = kernelQuotient B (n + h) * largeOddKernel B (n + h) :=
          (kernelQuotient_mul_kernel B (n + h)).symm
        _ ≤ kernelQuotient B (n + h) * (2 * S) := Nat.mul_le_mul_left _ hs.2.le
        _ = _ := by ring
  have hbox : (largeOddKernel B n, largeOddKernel B (n + h)) ∈
      boxSolutions (kernelQuotient B n) (kernelQuotient B (n + h)) h R (2 * R) S (2 * S) := by
    apply mem_boxSolutions.mpr
    exact ⟨hr, hs, by simp only [kernelQuotient_mul_kernel]⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨kernelQuotient B n, hq, Finset.mem_biUnion.mpr ?_⟩
  refine ⟨kernelQuotient B (n + h), hq', Finset.mem_image.mpr ?_⟩
  exact ⟨(largeOddKernel B n, largeOddKernel B (n + h)), hbox, kernelQuotient_mul_kernel B n⟩

/-- The canonical cover gives a sum of fibre counts without requiring injectivity of the cover. -/
theorem card_shiftedKernelRangeValues_le_sum_boxes
    (B h X R S : ℕ) (hX : 0 < X) (hhX : h ≤ X) :
    (shiftedKernelRangeValues B h X R S).card ≤
      ∑ q ∈ kernelQuotients B (3 * X) R,
        ∑ q' ∈ admissibleSecondQuotients B X S,
          (boxSolutions q q' h R (2 * R) S (2 * S)).card := by
  classical
  refine (Finset.card_le_card
    (shiftedKernelRangeValues_subset_quotientBoxCover B h X R S hX hhX)).trans ?_
  unfold quotientBoxCover
  refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun q _ => ?_)
  exact Finset.card_biUnion_le.trans (Finset.sum_le_sum fun q' _ => Finset.card_image_le)

/-- Finite pair count in terms of the two quotient populations and one common fibre bound. -/
theorem card_shiftedKernelRangeValues_le_quotient_counts
    (B h X R S : ℕ) (hX : 0 < X) (hh : 0 < h) (hhX : h ≤ X) :
    ((shiftedKernelRangeValues B h X R S).card : ℝ) ≤
      ((kernelQuotients B (3 * X) R).card : ℝ) *
        ((kernelQuotients B (3 * X) S).card : ℝ) *
          (1 + 2 * R * S * h / X) := by
  have hnat := card_shiftedKernelRangeValues_le_sum_boxes B h X R S hX hhX
  have hreal : ((shiftedKernelRangeValues B h X R S).card : ℝ) ≤
      ∑ q ∈ kernelQuotients B (3 * X) R,
        ∑ q' ∈ admissibleSecondQuotients B X S,
          ((boxSolutions q q' h R (2 * R) S (2 * S)).card : ℝ) := by
    exact_mod_cast hnat
  have hsecond : ((admissibleSecondQuotients B X S).card : ℝ) ≤
      ((kernelQuotients B (3 * X) S).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset (fun q' => 0 < q' ∧ X ≤ 2 * q' * S) _)
  calc
    _ ≤ _ := hreal
    _ ≤ ∑ _q ∈ kernelQuotients B (3 * X) R,
        ∑ _q' ∈ admissibleSecondQuotients B X S, (1 + 2 * (R : ℝ) * S * h / X) := by
      apply Finset.sum_le_sum
      intro q _
      apply Finset.sum_le_sum
      intro q' hq'
      obtain ⟨hqpos, hqscale⟩ := (Finset.mem_filter.mp hq').2
      exact card_dyadic_boxSolutions_le q q' h R S X hqpos hh hX hqscale
    _ = ((kernelQuotients B (3 * X) R).card : ℝ) *
        ((admissibleSecondQuotients B X S).card : ℝ) * (1 + 2 * R * S * h / X) := by
      simp [mul_assoc]
      ring
    _ ≤ _ := by gcongr

/-- The finite shifted-kernel estimate in two specified ranges, before any dyadic summation. -/
theorem card_shiftedKernelRangeValues_le_sqrt_fibres
    (B h X R S : ℕ) (hX : 0 < X) (hh : 0 < h) (hhX : h ≤ X)
    (hR : 0 < R) (hS : 0 < S) :
    ((shiftedKernelRangeValues B h X R S).card : ℝ) ≤
      4 * Real.sqrt ((3 * X : ℝ) / R) * Real.sqrt ((3 * X : ℝ) / S) *
        (∏ p ∈ smallPrimesUpTo B, (1 + (Real.sqrt p)⁻¹)) ^ 2 *
          (1 + 2 * R * S * h / X) := by
  have hfirst := card_kernelQuotients_le_sqrt_ratio B (3 * X) R hR
  have hsecond := card_kernelQuotients_le_sqrt_ratio B (3 * X) S hS
  have hW : 0 ≤ ∏ p ∈ smallPrimesUpTo B, (1 + (Real.sqrt p)⁻¹) := by positivity
  refine (card_shiftedKernelRangeValues_le_quotient_counts B h X R S hX hh hhX).trans ?_
  calc
    _ ≤ (2 * Real.sqrt ((3 * X : ℕ) / (R : ℝ)) *
          ∏ p ∈ smallPrimesUpTo B, (1 + (Real.sqrt p)⁻¹)) *
        (2 * Real.sqrt ((3 * X : ℕ) / (S : ℝ)) *
          ∏ p ∈ smallPrimesUpTo B, (1 + (Real.sqrt p)⁻¹)) *
        (1 + 2 * R * S * h / X) := by gcongr
    _ = _ := by push_cast; ring

end
end PaperC.V282.ShiftedKernelRangeCount
