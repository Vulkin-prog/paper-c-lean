import PaperCV282.ShiftedKernelDyadicCover
import PaperCV282.SmallKernelAnchors
import PaperCV282.KernelWindowEnergy

/-!
# Complete small-kernel pair counts on a dyadic value slice

The low-kernel branch is anchored by either occurrence. The high branch
is the exhaustive two-range sum. Their combination retains all shifted
pairs, with threshold before the shift and kernel cap.
-/

namespace PaperC.V282.ShiftedKernelPairCount

open LargeOddKernel TerminalKernelCount SmallKernelAnchors
open ShiftedKernelDyadicCover KernelWindowEnergy LogarithmicWordPowers

noncomputable section

/-- A finite partition bound with either low occurrence and the high-pair cover. -/
theorem card_shiftedKernelValues_le_low_add_high
    {B T X h : ℕ} (hhX : h ≤ X) :
    (shiftedKernelValues B T X (2 * X) h).card ≤
      2 * (boundedLargeKernelValues B ⌊(X : ℝ) ^ (1 / (3 : ℝ))⌋₊ (3 * X)).card +
        (highShiftedKernelValues B T X h).card := by
  classical
  let low := boundedLargeKernelValues B ⌊(X : ℝ) ^ (1 / (3 : ℝ))⌋₊ (3 * X)
  let other := (Finset.Ico X (2 * X)).filter fun n => n + h ∈ low
  have hsecond : other.card ≤ low.card := by
    apply Finset.card_le_card_of_injOn (fun n => n + h)
    · intro n hn
      exact (Finset.mem_filter.mp hn).2
    · intro n hn m hm heq
      exact Nat.add_right_cancel heq
  have hcover : shiftedKernelValues B T X (2 * X) h ⊆
      low ∪ other ∪ highShiftedKernelValues B T X h := by
    intro n hn
    obtain ⟨hnX, hr, hs⟩ := Finset.mem_filter.mp hn
    have hnX' := Finset.mem_Ico.mp hnX
    by_cases hrlo : largeOddKernel B n ≤ ⌊(X : ℝ) ^ (1 / (3 : ℝ))⌋₊
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (mem_boundedLargeKernelValues.mpr ⟨by omega, by omega, hrlo⟩))
    by_cases hslo : largeOddKernel B (n + h) ≤ ⌊(X : ℝ) ^ (1 / (3 : ℝ))⌋₊
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hnX, mem_boundedLargeKernelValues.mpr ⟨by omega, by omega, hslo⟩⟩))
    · apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨hnX,
        ⟨Nat.ceil_le.mpr (Nat.lt_of_floor_lt (by omega)).le, hr⟩,
        ⟨Nat.ceil_le.mpr (Nat.lt_of_floor_lt (by omega)).le, hs⟩⟩
  have hc := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  have hu := Finset.card_union_le (s := low) (t := other)
  dsimp only [low] at *
  omega

/-- Every shifted pair with two kernels below the terminal cap has the two-thirds count. -/
theorem card_shiftedKernelValues_le_two_thirds_eventually
    (C D epsilon : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hepsilon : 0 < epsilon) :
    ∃ Xzero : ℕ, ∀ X ≥ Xzero, ∀ L : ℕ,
      (L + 1 : ℝ) ≤ C * Real.log X → ∀ T h : ℕ,
      0 < h → h ≤ L + 1 →
      (T : ℝ) ≤ D * Real.sqrt ((X : ℝ) * (L + 1)) →
      ((shiftedKernelValues (L + 1) T X (2 * X) h).card : ℝ) ≤
        (X : ℝ) ^ (2 / (3 : ℝ) + epsilon) := by
  have heps : 0 < epsilon / 2 := by positivity
  obtain ⟨Xlow, hlow⟩ := card_smallKernelAnchors_le_two_thirds_eventually C (epsilon / 2) hC heps
  obtain ⟨Xhigh, hhigh⟩ := card_highShiftedKernelValues_le_two_thirds_eventually C D (epsilon / 2) hC hD heps
  obtain ⟨Xconstant, hconstant⟩ := polynomial_factor_le_rpow_eventually C hC 3 0 (epsilon / 2) heps
  obtain ⟨Xlength, hlength⟩ := MacroscopicCanonicalCode.logarithmic_power_lt_rpow_eventually
    C 1 hC (by norm_num) 1 (by omega)
  refine ⟨max Xlow (max Xhigh (max Xconstant (max Xlength 1))), ?_⟩
  intro X hX L hL T h hh hhB hT
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hl := hlength X (by omega) (L + 1) (by simpa using hL)
  have hhX : h ≤ X := by
    simp only [pow_one, Real.rpow_one, Nat.cast_add, Nat.cast_one] at hl
    have hhreal : (h : ℝ) ≤ L + 1 := by exact_mod_cast hhB
    exact_mod_cast (show (h : ℝ) ≤ X by linarith)
  have hfinite := card_shiftedKernelValues_le_low_add_high (B := L + 1) (T := T) hhX
  have hlo := hlow X (by omega) L hL ⌊(X : ℝ) ^ (1 / (3 : ℝ))⌋₊ (Nat.floor_le (by positivity))
  have hhi := hhigh X (by omega) L hL T h hh hhB hT
  have hthree : (3 : ℝ) ≤ (X : ℝ) ^ (epsilon / 2) := by
    simpa using hconstant X (by omega) L (by simpa using hL)
  have hpower : (X : ℝ) ^ (epsilon / 2) * (X : ℝ) ^ (2 / (3 : ℝ)) =
      (X : ℝ) ^ (2 / (3 : ℝ) + epsilon / 2) := by
    rw [← Real.rpow_add hXpos]; congr 1; ring
  rw [hpower] at hlo
  have hf : ((shiftedKernelValues (L + 1) T X (2 * X) h).card : ℝ) ≤
      3 * (X : ℝ) ^ (2 / (3 : ℝ) + epsilon / 2) := by
    have hcast : ((shiftedKernelValues (L + 1) T X (2 * X) h).card : ℝ) ≤
      2 * ((boundedLargeKernelValues (L + 1) ⌊(X : ℝ) ^ (1 / (3 : ℝ))⌋₊ (3 * X)).card : ℝ) +
        ((highShiftedKernelValues (L + 1) T X h).card : ℝ) := by exact_mod_cast hfinite
    linarith
  calc
    _ ≤ _ := hf
    _ ≤ (X : ℝ) ^ (epsilon / 2) * (X : ℝ) ^ (2 / (3 : ℝ) + epsilon / 2) :=
      mul_le_mul_of_nonneg_right hthree (by positivity)
    _ = _ := by rw [← Real.rpow_add hXpos]; congr 1; ring

end
end PaperC.V282.ShiftedKernelPairCount
