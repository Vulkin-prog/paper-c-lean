import PaperCV282.PrimeEulerRankin
import PaperCV282.MaskedArithmeticGeometry

/-!
# Rankin bounds for the actual whole-support deletion set

A defective vertex contaminates at most B=L+1 windows, including the left
boundary x-1. The deletion population is exactly the common fullBadStarts
and its intersection with the user's deterministic mask. No regularity or
density hypothesis on the mask is required for ambient normalization.
-/

namespace PaperC.V282.BadStartRankin

open DefectivePredicate DefectiveRankinCount PrimeEulerRankin MaskedArithmeticGeometry
open LargePrimeDependencyGraph

noncomputable section

/-- A complete-tree vertex has a literal offset between zero and L, including the root. -/
theorem tree_vertex_eq_complete_offset {x L n : ℕ} (hx : 1 ≤ x)
    (hn : n ∈ startTreeSupport x L) : ∃ i : ℕ, i < L + 1 ∧ n = x - 1 + i := by
  rcases mem_startTreeSupport.mp hn with hr | ⟨j, hj, heq⟩
  · exact ⟨0, by omega, by omega⟩
  · exact ⟨j + 1, by omega, by omega⟩

/-- Every bad start is reconstructed from a defective integer and one of B offsets. -/
theorem fullBadStarts_subset_offset_cover {N L Y : ℕ} (hN : 2 ≤ N) (hL : L ≤ N) :
    fullBadStarts N L Y ⊆ (Finset.range (L + 1)).biUnion
      (fun i => (defectiveValues (3 * N) Y).image fun n => n + 1 - i) := by
  intro x hx
  obtain ⟨hxblock, n, hn, hd⟩ := mem_fullBadStarts.mp hx
  obtain ⟨hxN, hx2N⟩ := Finset.mem_Ico.mp hxblock
  obtain ⟨i, hi, heq⟩ := tree_vertex_eq_complete_offset (by omega) hn
  have hnmem : n ∈ defectiveValues (3 * N) Y :=
    mem_defectiveValues.mpr ⟨by omega, by omega, hd⟩
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi,
    Finset.mem_image.mpr ⟨n, hnmem, by omega⟩⟩

/-- The exact finite contamination factor is the full number B of vertices. -/
theorem card_fullBadStarts_le_defectiveValues {N L Y : ℕ} (hN : 2 ≤ N) (hL : L ≤ N) :
    (fullBadStarts N L Y).card ≤ (L + 1) * (defectiveValues (3 * N) Y).card := by
  calc
    _ ≤ ((Finset.range (L + 1)).biUnion
        (fun i => (defectiveValues (3 * N) Y).image fun n => n + 1 - i)).card :=
      Finset.card_le_card (fullBadStarts_subset_offset_cover hN hL)
    _ ≤ ∑ i ∈ Finset.range (L + 1), ((defectiveValues (3 * N) Y).image fun n => n + 1 - i).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ Finset.range (L + 1), (defectiveValues (3 * N) Y).card :=
      Finset.sum_le_sum fun _ _ => Finset.card_image_le
    _ = _ := by simp

/-- The same contamination bound holds for every deterministic deletion mask. -/
theorem card_fullBadMask_le_defectiveValues {N L Y : ℕ} (hN : 2 ≤ N) (hL : L ≤ N)
    (mask : Finset ℕ) :
    (fullBadMask N L Y mask).card ≤ (L + 1) * (defectiveValues (3 * N) Y).card := by
  exact (Finset.card_le_card (Finset.inter_subset_right : fullBadMask N L Y mask ⊆ fullBadStarts N L Y)).trans
    (card_fullBadStarts_le_defectiveValues hN hL)

/-- Finite masked Rankin bound, with the complete support and exact scale 3N. -/
theorem card_fullBadMask_le_rankin {N L Y : ℕ} (hN : 2 ≤ N) (hL : L ≤ N)
    (mask : Finset ℕ) {zeta : ℝ} (hzeta : zeta ≤ 1 / 2) :
    ((fullBadMask N L Y mask).card : ℝ) ≤
      (L + 1 : ℝ) * ((3 * N : ℕ) : ℝ) ^ (1 - zeta) * rankinEulerProduct Y zeta := by
  have hfinite : ((fullBadMask N L Y mask).card : ℝ) ≤
      (L + 1 : ℝ) * ((defectiveValues (3 * N) Y).card : ℝ) := by
    exact_mod_cast card_fullBadMask_le_defectiveValues hN hL mask
  exact hfinite.trans (by simpa only [mul_assoc] using
    (mul_le_mul_of_nonneg_left (card_defectiveValues_le_rankin (3 * N) Y hzeta)
      (by positivity : (0 : ℝ) ≤ L + 1)))

/-- Ambient normalization retains the exact factor 3B, uniformly over all masks. -/
theorem normalized_fullBadMask_le_rankin {N L Y : ℕ} (hN : 2 ≤ N) (hL : L ≤ N)
    (mask : Finset ℕ) {zeta : ℝ} (hzeta : zeta ≤ 1 / 2) :
    ((fullBadMask N L Y mask).card : ℝ) / N ≤
      3 * (L + 1 : ℝ) * ((3 * N : ℕ) : ℝ) ^ (-zeta) * rankinEulerProduct Y zeta := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h3Nr : (0 : ℝ) < (3 * N : ℕ) := by positivity
  have hfinite : ((fullBadMask N L Y mask).card : ℝ) ≤
      (L + 1 : ℝ) * ((defectiveValues (3 * N) Y).card : ℝ) := by
    exact_mod_cast card_fullBadMask_le_defectiveValues hN hL mask
  calc
    _ ≤ ((L + 1 : ℝ) * ((defectiveValues (3 * N) Y).card : ℝ)) / N :=
      div_le_div_of_nonneg_right hfinite hNr.le
    _ = (3 * (L + 1 : ℝ)) * (((defectiveValues (3 * N) Y).card : ℝ) / (3 * N : ℕ)) := by
      push_cast
      field_simp
    _ ≤ (3 * (L + 1 : ℝ)) * (((3 * N : ℕ) : ℝ) ^ (-zeta) * rankinEulerProduct Y zeta) :=
      mul_le_mul_of_nonneg_left (normalized_defectiveValues_le_rankin (by omega) Y hzeta) (by positivity)
    _ = _ := by ring

/-- Logarithmic-exponent form, isolating the only remaining weighted-prime main term. -/
theorem normalized_fullBadMask_le_exp {N L Y : ℕ} (hN : 2 ≤ N) (hL : L ≤ N)
    (mask : Finset ℕ) {zeta : ℝ} (hzeta : zeta ≤ 1 / 2) :
    ((fullBadMask N L Y mask).card : ℝ) / N ≤
      Real.exp (Real.log (3 * (L + 1 : ℝ)) - zeta * Real.log (3 * N : ℕ) + rankinLogSum Y zeta) := by
  have hNr : (0 : ℝ) < (3 * N : ℕ) := by exact_mod_cast (show 0 < 3 * N by omega)
  calc
    _ ≤ 3 * (L + 1 : ℝ) * ((3 * N : ℕ) : ℝ) ^ (-zeta) * rankinEulerProduct Y zeta :=
      normalized_fullBadMask_le_rankin hN hL mask hzeta
    _ = _ := by
      rw [rankinEulerProduct_eq_exp, Real.rpow_def_of_pos hNr,
        ← Real.exp_log (by positivity : 0 < 3 * (L + 1 : ℝ)), ← Real.exp_add, ← Real.exp_add]
      simp only [Real.log_exp]
      congr 1
      ring

/-- The full dyadic deletion set is recovered by choosing the ambient block as mask. -/
theorem normalized_fullBadStarts_le_exp {N L Y : ℕ} (hN : 2 ≤ N) (hL : L ≤ N)
    {zeta : ℝ} (hzeta : zeta ≤ 1 / 2) :
    ((fullBadStarts N L Y).card : ℝ) / N ≤
      Real.exp (Real.log (3 * (L + 1 : ℝ)) - zeta * Real.log (3 * N : ℕ) + rankinLogSum Y zeta) := by
  have heq : fullBadMask N L Y (dyadicBlock N) = fullBadStarts N L Y :=
    Finset.inter_eq_right.mpr (fullBadStarts_subset_block N L Y)
  have h := normalized_fullBadMask_le_exp (Y := Y) hN hL (dyadicBlock N) hzeta
  rw [heq] at h
  exact h

end
end PaperC.V282.BadStartRankin
