import PaperCV282.CutoffGraphDegree
import PaperCV282.PrimeEulerCutoff

/-!
# Exponential-cutoff degree and edge envelopes

The literal floor(exp w) remains in the graph definitions. Its rounding
is discharged explicitly, producing exp(-w) plus the finite-size 1/N term.
All estimates hold on arbitrary masks and include exceptional starts.
-/

namespace PaperC.V282.CutoffGraphScale

open CutoffGraphDegree PrimeEulerCutoff MaskedPairGeometry

noncomputable section

/-- The finite numeric effect of rounding the exponentially large cutoff. -/
theorem floor_cutoff_envelope_le {N L : ℕ} (hN : 2 ≤ N) {w : ℝ} (hw : Real.log 4 ≤ w) :
    (L + 1 : ℝ) ^ 2 * (Real.log (3 * N : ℕ) / Real.log (⌊Real.exp w⌋₊ : ℕ)) *
        (1 / (⌊Real.exp w⌋₊ : ℝ) + 1 / N) ≤
      (L + 1 : ℝ) ^ 2 * (Real.log (3 * N : ℕ) / (w - Real.log 2)) *
        (2 * Real.exp (-w) + 1 / N) := by
  have hlogN : 0 ≤ Real.log (3 * N : ℕ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 3 * N by omega))
  have hgap : 0 < w - Real.log 2 := by
    have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogfour : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith
  have hlog := (floor_exp_bounds hw).2.2.2
  have hratio : Real.log (3 * N : ℕ) / Real.log (⌊Real.exp w⌋₊ : ℕ) ≤
      Real.log (3 * N : ℕ) / (w - Real.log 2) :=
    div_le_div_of_nonneg_left hlogN hgap hlog
  have hinv := inv_floor_exp_le_two_exp_neg hw
  have hratio0 : 0 ≤ Real.log (3 * N : ℕ) / Real.log (⌊Real.exp w⌋₊ : ℕ) :=
    div_nonneg hlogN (hgap.trans_le hlog).le
  have hnext0 : 0 ≤ Real.log (3 * N : ℕ) / (w - Real.log 2) := div_nonneg hlogN hgap.le
  gcongr

/-- Companion (B.3) at the exact discretized cutoff, normalized by the ambient population. -/
theorem normalized_cutoffMaxDegree_floor_exp_le {N L : ℕ} (hN : 2 ≤ N) (hL : L ≤ N)
    {w : ℝ} (hw : Real.log 4 ≤ w) (hLY : L ≤ ⌊Real.exp w⌋₊)
    {mask : Finset ℕ} (hmask : mask ⊆ dyadicBlock N) :
    (cutoffMaxDegree L ⌊Real.exp w⌋₊ mask : ℝ) / N ≤
      (L + 1 : ℝ) ^ 2 * (Real.log (3 * N : ℕ) / (w - Real.log 2)) *
        (2 * Real.exp (-w) + 1 / N) := by
  have hY : 1 < ⌊Real.exp w⌋₊ := by have := (floor_exp_bounds hw).1; omega
  exact (normalized_cutoffMaxDegree_le hN hL hLY hY hmask).trans (floor_cutoff_envelope_le hN hw)

/-- The identical cutoff envelope for the ordered edges on every mask. -/
theorem normalized_maskedSupportEdges_floor_exp_le {N L : ℕ} (hN : 2 ≤ N) (hL : L ≤ N)
    {w : ℝ} (hw : Real.log 4 ≤ w) (hLY : L ≤ ⌊Real.exp w⌋₊)
    {mask : Finset ℕ} (hmask : mask ⊆ dyadicBlock N) :
    ((maskedSupportEdges L ⌊Real.exp w⌋₊ mask).card : ℝ) / (N : ℝ) ^ 2 ≤
      (L + 1 : ℝ) ^ 2 * (Real.log (3 * N : ℕ) / (w - Real.log 2)) *
        (2 * Real.exp (-w) + 1 / N) := by
  have hY : 1 < ⌊Real.exp w⌋₊ := by have := (floor_exp_bounds hw).1; omega
  exact (normalized_maskedSupportEdges_le hN hL hLY hY hmask).trans (floor_cutoff_envelope_le hN hw)

end
end PaperC.V282.CutoffGraphScale
