import PaperCV282.MacroscopicFirstMoment
import PaperC.Probability.BadStartMass

/-! # Independent logarithmic window width and defect threshold

The common maximum encloses the actual window and enlarges its permitted
prime threshold. The original pointwise and weighted bounds therefore apply
uniformly before either independent parameter is selected.
-/

namespace PaperC.V282.IndependentDefectParameters

open WindowValues MacroscopicGeometry MacroscopicFirstMoment
open MacroscopicPointwiseDefects
open scoped BigOperators

noncomputable section

/-- Simultaneous monotonicity in the threshold and the number of vertices. -/
theorem card_defects_mono {H B K x : ℕ} (hH : H ≤ K) (hB : B ≤ K) :
    (defectIndices H x B).card ≤ (defectIndices K x K).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun i : Fin B => (⟨i.val, lt_of_lt_of_le i.isLt hB⟩ : Fin K))
  · intro i hi
    have hd : DefectivePredicate.HDefective H (vertex x B i) := by
      simpa [defectIndices] using hi
    have ht := BadStartMass.hDefective_mono hH hd
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩
  · intro i _ j _ hij
    apply Fin.ext
    exact congrArg (fun k : Fin K => k.val) hij

/-- Both independent parameters may be chosen in the same fixed logarithmic band. -/
theorem pointwise_defects_independent_eventually
    (lo hi delta : ℝ) (hlo : 0 < lo) (hband : lo < hi) (hdelta : 0 < delta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ H B : ℕ,
      lo * Real.log M ≤ (H : ℝ) → (H : ℝ) ≤ hi * Real.log M →
      lo * Real.log M ≤ (B : ℝ) → (B : ℝ) ≤ hi * Real.log M →
      ∀ x ∈ macroscopicStarts M delta,
        ((defectIndices H x B).card : ℝ) ≤
          C * (Real.log M / Real.log (Real.log M)) := by
  obtain ⟨C,hC,Mzero,hpoint⟩ := root_defects_log_bound_eventually lo hi delta hlo hband hdelta
  refine ⟨C,hC,Mzero,?_⟩
  intro M hM H B hHl hHu _hBl hBu x hx
  have hm : ((defectIndices H x B).card : ℝ) ≤
      ((defectIndices (max H B) x (max H B)).card : ℝ) := by
    exact_mod_cast card_defects_mono (le_max_left H B) (le_max_right H B) (x := x)
  have he : ((defectIndices (max H B) x (max H B)).card : ℝ) ≤
      ((IntervalDefectBound.defectsInInterval (max H B) (x - 1)).card : ℝ) := by
    exact_mod_cast card_fullDefects_le_root_interval x (max H B)
  exact hm.trans (he.trans (hpoint M hM (max H B)
    (hHl.trans (by exact_mod_cast le_max_left H B))
    (by exact_mod_cast (max_le hHu hBu)) x hx))

/-- The sentence after (2.4): true weighted defects with independent width and cutoff. -/
theorem weighted_defects_independent_eventually
    (lo hi delta epsilon : ℝ) (hlo : 0 < lo) (hband : lo < hi)
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ H B : ℕ,
      lo * Real.log M ≤ (H : ℝ) → (H : ℝ) ≤ hi * Real.log M →
      lo * Real.log M ≤ (B : ℝ) → (B : ℝ) ≤ hi * Real.log M →
      ∀ s : Finset ℕ, s ⊆ macroscopicStarts M delta →
        (∑ x ∈ s, ((2 : ℝ) ^ (defectIndices H x B).card - 1)) ≤
          (M : ℝ) ^ (1 / (2 : ℝ) + epsilon) := by
  obtain ⟨Mzero,hweight⟩ := sum_fullDefectWeight_le_half_power_eventually
    lo hi delta epsilon hlo hband hdelta hepsilon
  refine ⟨max Mzero 2,?_⟩
  intro M hM H B hHl hHu _hBl hBu s hs
  have hpos : 0 < max H B := by
    have hlog : 0 < Real.log M := Real.log_pos (by exact_mod_cast (show 1 < M by omega))
    have hp : (0 : ℝ) < H := lt_of_lt_of_le (mul_pos hlo hlog) hHl
    have : 0 < H := by exact_mod_cast hp
    omega
  have heq : max H B - 1 + 1 = max H B := by omega
  have hf := hweight M (by omega) (max H B - 1)
    (by rw [← Nat.cast_add_one, heq]; exact hHl.trans (by exact_mod_cast le_max_left H B))
    (by rw [← Nat.cast_add_one, heq]; exact_mod_cast max_le hHu hBu) s hs
  rw [heq] at hf
  refine (Finset.sum_le_sum fun x _ => ?_).trans hf
  exact sub_le_sub_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    (card_defects_mono (le_max_left H B) (le_max_right H B) (x := x))) 1

end
end PaperC.V282.IndependentDefectParameters
