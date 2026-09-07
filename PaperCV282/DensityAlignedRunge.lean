import PaperCV282.DensityHammingBudget
import PaperCV282.MacroscopicAlignedExclusion

/-! # Component extraction and Runge at an arbitrary fixed positive density -/

namespace PaperC.V282.DensityAlignedRunge

open MacroscopicAlignedRunge MacroscopicGeometry TheoremEightHammingBudget
open Affine.CanonicalRationalCode AlignedCoreExclusion CanonicalResidualComponents

noncomputable section

/-- A density denominator determines a fixed cutoff and pays the two exceptional components. -/
theorem density_counting_budget {B D c : ℕ} (hD : 0 < D)
    (hB : 4 * D ≤ B) (hc : B ≤ D * c) :
    B / (4 * D) + 2 + (2 * B) / (8 * D + 1) ≤ c := by
  have htail : (2 * B) / (8 * D + 1) ≤ B / (4 * D) := by
    calc
      _ ≤ (2 * B) / (8 * D) := Nat.div_le_div_left (by omega) (by omega)
      _ = B / (4 * D) := by
        rw [show 8 * D = 2 * (4 * D) by ring]
        exact Nat.mul_div_mul_left B (4 * D) (by norm_num)
  have hq := Nat.div_mul_le_self B (4 * D)
  have hbudget : D * (B / (4 * D) + 2 + (2 * B) / (8 * D + 1)) ≤ B := by
    have hmul := Nat.mul_le_mul_left D htail
    nlinarith
  exact Nat.le_of_mul_le_mul_left (hbudget.trans hc) hD

/-- The finite extraction is applied to the actual residual component family. -/
theorem density_small_components {x y L H D : ℕ}
    (c : ReducedCandidate x y (L + 1) H) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hD : 0 < D) (hB : 4 * D ≤ L + 1)
    (hc : L + 1 ≤ D * (residualComponents x y L c.1.1 c.1.2
      (pairChannelError x y c.1.1 c.1.2)).card) :
    (L + 1) / (4 * D) ≤ (smallExactFreeResidualComponents x y L c.1.1 c.1.2
      (pairChannelError x y c.1.1 c.1.2) (8 * D)).card := by
  apply target_le_card_smallExactFreeResidualComponents_of_candidate c hx hy
  exact density_counting_budget hD hB hc

/-- Any fixed component-size cutoff is absorbed by rescaling the Runge radius budget. -/
theorem runge_general_cutoff_eventually
    (betaMin betaMax delta : ℝ) (hmin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (hdelta : 0 < delta) (A K : ℕ) :
    ∃ Mzero : ℕ, ∀ M ≥ Mzero, ∀ B : ℕ,
      betaMin * Real.log M ≤ (B : ℝ) → (B : ℝ) ≤ betaMax * Real.log M →
      ∀ H : ℕ, 1 ≤ H → H ≤ B ^ A → ∀ t : ℕ,
      (t : ℝ) ≤ 65 * B / (Real.log B * Real.log (Real.log B)) →
      ∀ k : ℕ, 1 ≤ k → k ≤ K * t → ∀ a : ℕ, 1 ≤ a →
      ∀ x ∈ macroscopicStarts M delta,
        (128 * (2 * k) * (3 * H * B)) ^ (4 * k) < a * x := by
  obtain ⟨Mzero, hrunge⟩ := rungeScale_lt_macroscopic_eventually
    betaMin betaMax delta (65 * K) hmin hbeta hdelta (by positivity) A
  refine ⟨Mzero, ?_⟩
  intro M hM B hlo hhi H hH hHB t ht k hk hkt a ha x hx
  apply hrunge M hM B hlo hhi H hH hHB (K * t) _ k hk _ a ha x hx
  · have h := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg K)
    push_cast
    simpa only [mul_div_assoc, mul_assoc, mul_left_comm, mul_comm] using h
  · exact hkt.trans (Nat.le_mul_of_pos_left _ (by norm_num : 0 < 43))

end
end PaperC.V282.DensityAlignedRunge
