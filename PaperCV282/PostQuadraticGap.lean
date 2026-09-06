import PaperCV282.PostQuadraticPrimeBounds
import PaperCV282.PostQuadraticStartBounds
import PaperC.Asymptotics.PropositionFifteenFiveDecay

/-! # The exact post-quadratic gap dominates the prime scale -/
namespace PaperC.V282.PostQuadraticGap

open Filter BalasubramanianShoreyInput PropositionFifteenFiveDecay
open PostQuadraticPrimeBounds PostQuadraticStartBounds PostQuadraticLiterature
open InfiniteStartProbabilityTransfer WindowValues
open scoped Topology

noncomputable section

/-- The source gap divided by B/log B tends to infinity, without PNT. -/
theorem gap_div_scale_tendsto_atTop (theta : ℝ) :
    Tendsto (fun B : ℕ => gap B theta / ((B : ℝ) / Real.log B)) atTop atTop := by
  apply (gapFactor_tendsto_atTop theta).congr'
  filter_upwards [eventually_ge_atTop 2] with B hB
  have hBp : 0 < (B : ℝ) := by positivity
  have hlog : 0 < Real.log (B : ℝ) := Real.log_pos (by exact_mod_cast hB)
  rw [gap_eq hlog.ne']
  field_simp

/-- The gap divided by the actual inclusive prime count tends to infinity. -/
theorem gap_div_primeCounting_tendsto_atTop
    (hPNT : PrimeEulerPNT.PrimeNumberTheoremRemainder) (theta : ℝ) :
    Tendsto (fun B : ℕ => gap B theta / (Nat.primeCounting B : ℝ)) atTop atTop := by
  have hi := (primeCounting_normalized_tendsto_one hPNT).inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have ht := (gapFactor_tendsto_atTop theta).atTop_mul_pos
    (by norm_num : (0 : ℝ) < 1⁻¹) hi
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 2] with B hB
  have hBp : 0 < (B : ℝ) := by positivity
  have hlog : 0 < Real.log (B : ℝ) := Real.log_pos (by exact_mod_cast hB)
  rw [gap_eq hlog.ne']
  by_cases hp : (Nat.primeCounting B : ℝ) = 0
  · simp [hp]
  · field_simp

/-- The displayed E.3 defect maximum and probability estimate, with its
divergent prime-normalized gap, share the same absolute parameter. -/
theorem lemma_e_three (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeEulerPNT.PrimeNumberTheoremRemainder) :
    ∃ theta : ℝ,
      Tendsto (fun B : ℕ => gap B theta / (Nat.primeCounting B : ℝ)) atTop atTop ∧
      ∃ Lzero : ℕ, ∀ L ≥ Lzero, ∀ x : ℕ,
        (L + 1) ^ 2 + 2 < x →
        ((defectIndices (L + 1) x (L + 1)).card : ℝ) ≤
          (L + 1 : ℕ) - gap (L + 1) theta ∧
        infiniteStartProbability x L ≤ (2 : ℝ) ^ (-gap (L + 1) theta) := by
  obtain ⟨theta, Lzero, h⟩ := postquadratic_defects_and_affine_probability hShorey
  refine ⟨theta, gap_div_primeCounting_tendsto_atTop hPNT theta, max Lzero 1, ?_⟩
  intro L hL x hx
  obtain ⟨hc, hp⟩ := h L (by omega) x hx
  refine ⟨?_, ?_⟩
  · unfold gap
    linarith
  · rw [← PointwiseStartBounds.infiniteAffineStartProbability_startRhs_eq (by omega : 0 < L)]
    exact hp _

end
end PaperC.V282.PostQuadraticGap
