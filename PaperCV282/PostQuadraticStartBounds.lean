import PaperCV282.PostQuadraticLiterature
import PaperCV282.PointwiseStartBounds

/-! # Actual post-quadratic defective windows and start probabilities -/
namespace PaperC.V282.PostQuadraticStartBounds

open BalasubramanianShoreyInput BalasubramanianShoreyMaximum
open WindowValues PointwiseStartBounds PostQuadraticLiterature
open InfiniteStartProbabilityTransfer

noncomputable section

/-- The full list of value defects is exactly the historical offset population. -/
theorem card_full_defects_eq_offsets {B x : ℕ} (hx : 2 ≤ x) :
    (defectIndices B x B).card = (defectiveOffsets B (x - 2)).card := by
  classical
  apply Finset.card_bij (fun i _ => i.val + 1)
  · intro i hi
    have hd : DefectivePredicate.HDefective B (vertex x B i) := by
      simpa [defectIndices] using hi
    apply mem_defectiveOffsets.mpr
    refine ⟨by omega, by omega, ?_⟩
    have hv : x - 2 + (i.val + 1) = vertex x B i := by unfold vertex; omega
    simpa only [hv] using hd
  · intro i hi j hj hij
    apply Fin.ext
    omega
  · intro d hd
    obtain ⟨hdone, hdB, hddef⟩ := mem_defectiveOffsets.mp hd
    let i : Fin B := ⟨d - 1, by omega⟩
    refine ⟨i, ?_, by dsimp [i]; omega⟩
    have hv : vertex x B i = x - 2 + d := by dsimp [vertex, i]; omega
    simp only [defectIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa only [hv] using hddef

/-- The real affine upper bound, with the full B=L+1 window and no root loss. -/
theorem affine_probability_le_gap {x L : ℕ} {g : ℝ} (hx : 2 ≤ x)
    (hg : g ≤ (L : ℝ))
    (hm : ((defectIndices (L + 1) x (L + 1)).card : ℝ) ≤ (L + 1 : ℕ) - g)
    (b : Fin L → F₂) :
    infiniteAffineStartProbability x L b ≤ (2 : ℝ) ^ (-g) := by
  have h := corollary_two_five_upper_infinite hx b
  have hpow : (2 : ℝ) ^ ((defectIndices (L + 1) x (L + 1)).card - 1) /
      (2 : ℝ) ^ L = (2 : ℝ) ^
        (((defectIndices (L + 1) x (L + 1)).card - 1 : ℕ) - (L : ℝ)) := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_natCast, Real.rpow_natCast]
  rw [hpow] at h
  apply h.trans
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  by_cases hz : (defectIndices (L + 1) x (L + 1)).card = 0
  · simp only [hz, Nat.zero_sub, Nat.cast_zero, zero_sub]
    linarith
  · rw [Nat.cast_sub (by omega : 1 ≤ (defectIndices (L + 1) x (L + 1)).card)]
    push_cast at hm ⊢
    linarith

/-- The full defective-window maximum and the sharp real probability gap,
uniformly after a single absolute threshold and with no upper bound on x. -/
theorem postquadratic_defects_and_affine_probability
    (hShorey : ShoreySquareProductStatement) :
    ∃ theta : ℝ, ∃ Lzero : ℕ, ∀ L ≥ Lzero, ∀ x : ℕ,
      (L + 1) ^ 2 + 2 < x →
      ((defectIndices (L + 1) x (L + 1)).card : ℝ) < mu (L + 1) theta ∧
      ∀ b : Fin L → F₂,
        infiniteAffineStartProbability x L b ≤ (2 : ℝ) ^ (-gap (L + 1) theta) := by
  obtain ⟨theta, Bzero, hmax⟩ := defectiveWindow_card_lt_mu_eventually
    (balasubramanianShorey_of_square_product hShorey)
  obtain ⟨Bmu, hmu⟩ := eventually_two_le_mu theta
  refine ⟨theta, max Bzero Bmu, ?_⟩
  intro L hL x hx
  have hB : Bzero ≤ L + 1 := by omega
  have hBm : Bmu ≤ L + 1 := by omega
  have hxtwo : 2 ≤ x := by omega
  have hc := hmax (L + 1) hB x hx
  rw [← card_full_defects_eq_offsets hxtwo] at hc
  refine ⟨hc, fun b => affine_probability_le_gap hxtwo ?_ ?_ b⟩
  · have hm := hmu (L + 1) hBm
    unfold gap
    push_cast
    linarith
  · unfold gap
    linarith

/-- The genuine left-maximal start event satisfies the displayed E.3 bound. -/
theorem postquadratic_start_probability
    (hShorey : ShoreySquareProductStatement) :
    ∃ theta : ℝ, ∃ Lzero : ℕ, ∀ L ≥ Lzero, ∀ x : ℕ,
      (L + 1) ^ 2 + 2 < x →
      infiniteStartProbability x L ≤ (2 : ℝ) ^ (-gap (L + 1) theta) := by
  obtain ⟨theta, Lzero, h⟩ := postquadratic_defects_and_affine_probability hShorey
  refine ⟨theta, max Lzero 1, ?_⟩
  intro L hL x hx
  have hLp : 0 < L := by omega
  rw [← infiniteAffineStartProbability_startRhs_eq hLp]
  exact (h L (by omega) x hx).2 _

end
end PaperC.V282.PostQuadraticStartBounds
