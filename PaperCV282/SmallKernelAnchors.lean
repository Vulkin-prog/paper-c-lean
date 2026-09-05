import PaperCV282.SizeTwoHostAsymptotics
import PaperCV282.ShiftedKernelQuotients

/-!
# The small-kernel anchors in shifted energy

All integers with kernel at most the cube root of the ambient scale are
counted together. The cutoff is three times the scale, so the container
includes every positive occurrence in the enlarged window slice. This
is the low-kernel counting part of Lemma 3.24, before window multiplicities.
-/

namespace PaperC.V282.SmallKernelAnchors

open TerminalKernelCount SizeTwoHostAsymptotics

noncomputable section

/-- The elementary kernel container at the cube-root cutoff. -/
theorem card_smallKernelAnchors_le_exp
    {X T : ℕ} (hX : 0 < X) (hT : (T : ℝ) ≤ (X : ℝ) ^ (1 / (3 : ℝ))) (B : ℕ) :
    ((boundedLargeKernelValues B T (3 * X)).card : ℝ) ≤
      4 * Real.exp (2 * Real.sqrt B) * (X : ℝ) ^ (2 / (3 : ℝ)) := by
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX
  have hs : Real.sqrt (3 * X : ℝ) ≤ 2 * Real.sqrt X := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · rw [mul_pow, Real.sq_sqrt hXpos.le]
      nlinarith
  have ht : Real.sqrt T ≤ (X : ℝ) ^ (1 / (6 : ℝ)) := by
    calc
      _ ≤ Real.sqrt ((X : ℝ) ^ (1 / (3 : ℝ))) := Real.sqrt_le_sqrt hT
      _ = _ := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hXpos.le]
        norm_num
  have hprod : Real.sqrt X * (X : ℝ) ^ (1 / (6 : ℝ)) =
      (X : ℝ) ^ (2 / (3 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hXpos]
    norm_num
  calc
    _ ≤ 2 * Real.sqrt (3 * X : ℕ) * Real.sqrt T * Real.exp (2 * Real.sqrt B) :=
      card_boundedLargeKernelValues_cast_le_exp B T (3 * X)
    _ ≤ 2 * (2 * Real.sqrt X) * (X : ℝ) ^ (1 / (6 : ℝ)) * Real.exp (2 * Real.sqrt B) := by
      push_cast
      gcongr
    _ = 4 * Real.exp (2 * Real.sqrt B) *
        (Real.sqrt X * (X : ℝ) ^ (1 / (6 : ℝ))) := by ring
    _ = _ := by rw [hprod]

/-- Uniform cube-root-kernel population, with its actual height cutoff retained. -/
theorem card_smallKernelAnchors_le_two_thirds_eventually
    (C epsilon : ℝ) (hC : 0 ≤ C) (hepsilon : 0 < epsilon) :
    ∃ Xzero : ℕ, ∀ X ≥ Xzero, ∀ L : ℕ,
      (L + 1 : ℝ) ≤ C * Real.log X → ∀ T : ℕ,
      (T : ℝ) ≤ (X : ℝ) ^ (1 / (3 : ℝ)) →
      ((boundedLargeKernelValues (L + 1) T (3 * X)).card : ℝ) ≤
        (X : ℝ) ^ epsilon * (X : ℝ) ^ (2 / (3 : ℝ)) := by
  obtain ⟨Xfactor, hfactor⟩ := polynomial_euler_le_rpow_eventually C 4 epsilon hC hepsilon
  refine ⟨max Xfactor 1, ?_⟩
  intro X hX L hL T hT
  have hXpos : 0 < X := by omega
  have hpoly := hfactor X ((le_max_left _ _).trans hX) L (by simpa using hL)
  have hB : (1 : ℝ) ≤ L + 1 := by have := Nat.cast_nonneg (α := ℝ) L; linarith
  have hpow : (1 : ℝ) ≤ (L + 1 : ℝ) ^ 5 := one_le_pow₀ hB
  have hexp : Real.exp (2 * Real.sqrt (L + 1 : ℝ)) ≤
      Real.exp (4 * Real.sqrt (L + 1 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.sqrt_nonneg (L + 1 : ℝ)]
  have hsmall : 4 * Real.exp (2 * Real.sqrt (L + 1 : ℝ)) ≤ (X : ℝ) ^ epsilon := by
    rw [abs_of_nonneg (by positivity)] at hpoly
    refine le_trans ?_ hpoly
    nlinarith [Real.exp_pos (4 * Real.sqrt (L + 1 : ℝ))]
  exact (card_smallKernelAnchors_le_exp hXpos hT (L + 1)).trans
    (mul_le_mul_of_nonneg_right (by simpa only [Nat.cast_add, Nat.cast_one] using hsmall) (by positivity))

end
end PaperC.V282.SmallKernelAnchors
