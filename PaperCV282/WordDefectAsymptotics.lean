import PaperC.Analysis.CriticalWeightedDefect
import PaperC.Analysis.DefectGlobalBound
import PaperCV282.WordDefectCounting

/-!
# Uniform square-root bounds for defects of prescribed-word windows

The retained arithmetic mass controls intervals starting at `x`. Word
windows begin at `x - 1`; the finite bridge accounts separately for this
extra vertex. Both the retained mass and the extra global defect count
fit the same explicit subpolynomial residual factor.
-/

namespace PaperC.V282.WordDefectAsymptotics

open CriticalWeightedDefect CriticalWindowParameters
open WordDefectCounting
open scoped BigOperators

noncomputable section

/-- The retained finite bound, with its square-root factor extracted. -/
theorem retainedDefectMass_cast_le_sqrt_mul_residual
    {c₁ c₂ : ℝ} {N B : ℕ} (h : Admissible c₁ c₂ N B) :
    (dyadicDefectMass N B : ℝ) ≤ Real.sqrt N * residualFactor c₁ c₂ N B := by
  refine (dyadicDefectMass_cast_le h).trans_eq ?_
  unfold residualFactor
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
  ring

/-- The same residual factor dominates the global cost of the extra vertex. -/
theorem globalDefectCount_cast_le_sqrt_mul_residual
    (c₁ c₂ : ℝ) (N B : ℕ) :
    ((WeightedDefectCounting.positiveDefectValues
      (DefectCounting.smallPrimesUpTo B) (3 * N)).card : ℝ) ≤
      Real.sqrt N * residualFactor c₁ c₂ N B := by
  have hglobal := card_positiveHDefectValues_cast_le_sqrt_mul_exp B (3 * N)
  let e := 2 * RungeLogarithmicGrowth.cappedRadius N B (logarithmicCap N) *
    2 ^ (codingConstant c₁ c₂ + 1)
  have hB : (1 : ℝ) ≤ (B + 1 : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) B]
  have he : (1 : ℝ) ≤ ((2 ^ e : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_pow e 2 (by omega)
  have hfactor : (1 : ℝ) ≤ (B + 1 : ℝ) * ((2 ^ e : ℕ) : ℝ) :=
    one_le_mul_of_one_le_of_one_le hB he
  calc
    _ ≤ Real.sqrt ((3 * N : ℕ) : ℝ) * Real.exp (2 * Real.sqrt B) := hglobal
    _ ≤ (Real.sqrt ((3 * N : ℕ) : ℝ) * Real.exp (2 * Real.sqrt B)) *
        ((B + 1 : ℝ) * ((2 ^ e : ℕ) : ℝ)) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hfactor
        (by positivity : 0 ≤ Real.sqrt ((3 * N : ℕ) : ℝ) * Real.exp (2 * Real.sqrt B))
    _ = Real.sqrt N * residualFactor c₁ c₂ N B := by
      unfold residualFactor
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
      dsimp [e]
      ring

/-- The shifted word mass is at most three times the retained square-root majorant. -/
theorem wordDefectMass_cast_le_residual
    {c₁ c₂ : ℝ} {N B : ℕ} (h : Admissible c₁ c₂ N B) :
    (wordDefectMass N B : ℝ) ≤ Real.sqrt N * (3 * residualFactor c₁ c₂ N B) := by
  have htwoB := two_mul_H_le_N_of_criticalWindow h.1 h.2.2.2.1
  have hfinite : (wordDefectMass N B : ℝ) ≤
      2 * (dyadicDefectMass N B : ℝ) +
        ((WeightedDefectCounting.positiveDefectValues
          (DefectCounting.smallPrimesUpTo B) (3 * N)).card : ℝ) := by
    exact_mod_cast wordDefectMass_le h.2.1 (by omega : B ≤ N)
  calc
    _ ≤ _ := hfinite
    _ ≤ 2 * (Real.sqrt N * residualFactor c₁ c₂ N B) +
        Real.sqrt N * residualFactor c₁ c₂ N B :=
      add_le_add (mul_le_mul_of_nonneg_left
        (retainedDefectMass_cast_le_sqrt_mul_residual h) (by norm_num))
        (globalDefectCount_cast_le_sqrt_mul_residual c₁ c₂ N B)
    _ = _ := by ring

/-- Uniform square-root order under the explicit finite admissibility thresholds. -/
theorem wordDefectMass_uniformHalfPower
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁c₂ : c₁ < c₂) :
    UniformHalfPowerSubpolynomialOn (Admissible c₁ c₂)
      (fun N B => (wordDefectMass N B : ℝ)) := by
  apply UniformHalfPower.of_sqrt_mul_subpolynomial
    (ExpSqrtLog.uniformSubpolynomialOn_const_mul 3
      (residualFactor_uniformSubpolynomial hc₁ hc₁c₂))
  refine ⟨0, ?_⟩
  intro N _ B h
  rw [abs_of_nonneg (by positivity),
    abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3)
      (residualFactor_nonneg c₁ c₂ N B))]
  exact wordDefectMass_cast_le_residual h

/-- The word defect mass is `N^(1/2+o(1))` uniformly on the manuscript's
fixed logarithmic band, with no remaining finite technical threshold hypothesis. -/
theorem wordDefectMass_uniformHalfPower_on_window
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁c₂ : c₁ < c₂) :
    UniformHalfPowerSubpolynomialOn (InCriticalWindow c₁ c₂)
      (fun N B => (wordDefectMass N B : ℝ)) := by
  have hmass := wordDefectMass_uniformHalfPower hc₁ hc₁c₂
  obtain ⟨Nadm, hNadm⟩ := admissible_eventually hc₁ hc₁c₂
  intro k hk
  obtain ⟨Nmass, hNmass⟩ := hmass k hk
  refine ⟨max Nadm Nmass, ?_⟩
  intro N hN B hwindow
  exact hNmass N ((le_max_right _ _).trans hN) B
    (hNadm N ((le_max_left _ _).trans hN) B hwindow)

end
end PaperC.V282.WordDefectAsymptotics
