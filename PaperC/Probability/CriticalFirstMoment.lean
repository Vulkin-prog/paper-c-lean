import PaperC.Affine.StartDefectRank
import PaperC.Analysis.CriticalWeightedDefect
import PaperC.Probability.DefectFirstMoment

/-!
# Corollary 3.3 from the weighted defect mass

The start-tree rank bound is inserted here into the exact affine probability
formula.  The finite result is then packaged as the reciprocal-power meaning
of an `N^(-1/2+o(1))` first-moment error.
-/

namespace PaperC
namespace CriticalFirstMoment

/--
The exact finite first-moment error is bounded by the canonical weighted
defect mass divided by `2^L`.
-/
theorem abs_dyadicExpectation_sub_baseline_le
    {c₁ c₂ : ℝ} {N L : ℕ}
    (hL : 0 < L)
    (hAdm :
      CriticalWeightedDefect.Admissible c₁ c₂ N (L + 1)) :
    |dyadicExpectation N L - (N : ℚ) / (2 : ℚ) ^ L| ≤
      (CriticalWeightedDefect.dyadicDefectMass N (L + 1) : ℚ) /
        (2 : ℚ) ^ L := by
  have hN : 2 ≤ N := hAdm.2.1
  have htwoH : 2 * (L + 1) ≤ N :=
    CriticalWindowParameters.two_mul_H_le_N_of_criticalWindow
      hAdm.1 hAdm.2.2.2.1
  have hfinite :=
    DefectFirstMoment.abs_dyadicExpectation_sub_baseline_le_globalDefectWeight
      (N := N) (L := L) (X := 3 * N)
      (by omega) hL
      (by
        intro x hx
        have hxUpper : x < 2 * N :=
          (Finset.mem_Ico.mp (by simpa [dyadicBlock] using hx)).2
        omega)
      (by
        intro x hx
        exact
          Affine.StartDefectRank.relationRho_startSystem_le_card_defectsInInterval
            hN hx hL)
  simpa only [CriticalWeightedDefect.dyadicDefectMass, dyadicBlock] using
    hfinite

/-- Real-valued form of the finite first-moment estimate. -/
theorem abs_cast_dyadicExpectation_sub_baseline_le
    {c₁ c₂ : ℝ} {N L : ℕ}
    (hL : 0 < L)
    (hAdm :
      CriticalWeightedDefect.Admissible c₁ c₂ N (L + 1)) :
    |(dyadicExpectation N L : ℝ) - (N : ℝ) / (2 : ℝ) ^ L| ≤
      (CriticalWeightedDefect.dyadicDefectMass N (L + 1) : ℝ) /
        (2 : ℝ) ^ L := by
  have hq := abs_dyadicExpectation_sub_baseline_le hL hAdm
  calc
    |(dyadicExpectation N L : ℝ) -
          (N : ℝ) / (2 : ℝ) ^ L| =
        ((|dyadicExpectation N L -
          (N : ℚ) / (2 : ℚ) ^ L| : ℚ) : ℝ) := by
      simp only [Rat.cast_abs, Rat.cast_sub, Rat.cast_natCast,
        Rat.cast_div, map_pow, Rat.cast_ofNat]
      norm_num
    _ ≤
        (((CriticalWeightedDefect.dyadicDefectMass N (L + 1) : ℚ) /
          (2 : ℚ) ^ L : ℚ) : ℝ) :=
      (Rat.cast_le (K := ℝ)).2 hq
    _ =
        (CriticalWeightedDefect.dyadicDefectMass N (L + 1) : ℝ) /
          (2 : ℝ) ^ L := by
      simp only [Rat.cast_div, Rat.cast_natCast, map_pow, Rat.cast_ofNat]
      norm_num

/--
After multiplication by `N`, the first-moment error is bounded by a fixed
multiple of the weighted defect mass whenever `N / 2^L ≤ B`.
-/
theorem normalized_error_le_defectMass
    {c₁ c₂ B : ℝ} {N L : ℕ}
    (hL : 0 < L)
    (hAdm :
      CriticalWeightedDefect.Admissible c₁ c₂ N (L + 1))
    (hbalance : (N : ℝ) / (2 : ℝ) ^ L ≤ B) :
    (N : ℝ) *
        |(dyadicExpectation N L : ℝ) -
          (N : ℝ) / (2 : ℝ) ^ L| ≤
      B * (CriticalWeightedDefect.dyadicDefectMass N (L + 1) : ℝ) := by
  have hfinite :=
    abs_cast_dyadicExpectation_sub_baseline_le hL hAdm
  calc
    (N : ℝ) *
          |(dyadicExpectation N L : ℝ) -
            (N : ℝ) / (2 : ℝ) ^ L|
        ≤ (N : ℝ) *
          ((CriticalWeightedDefect.dyadicDefectMass N (L + 1) : ℝ) /
            (2 : ℝ) ^ L) :=
      mul_le_mul_of_nonneg_left hfinite (by positivity)
    _ = ((N : ℝ) / (2 : ℝ) ^ L) *
          (CriticalWeightedDefect.dyadicDefectMass N (L + 1) : ℝ) := by
      ring
    _ ≤ B *
          (CriticalWeightedDefect.dyadicDefectMass N (L + 1) : ℝ) :=
      mul_le_mul_of_nonneg_right hbalance (by positivity)

/--
Abstract critical run window used by the asymptotic corollary.  The usual
condition `|L-log₂ N| ≤ C` supplies fixed choices of `c₁,c₂,B`.
-/
def FirstMomentWindow
    (c₁ c₂ B : ℝ) (N L : ℕ) : Prop :=
  CriticalWindowParameters.InCriticalWindow c₁ c₂ N (L + 1) ∧
    0 < L ∧
    (N : ℝ) / (2 : ℝ) ^ L ≤ B

/--
Quantified form of Corollary 3.3:

`N * |E Z_{N,L} - N 2^{-L}| = N^(1/2+o(1))`,

uniformly in every fixed critical run window.  Equivalently, the unscaled
error is `N^(-1/2+o(1))`.
-/
theorem normalized_error_uniformHalfPower
    {c₁ c₂ B : ℝ}
    (hc₁ : 0 < c₁) (hc₁c₂ : c₁ < c₂) (hB : 0 ≤ B) :
    UniformHalfPowerSubpolynomialOn
      (FirstMomentWindow c₁ c₂ B)
      (fun N L =>
        (N : ℝ) *
          ((dyadicExpectation N L : ℝ) -
            (N : ℝ) / (2 : ℝ) ^ L)) := by
  have hmassWindow :=
    CriticalWeightedDefect.dyadicDefectMass_uniformHalfPower_on_window
      hc₁ hc₁c₂
  have hmass :
      UniformHalfPowerSubpolynomialOn
        (FirstMomentWindow c₁ c₂ B)
        (fun N L =>
          (CriticalWeightedDefect.dyadicDefectMass N (L + 1) : ℝ)) := by
    intro k hk
    obtain ⟨N₀, hN₀⟩ := hmassWindow k hk
    refine ⟨N₀, ?_⟩
    intro N hN L hwindow
    exact hN₀ N hN (L + 1) hwindow.1
  have hmajorant :
      UniformHalfPowerSubpolynomialOn
        (FirstMomentWindow c₁ c₂ B)
        (fun N L =>
          B *
            (CriticalWeightedDefect.dyadicDefectMass N (L + 1) : ℝ)) :=
    UniformHalfPower.const_mul B hmass
  apply UniformHalfPower.mono hmajorant
  obtain ⟨Nadm, hNadm⟩ :=
    CriticalWeightedDefect.admissible_eventually hc₁ hc₁c₂
  refine ⟨Nadm, ?_⟩
  intro N hN L hwindow
  have hAdm := hNadm N hN (L + 1) hwindow.1
  have hNnonneg : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hmassnonneg :
      0 ≤
        (CriticalWeightedDefect.dyadicDefectMass N (L + 1) : ℝ) := by
    positivity
  simp only [abs_mul, abs_of_nonneg hNnonneg,
    abs_of_nonneg hB, abs_of_nonneg hmassnonneg]
  exact normalized_error_le_defectMass hwindow.2.1 hAdm hwindow.2.2

end CriticalFirstMoment
end PaperC
