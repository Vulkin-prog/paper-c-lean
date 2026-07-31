import PaperC.Analysis.WeightedDefectMass
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Explicit parameters in the logarithmic critical window

This module discharges the integer-rounding obligations that occur when
Proposition 3.2 is applied under

`0 < c₁ < c₂` and `c₁ * log N ≤ H ≤ c₂ * log N`.

The common cap is the natural ceiling

`T(N) = ⌈log N⌉₊`.

The Chebyshev budget is handled without a circular hypothesis on the chosen
Runge radius.  We first define the least integral radius required by the
finite Chebyshev bound,

`requiredRadius(H,A) = ⌈((7H / ⌊log₂ H⌋) + 1) / A⌉`,

using natural ceiling division.  A single real inequality then places this
independently defined radius below `RungeLogarithmicGrowth.cappedRadius`.
The final theorem feeds all resulting conditions into
`WeightedDefectMass.sum_two_pow_localCount_sub_one_cast_le_of_cappedRadius`.

Thus the remaining asymptotic work is reduced to three transparent real
thresholds: `H ≥ 4`, the translation condition `2H ≤ N`, and one comparison
between `log N` and the logarithmic Runge denominator.
-/

namespace PaperC
namespace CriticalWindowParameters

/-- The precise logarithmic critical-window predicate used in Proposition 3.2. -/
def InCriticalWindow (c₁ c₂ : ℝ) (N H : ℕ) : Prop :=
  0 < c₁ ∧ c₁ < c₂ ∧
    c₁ * Real.log N ≤ (H : ℝ) ∧
    (H : ℝ) ≤ c₂ * Real.log N

/-- A natural cap of order `log N`, shared by all intervals in the family. -/
noncomputable def logarithmicCap (N : ℕ) : ℕ :=
  ⌈Real.log N⌉₊

/--
An explicit natural constant depending only on the endpoints of the critical
window.  Its generous numerical factor leaves room for the elementary
Chebyshev constant and for the factor `8` in the Runge denominator.
-/
noncomputable def codingConstant (c₁ c₂ : ℝ) : ℕ :=
  ⌈256 * (1 + c₂) * (1 + 1 / c₁)⌉₊

/-- The natural numerator appearing in the simplified Chebyshev budget. -/
def chebyshevDemand (H : ℕ) : ℕ :=
  (7 * H) / Nat.log 2 H + 1

/--
The least natural radius sufficient for the Chebyshev budget with constant
`A`.  Natural ceiling division makes the defining budget exact.
-/
def requiredRadius (H A : ℕ) : ℕ :=
  chebyshevDemand H ⌈/⌉ A

/-- `log N` is bounded above by its natural ceiling. -/
theorem log_le_logarithmicCap (N : ℕ) :
    Real.log N ≤ (logarithmicCap N : ℝ) := by
  exact Nat.le_ceil _

/-- The logarithmic cap is nonzero as soon as `N ≥ 2`. -/
theorem one_le_logarithmicCap {N : ℕ} (hN : 2 ≤ N) :
    1 ≤ logarithmicCap N := by
  rw [logarithmicCap, Nat.one_le_ceil_iff]
  apply Real.log_pos
  exact_mod_cast (show 1 < N by omega)

/-- Positivity of the denominator used to define the capped Runge radius. -/
theorem rungeDenominator_pos {H T : ℕ}
    (hH : 1 ≤ H) (hT : 1 ≤ T) :
    0 < (8 : ℝ) * Real.log (256 * T * H) := by
  have hbase : 1 < 256 * T * H := by
    have hHpos : 0 < H := Nat.zero_lt_of_lt hH
    have hTpos : 0 < T := Nat.zero_lt_of_lt hT
    nlinarith [show 256 ≤ 256 * T * H by
      calc
        256 = 256 * 1 * 1 := by norm_num
        _ ≤ 256 * T * H :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 256 hT) hH]
  have hlog : 0 < Real.log (256 * T * H : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hbase
  positivity

/--
The Runge denominator is at least one.  The only numerical input is
Mathlib's certified lower bound for `log 2`.
-/
theorem one_le_rungeDenominator {H T : ℕ}
    (hH : 1 ≤ H) (hT : 1 ≤ T) :
    (1 : ℝ) ≤ 8 * Real.log (256 * T * H) := by
  have hbase : 2 ≤ 256 * T * H := by
    calc
      2 ≤ 256 := by norm_num
      _ = 256 * 1 * 1 := by norm_num
      _ ≤ 256 * T * H :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 256 hT) hH
  have hlogMono :
      Real.log (2 : ℝ) ≤ Real.log (256 * T * H : ℝ) := by
    apply Real.log_le_log
    · norm_num
    · exact_mod_cast hbase
  nlinarith [Real.log_two_gt_d9]

/--
The floored Runge radius never exceeds the logarithmic cap.  In particular,
the auxiliary `t ≤ T` hypothesis in the capped Runge theorem is automatic
for `T = logarithmicCap N`.
-/
theorem cappedRadius_le_logarithmicCap
    {N H T : ℕ}
    (hH : 1 ≤ H) (hT : 1 ≤ T) :
    RungeLogarithmicGrowth.cappedRadius N H T ≤ logarithmicCap N := by
  have hden :
      (1 : ℝ) ≤ 8 * Real.log (256 * T * H) :=
    one_le_rungeDenominator hH hT
  have hlogNonneg : 0 ≤ Real.log (N : ℝ) :=
    Real.log_natCast_nonneg N
  have hquot :
      Real.log (N : ℝ) / (8 * Real.log (256 * T * H)) ≤
        Real.log (N : ℝ) :=
    div_le_self hlogNonneg hden
  unfold RungeLogarithmicGrowth.cappedRadius
  exact
    (Nat.floor_mono hquot).trans
      (Nat.floor_le_ceil (Real.log (N : ℝ)))

/--
A non-circular lower bound for the capped radius: it suffices to compare the
independently chosen integer `B` with the real logarithmic quotient before
taking its floor.
-/
theorem le_cappedRadius_of_scaled_log_le
    {N H T B : ℕ}
    (hH : 1 ≤ H) (hT : 1 ≤ T)
    (hscale :
      (B : ℝ) * (8 * Real.log (256 * T * H)) ≤
        Real.log N) :
    B ≤ RungeLogarithmicGrowth.cappedRadius N H T := by
  have hden :
      0 < (8 : ℝ) * Real.log (256 * T * H) :=
    rungeDenominator_pos hH hT
  have hlogNonneg : 0 ≤ Real.log (N : ℝ) := by
    exact Real.log_natCast_nonneg N
  have hquotNonneg :
      0 ≤ Real.log (N : ℝ) /
        (8 * Real.log (256 * T * H)) :=
    div_nonneg hlogNonneg hden.le
  unfold RungeLogarithmicGrowth.cappedRadius
  rw [Nat.le_floor_iff hquotNonneg]
  exact (le_div_iff₀ hden).2 hscale

/-- The critical-window constant is positive under `0 < c₁ < c₂`. -/
theorem one_le_codingConstant
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁c₂ : c₁ < c₂) :
    1 ≤ codingConstant c₁ c₂ := by
  rw [codingConstant, Nat.one_le_ceil_iff]
  have hc₂ : 0 < c₂ := hc₁.trans hc₁c₂
  have hinv : 0 < 1 / c₁ := one_div_pos.mpr hc₁
  positivity

/-- The real upper-window constant is bounded by the chosen natural constant. -/
theorem c₂_le_codingConstant
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁c₂ : c₁ < c₂) :
    c₂ ≤ (codingConstant c₁ c₂ : ℝ) := by
  have hc₂ : 0 < c₂ := hc₁.trans hc₁c₂
  have hinv : 0 < 1 / c₁ := one_div_pos.mpr hc₁
  have hfirst : c₂ ≤ 256 * (1 + c₂) := by
    nlinarith
  have hnonneg : 0 ≤ 256 * (1 + c₂) := by positivity
  have hfactor : 1 ≤ 1 + 1 / c₁ := by linarith
  calc
    c₂ ≤ 256 * (1 + c₂) := hfirst
    _ ≤ 256 * (1 + c₂) * (1 + 1 / c₁) :=
      le_mul_of_one_le_right hnonneg hfactor
    _ ≤ (codingConstant c₁ c₂ : ℝ) := by
      exact Nat.le_ceil _

/--
Inside the critical window, the height is bounded by the natural constant
times the logarithmic cap.  This removes `H` from upper estimates for the
Runge base.
-/
theorem H_le_codingConstant_mul_logarithmicCap
    {c₁ c₂ : ℝ} {N H : ℕ}
    (hwindow : InCriticalWindow c₁ c₂ N H) :
    H ≤ codingConstant c₁ c₂ * logarithmicCap N := by
  have hc₂A :
      c₂ ≤ (codingConstant c₁ c₂ : ℝ) :=
    c₂_le_codingConstant hwindow.1 hwindow.2.1
  have hlog : Real.log N ≤ (logarithmicCap N : ℝ) :=
    log_le_logarithmicCap N
  have hlogNonneg : 0 ≤ Real.log (N : ℝ) :=
    Real.log_natCast_nonneg N
  have hcast :
      (H : ℝ) ≤
        (codingConstant c₁ c₂ : ℝ) *
          (logarithmicCap N : ℝ) := by
    exact hwindow.2.2.2.trans
      (mul_le_mul hc₂A hlog hlogNonneg
        (Nat.cast_nonneg (codingConstant c₁ c₂)))
  exact_mod_cast hcast

/--
Uniform envelope for the logarithm in the Runge denominator.  Its base is a
constant times `⌈log N⌉²`, as expected in the critical window.
-/
theorem rungeLog_le_criticalEnvelope
    {c₁ c₂ : ℝ} {N H : ℕ}
    (hwindow : InCriticalWindow c₁ c₂ N H)
    (hH : 1 ≤ H)
    (hT : 1 ≤ logarithmicCap N) :
    Real.log (256 * logarithmicCap N * H) ≤
      Real.log
        (256 * codingConstant c₁ c₂ *
          logarithmicCap N * logarithmicCap N) := by
  have hheight :
      H ≤ codingConstant c₁ c₂ * logarithmicCap N :=
    H_le_codingConstant_mul_logarithmicCap hwindow
  have hbase :
      256 * logarithmicCap N * H ≤
        256 * codingConstant c₁ c₂ *
          logarithmicCap N * logarithmicCap N := by
    calc
      256 * logarithmicCap N * H
          ≤ 256 * logarithmicCap N *
              (codingConstant c₁ c₂ * logarithmicCap N) :=
        Nat.mul_le_mul_left (256 * logarithmicCap N) hheight
      _ = 256 * codingConstant c₁ c₂ *
            logarithmicCap N * logarithmicCap N := by ring
  have hbasePos : 0 < 256 * logarithmicCap N * H := by
    have hHpos : 0 < H := Nat.zero_lt_of_lt hH
    have hTpos : 0 < logarithmicCap N := Nat.zero_lt_of_lt hT
    positivity
  apply Real.log_le_log
  · exact_mod_cast hbasePos
  · exact_mod_cast hbase

/--
It is enough to verify the scaled-log condition with the uniform critical
envelope `256 * A * T²`.
-/
theorem scaled_log_le_of_criticalEnvelope
    {c₁ c₂ : ℝ} {N H : ℕ}
    (hwindow : InCriticalWindow c₁ c₂ N H)
    (hH : 1 ≤ H)
    (hT : 1 ≤ logarithmicCap N)
    (henvelope :
      (requiredRadius H (codingConstant c₁ c₂) : ℝ) *
          (8 * Real.log
            (256 * codingConstant c₁ c₂ *
              logarithmicCap N * logarithmicCap N)) ≤
        Real.log N) :
    (requiredRadius H (codingConstant c₁ c₂) : ℝ) *
          (8 * Real.log
            (256 * logarithmicCap N * H)) ≤
        Real.log N := by
  apply le_trans ?_ henvelope
  have hlog :=
    rungeLog_le_criticalEnvelope hwindow hH hT
  have hrequired :
      0 ≤ (requiredRadius H (codingConstant c₁ c₂) : ℝ) := by
    positivity
  nlinarith

/--
The defining property of the natural ceiling quotient gives the exact
Chebyshev budget.
-/
theorem chebyshevDemand_le_mul_requiredRadius
    {H A : ℕ} (hA : 1 ≤ A) :
    chebyshevDemand H ≤ A * requiredRadius H A := by
  unfold requiredRadius
  exact
    (ceilDiv_le_iff_le_mul (show 0 < A by omega)).1 le_rfl

/-- The required radius is positive whenever the coding constant is. -/
theorem one_le_requiredRadius
    {H A : ℕ} (hA : 1 ≤ A) :
    1 ≤ requiredRadius H A := by
  have hdemand : 1 ≤ chebyshevDemand H := by
    simp [chebyshevDemand]
  have hbudget := chebyshevDemand_le_mul_requiredRadius
    (H := H) hA
  by_contra h
  have hz : requiredRadius H A = 0 := by omega
  rw [hz, mul_zero] at hbudget
  omega

/--
The single scaled-log comparison implies the finite Chebyshev budget for the
actual capped radius.
-/
theorem chebyshev_budget_of_scaled_log_le
    {N H T A : ℕ}
    (hH : 1 ≤ H) (hT : 1 ≤ T) (hA : 1 ≤ A)
    (hscale :
      (requiredRadius H A : ℝ) *
          (8 * Real.log (256 * T * H)) ≤
        Real.log N) :
    (7 * H) / Nat.log 2 H + 1 ≤
      A * RungeLogarithmicGrowth.cappedRadius N H T := by
  have hradius :
      requiredRadius H A ≤
        RungeLogarithmicGrowth.cappedRadius N H T :=
    le_cappedRadius_of_scaled_log_le hH hT hscale
  exact
    (chebyshevDemand_le_mul_requiredRadius hA).trans
      (Nat.mul_le_mul_left A hradius)

/--
The lower edge of the critical window implies `H ≥ 4` once the displayed
real threshold is met.
-/
theorem four_le_H_of_criticalWindow
    {c₁ c₂ : ℝ} {N H : ℕ}
    (hwindow : InCriticalWindow c₁ c₂ N H)
    (hfour : (4 : ℝ) ≤ c₁ * Real.log N) :
    4 ≤ H := by
  exact_mod_cast hfour.trans hwindow.2.2.1

/--
The upper edge of the critical window implies the Runge translation
condition `2H ≤ N` once `2 c₂ log N ≤ N`.
-/
theorem two_mul_H_le_N_of_criticalWindow
    {c₁ c₂ : ℝ} {N H : ℕ}
    (hwindow : InCriticalWindow c₁ c₂ N H)
    (htranslation :
      2 * c₂ * Real.log N ≤ (N : ℝ)) :
    2 * H ≤ N := by
  have hupper := hwindow.2.2.2
  have hcast : (2 * H : ℕ) ≤ N := by
    exact_mod_cast
      (calc
        (2 : ℝ) * (H : ℝ) ≤
            2 * (c₂ * Real.log N) :=
          mul_le_mul_of_nonneg_left hupper (by norm_num)
        _ = 2 * c₂ * Real.log N := by ring
        _ ≤ (N : ℝ) := htranslation)
  exact hcast

/--
All finite parameter obligations of the capped-radius mass theorem follow
from explicit, non-circular real thresholds.
-/
theorem cappedRadius_conditions_of_criticalWindow
    {c₁ c₂ : ℝ} {N H : ℕ}
    (hwindow : InCriticalWindow c₁ c₂ N H)
    (hN : 2 ≤ N)
    (hfour : (4 : ℝ) ≤ c₁ * Real.log N)
    (hscale :
      (requiredRadius H (codingConstant c₁ c₂) : ℝ) *
          (8 * Real.log
            (256 * logarithmicCap N * H)) ≤
        Real.log N) :
    4 ≤ H ∧
      1 ≤ logarithmicCap N ∧
      1 ≤ RungeLogarithmicGrowth.cappedRadius
        N H (logarithmicCap N) ∧
      RungeLogarithmicGrowth.cappedRadius
          N H (logarithmicCap N) ≤ logarithmicCap N ∧
      (7 * H) / Nat.log 2 H + 1 ≤
        codingConstant c₁ c₂ *
          RungeLogarithmicGrowth.cappedRadius
            N H (logarithmicCap N) := by
  have hH : 4 ≤ H :=
    four_le_H_of_criticalWindow hwindow hfour
  have hT : 1 ≤ logarithmicCap N :=
    one_le_logarithmicCap hN
  have hA : 1 ≤ codingConstant c₁ c₂ :=
    one_le_codingConstant hwindow.1 hwindow.2.1
  have hrequired :
      requiredRadius H (codingConstant c₁ c₂) ≤
        RungeLogarithmicGrowth.cappedRadius
          N H (logarithmicCap N) :=
    le_cappedRadius_of_scaled_log_le (by omega) hT hscale
  have hpositive :
      1 ≤ RungeLogarithmicGrowth.cappedRadius
        N H (logarithmicCap N) :=
    (one_le_requiredRadius hA).trans hrequired
  have hbelow :
      RungeLogarithmicGrowth.cappedRadius
          N H (logarithmicCap N) ≤ logarithmicCap N :=
    cappedRadius_le_logarithmicCap (by omega) hT
  have hbudget :
      (7 * H) / Nat.log 2 H + 1 ≤
        codingConstant c₁ c₂ *
          RungeLogarithmicGrowth.cappedRadius
            N H (logarithmicCap N) :=
    chebyshev_budget_of_scaled_log_le (by omega) hT hA hscale
  exact ⟨hH, hT, hpositive, hbelow, hbudget⟩

/--
Critical-window specialization of the finite weighted defect-mass estimate.

The conclusion is equation (3.4)'s explicit finite precursor.  Apart from
the interval-family bounds, its only analytic assumptions are the three
displayed real thresholds `hfour`, `htranslation`, and `hscale`.
-/
theorem sum_two_pow_localCount_sub_one_cast_le_of_criticalWindow
    {c₁ c₂ : ℝ} {N H X : ℕ}
    (starts : Finset ℕ)
    (hwindow : InCriticalWindow c₁ c₂ N H)
    (hN : 2 ≤ N)
    (hfour : (4 : ℝ) ≤ c₁ * Real.log N)
    (htranslation :
      2 * c₂ * Real.log N ≤ (N : ℝ))
    (hstartLower : ∀ u ∈ starts, N ≤ u)
    (hstartUpper : ∀ u ∈ starts, u + H ≤ X)
    (hscale :
      (requiredRadius H (codingConstant c₁ c₂) : ℝ) *
          (8 * Real.log
            (256 * logarithmicCap N * H)) ≤
        Real.log N) :
    let A := codingConstant c₁ c₂
    let T := logarithmicCap N
    let t := RungeLogarithmicGrowth.cappedRadius N H T
    let defects :=
      WeightedDefectCounting.positiveDefectValues
        (DefectCounting.smallPrimesUpTo H) X
    ((∑ u ∈ starts,
        (2 ^ IntervalDefectAggregation.localCount defects H u - 1) : ℕ) :
        ℝ) ≤
      (H + 1 : ℝ) * Real.sqrt X *
        Real.exp (2 * Real.sqrt H) *
        ((2 ^ (2 * t * 2 ^ (A + 1)) : ℕ) : ℝ) := by
  dsimp only
  obtain ⟨hH, hT, ht, htT, hbudget⟩ :=
    cappedRadius_conditions_of_criticalWindow
      hwindow hN hfour hscale
  exact
    WeightedDefectMass.sum_two_pow_localCount_sub_one_cast_le_of_cappedRadius
      starts hH
      (two_mul_H_le_N_of_criticalWindow hwindow htranslation)
      hstartLower hstartUpper hT ht htT hbudget

end CriticalWindowParameters
end PaperC
