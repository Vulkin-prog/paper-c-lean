import PaperCV282.PrimeEulerRankin

/-!
# Explicit discretization of the exponential prime cutoff

These bounds retain the floor instead of treating it as an asymptotic
identity. The numerical loss is at most a factor two in the reciprocal
cutoff and an additive log 2 in its logarithm.
-/

namespace PaperC.V282.PrimeEulerCutoff

open DefectCounting DefectiveRankinCount PrimeEulerRankin

noncomputable section

/-- Uniform finite rounding bounds for the literal cutoff floor(exp w). -/
theorem floor_exp_bounds {w : ℝ} (hw : Real.log 4 ≤ w) :
    4 ≤ ⌊Real.exp w⌋₊ ∧ Real.exp w / 2 ≤ (⌊Real.exp w⌋₊ : ℝ) ∧
      (⌊Real.exp w⌋₊ : ℝ) ≤ Real.exp w ∧
      w - Real.log 2 ≤ Real.log (⌊Real.exp w⌋₊ : ℕ) := by
  have hexp : (4 : ℝ) ≤ Real.exp w := by
    calc
      (4 : ℝ) = Real.exp (Real.log 4) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp w := Real.exp_le_exp.mpr hw
  have hfloor : 4 ≤ ⌊Real.exp w⌋₊ := (Nat.le_floor_iff (Real.exp_nonneg w)).mpr (by exact hexp)
  have hfloorreal : (4 : ℝ) ≤ (⌊Real.exp w⌋₊ : ℝ) := by exact_mod_cast hfloor
  have hclose := Nat.lt_floor_add_one (Real.exp w)
  have hhalf : Real.exp w / 2 ≤ (⌊Real.exp w⌋₊ : ℝ) := by linarith
  refine ⟨hfloor, hhalf, Nat.floor_le (Real.exp_nonneg w), ?_⟩
  have hlog := Real.log_le_log (by positivity : 0 < Real.exp w / 2) hhalf
  simpa only [Real.log_div (Real.exp_ne_zero w) (by norm_num : (2 : ℝ) ≠ 0), Real.log_exp] using hlog

/-- The reciprocal floor differs from exp(-w) by at most the factor two. -/
theorem inv_floor_exp_le_two_exp_neg {w : ℝ} (hw : Real.log 4 ≤ w) :
    1 / (⌊Real.exp w⌋₊ : ℝ) ≤ 2 * Real.exp (-w) := by
  have hhalf := (floor_exp_bounds hw).2.1
  calc
    _ ≤ 1 / (Real.exp w / 2) := one_div_le_one_div_of_le (by positivity) hhalf
    _ = _ := by rw [Real.exp_neg]; ring

/-- Nonnegative powers preserve the floor upper bound without a rounding error. -/
theorem floor_exp_rpow_le_exp (w : ℝ) {zeta : ℝ} (hzeta : 0 ≤ zeta) :
    (⌊Real.exp w⌋₊ : ℝ) ^ zeta ≤ Real.exp (w * zeta) := by
  calc
    _ ≤ (Real.exp w) ^ zeta := Real.rpow_le_rpow (by positivity) (Nat.floor_le (Real.exp_nonneg w)) hzeta
    _ = _ := by rw [Real.exp_mul]

/-- The completely proved logarithmic envelope at an exponentially varying cutoff.
This upper bound has an explicit constant; it does not replace the PNT main term. -/
theorem rankinEulerProduct_floor_exp_le {w zeta : ℝ} (hw : Real.log 4 ≤ w) (hzeta : 0 ≤ zeta) :
    rankinEulerProduct ⌊Real.exp w⌋₊ zeta ≤
      Real.exp (120 * Real.exp (w * zeta) * Real.log (w + Real.log 3)) := by
  let Y := ⌊Real.exp w⌋₊
  obtain ⟨hYfour, _, hYupper, _⟩ := floor_exp_bounds hw
  have hY : 3 ≤ Y := by dsimp [Y]; omega
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  have hrecip := V11.PrimeHarmonic.sum_inv_smallPrimesUpTo_real_le_loglog Y hY
  have hrecipnonneg : 0 ≤ ∑ p ∈ smallPrimesUpTo Y, (p : ℝ)⁻¹ := Finset.sum_nonneg (fun p _ => by positivity)
  have hloglog : 0 ≤ Real.log (Real.log ((3 * Y : ℕ) : ℝ)) := by linarith
  have hinnerpos : 0 < Real.log ((3 * Y : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < 3 * Y by omega))
  have hlogupper : Real.log ((3 * Y : ℕ) : ℝ) ≤ w + Real.log 3 := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < (3 * Y : ℕ))
      (show ((3 * Y : ℕ) : ℝ) ≤ 3 * Real.exp w by push_cast; dsimp [Y]; nlinarith)
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (Real.exp_ne_zero w), Real.log_exp] at hh
    linarith
  have houter := Real.log_le_log hinnerpos hlogupper
  have hpow := floor_exp_rpow_le_exp w hzeta
  have hbound : (Y : ℝ) ^ zeta * (120 * Real.log (Real.log ((3 * Y : ℕ) : ℝ))) ≤
      120 * Real.exp (w * zeta) * Real.log (w + Real.log 3) := by
    have hfirst := mul_le_mul_of_nonneg_right hpow (mul_nonneg (by norm_num : (0 : ℝ) ≤ 120) hloglog)
    have hsecond := mul_le_mul_of_nonneg_left houter (by positivity : 0 ≤ 120 * Real.exp (w * zeta))
    dsimp [Y] at *
    nlinarith
  exact (rankinEulerProduct_le_exp_loglog hY hzeta).trans (Real.exp_le_exp.mpr hbound)

/-- Explicit cutoff-discretized Rankin bound for actual positive defective integers. -/
theorem normalized_defectiveValues_floor_exp_le {X : ℕ} (hX : 0 < X) {w zeta : ℝ}
    (hw : Real.log 4 ≤ w) (hzeta : 0 ≤ zeta) (hzetaHalf : zeta ≤ 1 / 2) :
    ((defectiveValues X ⌊Real.exp w⌋₊).card : ℝ) / X ≤
      Real.exp (-zeta * Real.log X + 120 * Real.exp (w * zeta) * Real.log (w + Real.log 3)) := by
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX
  calc
    _ ≤ (X : ℝ) ^ (-zeta) * rankinEulerProduct ⌊Real.exp w⌋₊ zeta :=
      normalized_defectiveValues_le_rankin hX _ hzetaHalf
    _ ≤ (X : ℝ) ^ (-zeta) * Real.exp (120 * Real.exp (w * zeta) * Real.log (w + Real.log 3)) :=
      mul_le_mul_of_nonneg_left (rankinEulerProduct_floor_exp_le hw hzeta) (by positivity)
    _ = _ := by rw [Real.rpow_def_of_pos hXpos, ← Real.exp_add]; congr 1; ring

end
end PaperC.V282.PrimeEulerCutoff
