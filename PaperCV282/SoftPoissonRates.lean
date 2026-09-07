import PaperCV282.PoissonIntensityBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Numerical soft rates for every intensity

The positive logarithm is max(0,log lambda), including lambda=0. The
nontrivial branch of the final minimum forces this logarithm below the
cutoff scale. Only in that branch is the intensity absorbed into a small
power of the ambient scale. No global subpolynomial-intensity hypothesis
is imposed.
-/

namespace PaperC.V282.SoftPoissonRates

open ScalarSteinInput PoissonIntensityBounds
open scoped NNReal

noncomputable section

def positiveLog (rate : ℝ≥0) : ℝ := max 0 (Real.log (rate : ℝ))

def intensityEnvelope (rate : ℝ≥0) : ℝ := max 1 (rate : ℝ)

def softExponential (rate : ℝ≥0) (w error : ℝ) : ℝ :=
  Real.exp (-(w - positiveLog rate) / 2 + error)

def softBudget (rate : ℝ≥0) (diagonal defect degree relation touching bad : ℝ) : ℝ :=
  firstSteinFactor rate * ((rate : ℝ) ^ 2 *
    (diagonal + degree * (defect + 2) + touching) + relation) +
      zeroSteinFactor rate * (rate : ℝ) * (defect + 2 * bad)

theorem one_le_intensityEnvelope (rate : ℝ≥0) : 1 ≤ intensityEnvelope rate := le_max_left _ _

theorem exp_positiveLog (rate : ℝ≥0) : Real.exp (positiveLog rate) = intensityEnvelope rate := by
  by_cases hz : rate = 0
  · simp [hz, positiveLog, intensityEnvelope]
  · have hp : (0 : ℝ) < rate := by exact_mod_cast (pos_iff_ne_zero.mpr hz)
    by_cases hlarge : 1 ≤ (rate : ℝ)
    · rw [positiveLog, max_eq_right (Real.log_nonneg hlarge), Real.exp_log hp,
        intensityEnvelope, max_eq_right hlarge]
    · have hsmall : (rate : ℝ) ≤ 1 := le_of_not_ge hlarge
      rw [positiveLog, max_eq_left (Real.log_nonpos rate.coe_nonneg hsmall), Real.exp_zero,
        intensityEnvelope, max_eq_left hsmall]

theorem sqrt_intensityEnvelope_eq_exp (rate : ℝ≥0) :
    Real.sqrt (intensityEnvelope rate) = Real.exp (positiveLog rate / 2) := by
  apply (Real.sqrt_eq_iff_mul_self_eq_of_pos (Real.exp_pos _)).mpr
  rw [← Real.exp_add, show positiveLog rate / 2 + positiveLog rate / 2 = positiveLog rate by ring,
    exp_positiveLog]

theorem sqrt_intensityEnvelope_le (rate : ℝ≥0) :
    Real.sqrt (intensityEnvelope rate) ≤ intensityEnvelope rate := by
  have hk := one_le_intensityEnvelope rate
  have hs := Real.sq_sqrt (show 0 ≤ intensityEnvelope rate by linarith)
  nlinarith [Real.sqrt_nonneg (intensityEnvelope rate)]

theorem sqrt_envelope_mul_exp (rate : ℝ≥0) (w error : ℝ) :
    Real.sqrt (intensityEnvelope rate) * Real.exp (-w / 2 + error) = softExponential rate w error := by
  rw [sqrt_intensityEnvelope_eq_exp, ← Real.exp_add]
  congr 1
  ring

theorem envelope_mul_exp (rate : ℝ≥0) (w error : ℝ) :
    intensityEnvelope rate * Real.exp (-w + error) = Real.exp (positiveLog rate - w + error) := by
  rw [← exp_positiveLog, ← Real.exp_add]
  congr 1
  ring

theorem positiveLog_le_cutoff_of_softExponential_le_one {rate : ℝ≥0} {w error : ℝ}
    (herror : 0 ≤ error) (hsmall : softExponential rate w error ≤ 1) :
    positiveLog rate ≤ w := by
  have h := Real.exp_le_one_iff.mp hsmall
  change -(w - positiveLog rate) / 2 + error ≤ 0 at h
  linarith

theorem degree_exponential_le_softExponential {rate : ℝ≥0} {w error : ℝ}
    (herror : 0 ≤ error) (hsmall : softExponential rate w error ≤ 1) :
    Real.exp (positiveLog rate - w + error) ≤ softExponential rate w error := by
  have h := positiveLog_le_cutoff_of_softExponential_le_one herror hsmall
  apply Real.exp_le_exp.mpr
  change positiveLog rate - w + error ≤ -(w - positiveLog rate) / 2 + error
  linarith

theorem intensityEnvelope_le_rpow_of_positiveLog_le {rate : ℝ≥0} {N w delta : ℝ}
    (hN : 0 < N) (hw : w ≤ delta * Real.log N) (hlog : positiveLog rate ≤ w) :
    intensityEnvelope rate ≤ N ^ delta := by
  rw [← exp_positiveLog, Real.rpow_def_of_pos hN]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem intensityEnvelope_mul_rpow_le {rate : ℝ≥0} {N w delta power : ℝ}
    (hN : 0 < N) (hw : w ≤ delta * Real.log N) (hlog : positiveLog rate ≤ w) :
    intensityEnvelope rate * N ^ power ≤ N ^ (power + delta) := by
  calc
    _ ≤ N ^ delta * N ^ power := mul_le_mul_of_nonneg_right
      (intensityEnvelope_le_rpow_of_positiveLog_le hN hw hlog) (Real.rpow_nonneg hN.le _)
    _ = _ := by rw [← Real.rpow_add hN]; congr 1; ring

theorem softBudget_le_exponentials {rate : ℝ≥0}
    {diagonal defect degree relation touching bad P w error : ℝ}
    (hP : 0 ≤ P) (hPone : P ≤ 1) (hdegree : 0 ≤ degree)
    (hdiagonal : diagonal ≤ P) (hdefect : defect ≤ P) (htouching : touching ≤ P)
    (hrelation : relation ≤ P * ((rate : ℝ) ^ 2 + 2 * (rate : ℝ)))
    (hdegreeExp : degree ≤ Real.exp (-w + error))
    (hbadExp : bad ≤ Real.exp (-w / 2 + error)) :
    softBudget rate diagonal defect degree relation touching bad ≤
      2 * softExponential rate w error + 3 * Real.exp (positiveLog rate - w + error) +
        6 * intensityEnvelope rate * P := by
  let K := intensityEnvelope rate
  have hK : 1 ≤ K := one_le_intensityEnvelope rate
  have hK0 : 0 ≤ K := by linarith
  have hq : 0 ≤ Real.sqrt K := Real.sqrt_nonneg _
  have hmain : diagonal + degree * (defect + 2) + touching ≤ 2 * P + 3 * degree := by
    nlinarith
  have hfirst : firstSteinFactor rate * (rate : ℝ) ^ 2 *
      (diagonal + degree * (defect + 2) + touching) ≤
      2 * K * P + 3 * K * Real.exp (-w + error) := by
    calc
      _ ≤ firstSteinFactor rate * (rate : ℝ) ^ 2 * (2 * P + 3 * degree) :=
        mul_le_mul_of_nonneg_left hmain (mul_nonneg (firstSteinFactor_nonneg rate) (sq_nonneg _))
      _ ≤ K * (2 * P + 3 * degree) :=
        mul_le_mul_of_nonneg_right (firstSteinFactor_mul_square_le_max_one rate) (by positivity)
      _ ≤ 2 * K * P + 3 * K * Real.exp (-w + error) := by nlinarith
  have hrelation' : firstSteinFactor rate * relation ≤ 3 * K * P := by
    calc
      _ ≤ firstSteinFactor rate * (P * ((rate : ℝ) ^ 2 + 2 * (rate : ℝ))) :=
        mul_le_mul_of_nonneg_left hrelation (firstSteinFactor_nonneg rate)
      _ = P * (firstSteinFactor rate * ((rate : ℝ) ^ 2 + 2 * (rate : ℝ))) := by ring
      _ ≤ P * ((rate : ℝ) + 2) :=
        mul_le_mul_of_nonneg_left (firstSteinFactor_mul_square_add_twice_le rate) hP
      _ ≤ 3 * K * P := by have hr : (rate : ℝ) ≤ K := le_max_right _ _; nlinarith
  have hbad : zeroSteinFactor rate * (rate : ℝ) * (defect + 2 * bad) ≤
      K * P + 2 * Real.sqrt K * Real.exp (-w / 2 + error) := by
    calc
      _ ≤ zeroSteinFactor rate * (rate : ℝ) * (P + 2 * Real.exp (-w / 2 + error)) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (zeroSteinFactor_nonneg rate) rate.coe_nonneg)
      _ ≤ Real.sqrt K * (P + 2 * Real.exp (-w / 2 + error)) :=
        mul_le_mul_of_nonneg_right (zeroSteinFactor_mul_le_sqrt_max_one rate) (by positivity)
      _ ≤ K * P + 2 * Real.sqrt K * Real.exp (-w / 2 + error) := by
        have hs := sqrt_intensityEnvelope_le rate
        nlinarith
  have hroot := sqrt_envelope_mul_exp rate w error
  have hlinear := envelope_mul_exp rate w error
  change Real.sqrt K * Real.exp (-w / 2 + error) = _ at hroot
  change K * Real.exp (-w + error) = _ at hlinear
  unfold softBudget
  nlinarith

theorem soft_rate_minimum_of_budget {rate : ℝ≥0}
    {value diagonal defect degree relation touching bad P S w error : ℝ}
    (hvalue : value ≤ 1) (herror : 0 ≤ error) (hP : 0 ≤ P) (hS : 0 ≤ S) (hdegree : 0 ≤ degree)
    (hdiagonal : diagonal ≤ P) (hdefect : defect ≤ P) (htouching : touching ≤ P)
    (hrelation : relation ≤ P * ((rate : ℝ) ^ 2 + 2 * (rate : ℝ)))
    (hdegreeExp : degree ≤ Real.exp (-w + error)) (hbadExp : bad ≤ Real.exp (-w / 2 + error))
    (hbudget : value ≤ softBudget rate diagonal defect degree relation touching bad)
    (habsorb : positiveLog rate ≤ w → intensityEnvelope rate * P ≤ S) :
    value ≤ 6 * min 1 (softExponential rate w error + S) := by
  by_cases htrivial : 1 ≤ softExponential rate w error + S
  · rw [min_eq_left htrivial]
    linarith
  · have hsmall : softExponential rate w error ≤ 1 := by linarith
    have hlog := positiveLog_le_cutoff_of_softExponential_le_one herror hsmall
    have habs := habsorb hlog
    have hPone : P ≤ 1 := by
      have hk := one_le_intensityEnvelope rate
      have hq : 0 < softExponential rate w error := Real.exp_pos _
      nlinarith
    have hb := softBudget_le_exponentials hP hPone hdegree hdiagonal hdefect htouching
      hrelation hdegreeExp hbadExp
    have hd := degree_exponential_le_softExponential herror hsmall
    rw [min_eq_right (le_of_not_ge htrivial)]
    have hq : 0 < softExponential rate w error := Real.exp_pos _
    linarith

theorem soft_rate_rpow_of_budget {rate : ℝ≥0}
    {value diagonal defect degree relation touching bad N power delta w error : ℝ}
    (hN : 0 < N) (hw : w ≤ delta * Real.log N)
    (hvalue : value ≤ 1) (herror : 0 ≤ error) (hdegree : 0 ≤ degree)
    (hdiagonal : diagonal ≤ N ^ power) (hdefect : defect ≤ N ^ power) (htouching : touching ≤ N ^ power)
    (hrelation : relation ≤ N ^ power * ((rate : ℝ) ^ 2 + 2 * (rate : ℝ)))
    (hdegreeExp : degree ≤ Real.exp (-w + error)) (hbadExp : bad ≤ Real.exp (-w / 2 + error))
    (hbudget : value ≤ softBudget rate diagonal defect degree relation touching bad) :
    value ≤ 6 * min 1 (softExponential rate w error + N ^ (power + delta)) := by
  apply soft_rate_minimum_of_budget hvalue herror (Real.rpow_nonneg hN.le _) (Real.rpow_nonneg hN.le _)
    hdegree hdiagonal hdefect htouching hrelation hdegreeExp hbadExp hbudget
  intro hlog
  exact intensityEnvelope_mul_rpow_le hN hw hlog

end

end PaperC.V282.SoftPoissonRates
