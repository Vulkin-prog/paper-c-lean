import PaperCV282.SoftRateAssembly

/-!
# Independent deletion and graph errors in the actual soft ledger

The two exponential costs remain separate at a free cutoff. The source
law and both Stein factors are unchanged, and no intensity-growth premise
is required by the finite normalized bound.
-/

namespace PaperC.V282.SoftRateLedger

open ScalarSteinInput PoissonIntensityBounds SoftPoissonRates SoftRateAssembly
open AllStartSoftPoisson FullBandArithmetic DyadicPoissonDistance
open SoftArithmeticTransfer MaskedArithmeticGeometry CutoffGraphDegree
open TouchingPairMass TwoWindowParity SectionTwelveMoments
open scoped NNReal

noncomputable section

theorem softBudget_le_independent_costs {rate : ℝ≥0}
    {diagonal defect degree relation touching bad P b e : ℝ}
    (hP : 0 ≤ P) (hPone : P ≤ 1) (hdegree : 0 ≤ degree) (hb : 0 ≤ b)
    (hdiagonal : diagonal ≤ P) (hdefect : defect ≤ P) (htouching : touching ≤ P)
    (hrelation : relation ≤ P * ((rate : ℝ) ^ 2 + 2 * (rate : ℝ)))
    (hdegreeExp : degree ≤ e)
    (hbadExp : bad ≤ b) :
    softBudget rate diagonal defect degree relation touching bad ≤
      2 * Real.sqrt (intensityEnvelope rate) * b + 3 * intensityEnvelope rate * e +
        6 * intensityEnvelope rate * P := by
  let K := intensityEnvelope rate
  have hK : 1 ≤ K := one_le_intensityEnvelope rate
  have hK0 : 0 ≤ K := by linarith
  have hq : 0 ≤ Real.sqrt K := Real.sqrt_nonneg _
  have hmain : diagonal + degree * (defect + 2) + touching ≤ 2 * P + 3 * degree := by
    nlinarith
  have hfirst : firstSteinFactor rate * (rate : ℝ) ^ 2 *
      (diagonal + degree * (defect + 2) + touching) ≤
      2 * K * P + 3 * K * e := by
    calc
      _ ≤ firstSteinFactor rate * (rate : ℝ) ^ 2 * (2 * P + 3 * degree) :=
        mul_le_mul_of_nonneg_left hmain (mul_nonneg (firstSteinFactor_nonneg rate) (sq_nonneg _))
      _ ≤ K * (2 * P + 3 * degree) :=
        mul_le_mul_of_nonneg_right (firstSteinFactor_mul_square_le_max_one rate) (by positivity)
      _ ≤ 2 * K * P + 3 * K * e := by nlinarith
  have hrelation' : firstSteinFactor rate * relation ≤ 3 * K * P := by
    calc
      _ ≤ firstSteinFactor rate * (P * ((rate : ℝ) ^ 2 + 2 * (rate : ℝ))) :=
        mul_le_mul_of_nonneg_left hrelation (firstSteinFactor_nonneg rate)
      _ = P * (firstSteinFactor rate * ((rate : ℝ) ^ 2 + 2 * (rate : ℝ))) := by ring
      _ ≤ P * ((rate : ℝ) + 2) :=
        mul_le_mul_of_nonneg_left (firstSteinFactor_mul_square_add_twice_le rate) hP
      _ ≤ 3 * K * P := by have hr : (rate : ℝ) ≤ K := le_max_right _ _; nlinarith
  have hbad : zeroSteinFactor rate * (rate : ℝ) * (defect + 2 * bad) ≤
      K * P + 2 * Real.sqrt K * b := by
    calc
      _ ≤ zeroSteinFactor rate * (rate : ℝ) * (P + 2 * b) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (zeroSteinFactor_nonneg rate) rate.coe_nonneg)
      _ ≤ Real.sqrt K * (P + 2 * b) :=
        mul_le_mul_of_nonneg_right (zeroSteinFactor_mul_le_sqrt_max_one rate) (by positivity)
      _ ≤ K * P + 2 * Real.sqrt K * b := by
        have hs := sqrt_intensityEnvelope_le rate
        nlinarith
  unfold softBudget
  change _ ≤ 2 * Real.sqrt K * b + 3 * K * e + 6 * K * P
  nlinarith

/-- The actual mean conditional distance with separately estimated deletion and degree. -/
theorem conditionalDistance_le_independent_costs (hStein : ScalarSteinFactorsStatement)
    {N L Y : ℕ} {P b e : ℝ} (hN : 2 ≤ N) (hL : 0 < L) (hY : L + 1 ≤ Y)
    (hP : 0 ≤ P) (hPone : P ≤ 1) (hb : 0 ≤ b)
    (hu : 1 / (N : ℝ) ≤ P)
    (hm : (fullDefectMass L (dyadicBlock N) : ℝ) / N ≤ P)
    (ht : homogeneousTouchingMass (dyadicCutoff N L) L (dyadicBlock N) / (N : ℝ) ^ 2 ≤ P)
    (hr : (jointDefectMass N L (separatedPairs (dyadicBlock N) L) : ℝ) / (2 : ℝ) ^ (2 * L) ≤
      P * ((fullRate N L : ℝ) ^ 2 + 2 * (fullRate N L : ℝ)))
    (he : (cutoffMaxDegree L Y (dyadicBlock N) : ℝ) / N ≤ e)
    (hd : ((fullBadStarts N L Y).card : ℝ) / N ≤ b) :
    conditionalDistance N L Y ≤
      2 * Real.sqrt (intensityEnvelope (fullRate N L)) * b +
        3 * intensityEnvelope (fullRate N L) * e + 6 * intensityEnvelope (fullRate N L) * P := by
  have h := average_conditionalMaskedLaw_soft_le hStein hN hL hY
  change conditionalDistance N L Y ≤ _ at h
  rw [softArithmeticBudget_eq_normalized N L Y (by omega)] at h
  exact h.trans (softBudget_le_independent_costs hP hPone (by positivity) hb hu hm ht hr he hd)

end
end PaperC.V282.SoftRateLedger
