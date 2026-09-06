import PaperCV282.SectorSevenRank
import PaperCV282.CappedSectorMass

/-!
# Exact weights in the eighth residual sector

The actual rank/slack index is retained in the finite inequalities. Every
terminal pair has weight at most four times the word count. When fewer
than two small kernels are guaranteed by the index, its weight instead
has the two-thirds word-space bound. This separates the energy and
container branches without a geometric summation of intermediate strata.
-/

namespace PaperC.V282.SectorEightWeights

open PropositionSixteenOne BoundedRatioCanonicalTerminalPopulation
open ResidualComponentCounts ResidualSectorPartition ResidualSectorMass
open CappedRelationMass CappedSectorMass

noncomputable section

/-- The systematic weight is zero on the actual terminal sector. -/
theorem residualWeight_eq_two_pow_tau_sub_one
    {N M A L : ℕ} (hN : 2 ≤ N) (pair : SeparatedBoundedRatioPair N M L)
    (height : sectorOf A hN pair = 7) :
    residualWeight A hN pair = 2 ^ pairTau A hN pair - 1 := by
  have hs := sigma_eq_zero_of_sector_at_least_five hN pair
    (show 4 ≤ (sectorOf A hN pair).val by rw [height]; decide)
  simp only [residualWeight, hs, pow_zero, one_mul]

/-- The exact dimension budget gives a uniform factor four, independent of any cap. -/
theorem residualWeight_le_four_wordCount
    {N M A L : ℕ} (hN : 2 ≤ N) (pair : SeparatedBoundedRatioPair N M L)
    (height : sectorOf A hN pair = 7) :
    residualWeight A hN pair ≤ 4 * 2 ^ (L + 1) := by
  have hlate : 4 ≤ (sectorOf A hN pair).val := by rw [height]; decide
  have hdeep : 6 ≤ (sectorOf A hN pair).val := by rw [height]; decide
  have hadd := slack_add_rank_add_tau_of_sector_at_least_five hN pair hlate
  have hd := (dense_core_and_few_defects_of_sector_at_least_seven hN pair hdeep).2
  have htau : pairTau A hN pair ≤ L + 1 + 2 := by omega
  rw [residualWeight_eq_two_pow_tau_sub_one hN pair height]
  calc
    _ ≤ 2 ^ pairTau A hN pair := Nat.sub_le _ _
    _ ≤ 2 ^ (L + 1 + 2) := Nat.pow_le_pow_right (by omega) htau
    _ = _ := by rw [pow_add]; norm_num; ring

/-- Real pointwise form for finite mass and incidence bounds. -/
theorem residualWeight_cast_le_four_wordCount
    {N M A L : ℕ} (hN : 2 ≤ N) (pair : SeparatedBoundedRatioPair N M L)
    (height : sectorOf A hN pair = 7) :
    (residualWeight A hN pair : ℝ) ≤ 4 * (2 : ℝ) ^ (L + 1) := by
  exact_mod_cast residualWeight_le_four_wordCount hN pair height

/-- The same real ceiling survives the uniform factor four. -/
theorem capped_residualWeight_le_four_min_wordCount
    {N M A L : ℕ} (hN : 2 ≤ N) (pair : SeparatedBoundedRatioPair N M L)
    (height : sectorOf A hN pair = 7) {T : ℝ} (hT : 0 ≤ T) :
    min T (residualWeight A hN pair : ℝ) ≤ 4 * min T ((2 : ℝ) ^ (L + 1)) :=
  (min_le_min_left T (residualWeight_cast_le_four_wordCount hN pair height)).trans
    (min_mul_le_mul_min (by norm_num) hT)

/-- The exceptional small-kernel branch forces a two-thirds dimension envelope. -/
theorem three_mul_tau_le_two_runLength_add_eight
    {N M A L : ℕ} (hN : 2 ≤ N) (pair : SeparatedBoundedRatioPair N M L)
    (height : sectorOf A hN pair = 7)
    (hexception : L + 1 - 3 * (boundedTerminalSlack A pair + boundedCanonicalSmallRowRank A pair) - 1 ≤ 1) :
    3 * pairTau A hN pair ≤ 2 * (L + 1) + 8 := by
  have hlate : 4 ≤ (sectorOf A hN pair).val := by rw [height]; decide
  have hdeep : 6 ≤ (sectorOf A hN pair).val := by rw [height]; decide
  have hadd := slack_add_rank_add_tau_of_sector_at_least_five hN pair hlate
  have hd := (dense_core_and_few_defects_of_sector_at_least_seven hN pair hdeep).2
  omega

/-- The exceptional branch has the same fixed envelope as a two-thirds rank loss. -/
theorem exceptional_residualWeight_cast_le_eight_wordCount_two_thirds
    {N M A L : ℕ} (hN : 2 ≤ N) (pair : SeparatedBoundedRatioPair N M L)
    (height : sectorOf A hN pair = 7)
    (hexception : L + 1 - 3 * (boundedTerminalSlack A pair + boundedCanonicalSmallRowRank A pair) - 1 ≤ 1) :
    (residualWeight A hN pair : ℝ) ≤ 8 * ((2 : ℝ) ^ (L + 1)) ^ (2 / (3 : ℝ)) := by
  have ht := three_mul_tau_le_two_runLength_add_eight hN pair height hexception
  have htau : (pairTau A hN pair : ℝ) ≤ (L + 1 : ℝ) * (2 / (3 : ℝ)) + 3 := by
    have hc : (3 : ℝ) * pairTau A hN pair ≤ 2 * (L + 1 : ℝ) + 8 := by exact_mod_cast ht
    linarith
  have hw : residualWeight A hN pair ≤ 2 ^ pairTau A hN pair := by
    rw [residualWeight_eq_two_pow_tau_sub_one hN pair height]
    exact Nat.sub_le _ _
  calc
    _ ≤ (2 : ℝ) ^ pairTau A hN pair := by exact_mod_cast hw
    _ = (2 : ℝ) ^ (pairTau A hN pair : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ (2 : ℝ) ^ ((L + 1 : ℝ) * (2 / (3 : ℝ)) + 3) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) htau
    _ = _ := by
      rw [Real.rpow_add (by norm_num), Real.rpow_mul (by norm_num)]
      rw [show (L + 1 : ℝ) = ((L + 1 : ℕ) : ℝ) by norm_cast, Real.rpow_natCast]
      norm_num
      ring

end
end PaperC.V282.SectorEightWeights
