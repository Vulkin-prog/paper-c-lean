import PaperCV282.ResidualSectorMass

/-!
# The actual rank deficit in residual sector 7

The exact small-row rank and the integer budget give the pointwise
`Q_B^(2/3)` envelope used in Section 3.4. The final estimates reduce the
sector mass to the cardinality of its actual pair set. They do not assert
the separate arithmetic estimate for the number of deep hosts.
-/

namespace PaperC.V282.SectorSevenRank

open PropositionSixteenOne BoundedRatioCanonicalTerminalPopulation
open ResidualComponentCounts ResidualSectorPartition ResidualSectorMass
open scoped BigOperators

noncomputable section

/-- Integrality strengthens the strict seventh-sector rank test by one. -/
theorem rankBudget_add_one_le_slack_add_rank
    {N M A L : ℕ} (hN : 2 ≤ N) (pair : SeparatedBoundedRatioPair N M L)
    (hseven : sectorOf A hN pair = 6) :
    rankBudget L + 1 ≤
      ((boundedTerminalSlack A pair + boundedCanonicalSmallRowRank A pair : ℕ) : ℤ) := by
  have htest := (sectorOf_eq_seven_iff.mp hseven).2.2.2.2.2.2
  unfold exceedsRankBudget at htest
  omega

/-- Literal version of the manuscript inequality `tau <= B+1-T_B`. -/
theorem tau_add_rankBudget_le_runLength_add_one
    {N M A L : ℕ} (hN : 2 ≤ N) (pair : SeparatedBoundedRatioPair N M L)
    (hseven : sectorOf A hN pair = 6) :
    (pairTau A hN pair : ℤ) + rankBudget L ≤ (L : ℤ) + 2 := by
  have hlate : 4 ≤ (sectorOf A hN pair).val := by rw [hseven]; decide
  have hdeep : 6 ≤ (sectorOf A hN pair).val := by rw [hseven]; decide
  have hrank := rankBudget_add_one_le_slack_add_rank hN pair hseven
  have hadd := slack_add_rank_add_tau_of_sector_at_least_five hN pair hlate
  have hdef := (dense_core_and_few_defects_of_sector_at_least_seven hN pair hdeep).2
  omega

/-- A denominator-free envelope, including every residue class of `B` modulo three. -/
theorem three_mul_tau_le_two_runLength_add_seven
    {N M A L : ℕ} (hN : 2 ≤ N) (pair : SeparatedBoundedRatioPair N M L)
    (hseven : sectorOf A hN pair = 6) :
    3 * pairTau A hN pair ≤ 2 * (L + 1) + 7 := by
  have hbudget := tau_add_rankBudget_le_runLength_add_one hN pair hseven
  unfold rankBudget at hbudget
  omega

/-- The nonaligned seventh sector has no systematic factor in its residual weight. -/
theorem residualWeight_eq_two_pow_tau_sub_one
    {N M A L : ℕ} (hN : 2 ≤ N) (pair : SeparatedBoundedRatioPair N M L)
    (hseven : sectorOf A hN pair = 6) :
    residualWeight A hN pair = 2 ^ pairTau A hN pair - 1 := by
  have hsigma := sigma_eq_zero_of_sector_at_least_five hN pair
    (show 4 ≤ (sectorOf A hN pair).val by rw [hseven]; decide)
  simp only [residualWeight, hsigma, pow_zero, one_mul]

/-- Explicit real pointwise envelope with `Q_B = 2^(L+1)`. -/
theorem residualWeight_cast_le_eight_wordCount_two_thirds
    {N M A L : ℕ} (hN : 2 ≤ N) (pair : SeparatedBoundedRatioPair N M L)
    (hseven : sectorOf A hN pair = 6) :
    (residualWeight A hN pair : ℝ) ≤
      8 * ((2 : ℝ) ^ (L + 1)) ^ (2 / (3 : ℝ)) := by
  have htau := three_mul_tau_le_two_runLength_add_seven hN pair hseven
  have htauReal : (pairTau A hN pair : ℝ) ≤
      (L + 1 : ℝ) * (2 / (3 : ℝ)) + 3 := by
    have hcast : (3 : ℝ) * pairTau A hN pair ≤ 2 * (L + 1 : ℝ) + 7 := by
      exact_mod_cast htau
    linarith
  have hweight : residualWeight A hN pair ≤ 2 ^ pairTau A hN pair := by
    rw [residualWeight_eq_two_pow_tau_sub_one hN pair hseven]
    exact Nat.sub_le _ _
  calc
    (residualWeight A hN pair : ℝ) ≤ (2 : ℝ) ^ pairTau A hN pair := by
      exact_mod_cast hweight
    _ = (2 : ℝ) ^ (pairTau A hN pair : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ (2 : ℝ) ^ ((L + 1 : ℝ) * (2 / (3 : ℝ)) + 3) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) htauReal
    _ = 8 * ((2 : ℝ) ^ (L + 1)) ^ (2 / (3 : ℝ)) := by
      rw [Real.rpow_add (by norm_num), Real.rpow_mul (by norm_num)]
      rw [show (L + 1 : ℝ) = ((L + 1 : ℕ) : ℝ) by norm_cast, Real.rpow_natCast]
      norm_num
      ring

/-- A finite mass bound using the actual cardinality of the seventh sector. -/
theorem sectorMassNat_cast_le_card_mul_wordCount_two_thirds
    {N M A L : ℕ} (hN : 2 ≤ N) :
    (sectorMassNat (M := M) (L := L) A hN 6 : ℝ) ≤
      ((sectorPairs N M A L hN 6).card : ℝ) *
        (8 * ((2 : ℝ) ^ (L + 1)) ^ (2 / (3 : ℝ))) := by
  classical
  unfold sectorMassNat
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ _pair ∈ sectorPairs N M A L hN 6,
        (8 * ((2 : ℝ) ^ (L + 1)) ^ (2 / (3 : ℝ))) := by
      apply Finset.sum_le_sum
      intro pair hpair
      exact residualWeight_cast_le_eight_wordCount_two_thirds hN pair
        (mem_sectorPairs.mp hpair)
    _ = _ := by simp

/-- The real sector mass uses the same finite pair set and the same explicit envelope. -/
theorem sectorMass_le_card_mul_wordCount_two_thirds
    {N M A L : ℕ} (hN : 2 ≤ N) :
    sectorMass A 6 N M L ≤
      ((sectorPairs N M A L hN 6).card : ℝ) *
        (8 * ((2 : ℝ) ^ (L + 1)) ^ (2 / (3 : ℝ))) := by
  simpa only [sectorMass, dif_pos hN] using
    sectorMassNat_cast_le_card_mul_wordCount_two_thirds (M := M) (A := A) (L := L) hN

end
end PaperC.V282.SectorSevenRank
