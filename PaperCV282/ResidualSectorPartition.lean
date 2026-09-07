import PaperC.Combinatorics.BoundedRatioCanonicalTerminalPopulation
import PaperCV282.MacroscopicRelationProfile

/-!
# The exact eight residual sectors of v2.8.2

This classifier applies the seven successive tests of Section 3.3 to the
actual canonical arithmetic data. Its `Fin 8` index is zero-based: index
zero is manuscript sector 1, and index seven is sector 8. The historical
seven-sector classifier is not used.

The last rank is the rank of the fixed arithmetic small-prime and parity
matrix. No terminal predicate or rank is supplied by the caller. The budget
`floor((B-2)/3)` is represented by integer division, so the definition also
remains literal when `B=1`. No sector-size estimate is asserted here.
-/

namespace PaperC.V282.ResidualSectorPartition

open Affine Affine.CanonicalRationalCode
open CanonicalResidualComponents ResidualComponentCounts
open PropositionSixteenOne BoundedRatioCanonicalTerminalPopulation
open SectionElevenPartition
open scoped BigOperators

noncomputable section

/-- The actual residual prime product is compared with the upper endpoint. -/
def smallPrimeProduct {N M L : ℕ} (A : ℕ) (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) : Prop :=
  canonicalResidualPrimeProduct (A := A) (L := L)
    (show 1 ≤ pair.1.1 from (by omega : 1 ≤ 2).trans (pair_coordinates_two_le hN pair).1)
    (show 1 ≤ pair.1.2 from (by omega : 1 ≤ 2).trans (pair_coordinates_two_le hN pair).2) ≤ M

/-- Sector 2 requires positive systematic dimension, as well as small height. -/
def smallPositiveChannel {N M L : ℕ} (A : ℕ)
    (pair : SeparatedBoundedRatioPair N M L) : Prop :=
  0 < pairSigma A pair ∧
    (RationalMassFinite.canonicalPairHeight A L pair.1.1 pair.1.2 : ℝ) ≤
      Real.sqrt (Real.log (L + 1 : ℝ))

/-- Exact integer form of the sector-3 test `c# ≤ B/6`. -/
def shallowCore {N M L : ℕ} (A : ℕ)
    (pair : SeparatedBoundedRatioPair N M L) : Prop :=
  6 * canonicalResidualComponentCount A pair.1.1 pair.1.2 L ≤ L + 1

/-- Exact integer form of the new sector-5 test `c# ≤ 2B/3`. -/
def moderateCore {N M L : ℕ} (A : ℕ)
    (pair : SeparatedBoundedRatioPair N M L) : Prop :=
  3 * canonicalResidualComponentCount A pair.1.1 pair.1.2 L ≤ 2 * (L + 1)

/-- Literal floor budget `T_B = floor((B-2)/3)`, including the case `B=1`. -/
def rankBudget (L : ℕ) : ℤ := ((L : ℤ) - 1) / 3

/-- Sector 7 is the strict rank-budget failure `s+ktilde > T_B`. -/
def exceedsRankBudget {N M L : ℕ} (A : ℕ)
    (pair : SeparatedBoundedRatioPair N M L) : Prop :=
  rankBudget L <
    ((boundedTerminalSlack A pair + boundedCanonicalSmallRowRank A pair : ℕ) : ℤ)

/-- Apply the seven literal tests in order; zero denotes manuscript sector 1. -/
def sectorOf {N M L : ℕ} (A : ℕ) (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) : Fin 8 := by
  classical
  exact
    if smallPrimeProduct A hN pair then 0
    else if smallPositiveChannel A pair then 1
    else if shallowCore A pair then 2
    else if IsCanonicallyAligned A L pair.1.1 pair.1.2 then 3
    else if moderateCore A pair then 4
    else if HasAtLeastThreeCorrectedDefects A L pair.1.1 pair.1.2 then 5
    else if exceedsRankBudget A pair then 6
    else 7

/-- Exact membership in manuscript sector 1, after all earlier tests fail. -/
theorem sectorOf_eq_one_iff
    {N M A L : ℕ} {hN : 2 ≤ N} {pair : SeparatedBoundedRatioPair N M L} :
    sectorOf A hN pair = 0 ↔
      smallPrimeProduct A hN pair := by
  classical
  unfold sectorOf
  split_ifs <;> simp_all

/-- Exact membership in manuscript sector 2, after all earlier tests fail. -/
theorem sectorOf_eq_two_iff
    {N M A L : ℕ} {hN : 2 ≤ N} {pair : SeparatedBoundedRatioPair N M L} :
    sectorOf A hN pair = 1 ↔
      ¬smallPrimeProduct A hN pair ∧
        smallPositiveChannel A pair := by
  classical
  unfold sectorOf
  split_ifs <;> simp_all

/-- Exact membership in manuscript sector 3, after all earlier tests fail. -/
theorem sectorOf_eq_three_iff
    {N M A L : ℕ} {hN : 2 ≤ N} {pair : SeparatedBoundedRatioPair N M L} :
    sectorOf A hN pair = 2 ↔
      ¬smallPrimeProduct A hN pair ∧
        ¬smallPositiveChannel A pair ∧
        shallowCore A pair := by
  classical
  unfold sectorOf
  split_ifs <;> simp_all

/-- Exact membership in manuscript sector 4, after all earlier tests fail. -/
theorem sectorOf_eq_four_iff
    {N M A L : ℕ} {hN : 2 ≤ N} {pair : SeparatedBoundedRatioPair N M L} :
    sectorOf A hN pair = 3 ↔
      ¬smallPrimeProduct A hN pair ∧
        ¬smallPositiveChannel A pair ∧
        ¬shallowCore A pair ∧
        IsCanonicallyAligned A L pair.1.1 pair.1.2 := by
  classical
  unfold sectorOf
  split_ifs <;> simp_all

/-- Exact membership in manuscript sector 5, after all earlier tests fail. -/
theorem sectorOf_eq_five_iff
    {N M A L : ℕ} {hN : 2 ≤ N} {pair : SeparatedBoundedRatioPair N M L} :
    sectorOf A hN pair = 4 ↔
      ¬smallPrimeProduct A hN pair ∧
        ¬smallPositiveChannel A pair ∧
        ¬shallowCore A pair ∧
        ¬IsCanonicallyAligned A L pair.1.1 pair.1.2 ∧
        moderateCore A pair := by
  classical
  unfold sectorOf
  split_ifs <;> simp_all

/-- Exact membership in manuscript sector 6, after all earlier tests fail. -/
theorem sectorOf_eq_six_iff
    {N M A L : ℕ} {hN : 2 ≤ N} {pair : SeparatedBoundedRatioPair N M L} :
    sectorOf A hN pair = 5 ↔
      ¬smallPrimeProduct A hN pair ∧
        ¬smallPositiveChannel A pair ∧
        ¬shallowCore A pair ∧
        ¬IsCanonicallyAligned A L pair.1.1 pair.1.2 ∧
        ¬moderateCore A pair ∧
        HasAtLeastThreeCorrectedDefects A L pair.1.1 pair.1.2 := by
  classical
  unfold sectorOf
  split_ifs <;> simp_all

/-- Exact membership in manuscript sector 7, after all earlier tests fail. -/
theorem sectorOf_eq_seven_iff
    {N M A L : ℕ} {hN : 2 ≤ N} {pair : SeparatedBoundedRatioPair N M L} :
    sectorOf A hN pair = 6 ↔
      ¬smallPrimeProduct A hN pair ∧
        ¬smallPositiveChannel A pair ∧
        ¬shallowCore A pair ∧
        ¬IsCanonicallyAligned A L pair.1.1 pair.1.2 ∧
        ¬moderateCore A pair ∧
        ¬HasAtLeastThreeCorrectedDefects A L pair.1.1 pair.1.2 ∧
        exceedsRankBudget A pair := by
  classical
  unfold sectorOf
  split_ifs <;> simp_all

/-- Exact membership in manuscript sector 8, after all earlier tests fail. -/
theorem sectorOf_eq_eight_iff
    {N M A L : ℕ} {hN : 2 ≤ N} {pair : SeparatedBoundedRatioPair N M L} :
    sectorOf A hN pair = 7 ↔
      ¬smallPrimeProduct A hN pair ∧
        ¬smallPositiveChannel A pair ∧
        ¬shallowCore A pair ∧
        ¬IsCanonicallyAligned A L pair.1.1 pair.1.2 ∧
        ¬moderateCore A pair ∧
        ¬HasAtLeastThreeCorrectedDefects A L pair.1.1 pair.1.2 ∧
        ¬exceedsRankBudget A pair := by
  classical
  unfold sectorOf
  split_ifs <;> simp_all

/-- The actual finite population of a sector, on the fixed interval. -/
def sectorPairs (N M A L : ℕ) (hN : 2 ≤ N) (sector : Fin 8) :
    Finset (SeparatedBoundedRatioPair N M L) := by
  classical
  exact Finset.univ.filter fun pair => sectorOf A hN pair = sector

@[simp]
theorem mem_sectorPairs {N M A L : ℕ} {hN : 2 ≤ N} {sector : Fin 8}
    {pair : SeparatedBoundedRatioPair N M L} :
    pair ∈ sectorPairs N M A L hN sector ↔ sectorOf A hN pair = sector := by
  classical
  simp [sectorPairs]

/-- Distinct sectors are disjoint, even when some residual weights vanish. -/
theorem sectorPairs_disjoint {N M A L : ℕ} (hN : 2 ≤ N)
    {s t : Fin 8} (hst : s ≠ t) :
    Disjoint (sectorPairs N M A L hN s) (sectorPairs N M A L hN t) := by
  classical
  rw [Finset.disjoint_left]
  intro pair hs ht
  exact hst ((mem_sectorPairs.mp hs).symm.trans (mem_sectorPairs.mp ht))

/-- Every separated pair has exactly one of the eight sector indices. -/
theorem existsUnique_sector {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) :
    ∃! sector : Fin 8, pair ∈ sectorPairs N M A L hN sector := by
  refine ⟨sectorOf A hN pair, mem_sectorPairs.mpr rfl, ?_⟩
  intro sector hs
  exact (mem_sectorPairs.mp hs).symm

/-- The eight populations exhaust the entire interval pair population. -/
theorem sectorPairs_cover {N M A L : ℕ} (hN : 2 ≤ N) :
    (Finset.univ.biUnion fun sector : Fin 8 => sectorPairs N M A L hN sector) =
      Finset.univ := by
  classical
  ext pair
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, mem_sectorPairs, iff_true]
  exact ⟨sectorOf A hN pair, rfl⟩

/-- The slack is an exact complement, not a truncated loss of components. -/
theorem slack_add_componentCount {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) :
    boundedTerminalSlack A pair +
        canonicalResidualComponentCount A pair.1.1 pair.1.2 L = L + 1 := by
  exact Nat.sub_add_cancel (canonicalResidualComponentCount_le_runLength hN pair)

/-- The rank in the terminal test satisfies the actual nonaligned rank identity. -/
theorem residualTau_add_rank_eq_corrected_add_components
    {N M A L : ℕ} (hN : 2 ≤ N) (pair : SeparatedBoundedRatioPair N M L)
    (hnonaligned : IsCanonicallyNonaligned A L pair.1.1 pair.1.2) :
    pairTau A hN pair + boundedCanonicalSmallRowRank A pair =
      canonicalCorrectedDefectCount A pair.1.1 pair.1.2 L +
        canonicalResidualComponentCount A pair.1.1 pair.1.2 L :=
  pairTau_add_canonicalRank_eq_corrected_add_components hN pair hnonaligned

/-- The integer budget uses the same natural quotient once `B ≥ 2`. -/
theorem rankBudget_eq_nat {L : ℕ} (hL : 1 ≤ L) :
    rankBudget L = (((L - 1) / 3 : ℕ) : ℤ) := by
  unfold rankBudget
  rw [Int.natCast_ediv, Nat.cast_sub hL]
  rfl

/-- The literal real floor is exactly the integer rank budget. -/
theorem rankBudget_eq_floor (L : ℕ) :
    rankBudget L = ⌊((L + 1 : ℝ) - 2) / 3⌋ := by
  unfold rankBudget
  change ((L : ℤ) - 1) / 3 = ⌊((L + 1 : ℝ) - 2) / ((3 : ℕ) : ℝ)⌋
  rw [Int.floor_div_natCast]
  congr 1
  norm_num
  omega

/-- Every sector after the alignment test is genuinely nonaligned. -/
theorem nonaligned_of_sector_at_least_five
    {N M A L : ℕ} (hN : 2 ≤ N) (pair : SeparatedBoundedRatioPair N M L)
    (hlate : 4 ≤ (sectorOf A hN pair).val) :
    IsCanonicallyNonaligned A L pair.1.1 pair.1.2 := by
  apply not_isCanonicallyAligned_iff_nonaligned.mp
  intro haligned
  unfold sectorOf at hlate
  split_ifs at hlate <;> simp_all

/-- The systematic exponent vanishes in sectors 5 through 8. -/
theorem sigma_eq_zero_of_sector_at_least_five
    {N M A L : ℕ} (hN : 2 ≤ N) (pair : SeparatedBoundedRatioPair N M L)
    (hlate : 4 ≤ (sectorOf A hN pair).val) : pairSigma A pair = 0 := by
  have hnone := nonaligned_of_sector_at_least_five hN pair hlate
  unfold IsCanonicallyNonaligned at hnone
  simp [pairSigma, RationalMassFinite.canonicalPairSigma, canonicalMultiplicity, hnone]

/-- In the late nonaligned sectors the corrected defect count is the original count. -/
theorem correctedDefects_eq_original_of_sector_at_least_five
    {N M A L : ℕ} (hN : 2 ≤ N) (pair : SeparatedBoundedRatioPair N M L)
    (hlate : 4 ≤ (sectorOf A hN pair).val) :
    canonicalCorrectedDefectCount A pair.1.1 pair.1.2 L =
      LargePrimeGraphResolution.defectiveVertexCount pair.1.1 pair.1.2 L := by
  have hnone := nonaligned_of_sector_at_least_five hN pair hlate
  unfold IsCanonicallyNonaligned at hnone
  simp [canonicalCorrectedDefectCount, hnone]

/-- In sectors 5 through 8 no exact component has been removed. -/
theorem residualComponents_eq_original_of_sector_at_least_five
    {N M A L : ℕ} (hN : 2 ≤ N) (pair : SeparatedBoundedRatioPair N M L)
    (hlate : 4 ≤ (sectorOf A hN pair).val) :
    canonicalResidualComponentCount A pair.1.1 pair.1.2 L =
      LargePrimeGraphResolution.nontrivialComponentCount pair.1.1 pair.1.2 L := by
  have hnone := nonaligned_of_sector_at_least_five hN pair hlate
  unfold IsCanonicallyNonaligned at hnone
  simp [canonicalResidualComponentCount, hnone]

/-- Sectors 7 and 8 have the paper's dense core and at most two corrected defects. -/
theorem dense_core_and_few_defects_of_sector_at_least_seven
    {N M A L : ℕ} (hN : 2 ≤ N) (pair : SeparatedBoundedRatioPair N M L)
    (hdeep : 6 ≤ (sectorOf A hN pair).val) :
    2 * (L + 1) < 3 * canonicalResidualComponentCount A pair.1.1 pair.1.2 L ∧
      canonicalCorrectedDefectCount A pair.1.1 pair.1.2 L ≤ 2 := by
  unfold sectorOf at hdeep
  split_ifs at hdeep <;> simp_all [moderateCore, HasAtLeastThreeCorrectedDefects] <;> omega

/-- Additive form relating the actual rank, slack and residual dimension in late sectors. -/
theorem slack_add_rank_add_tau_of_sector_at_least_five
    {N M A L : ℕ} (hN : 2 ≤ N) (pair : SeparatedBoundedRatioPair N M L)
    (hlate : 4 ≤ (sectorOf A hN pair).val) :
    boundedTerminalSlack A pair + boundedCanonicalSmallRowRank A pair + pairTau A hN pair =
      L + 1 + canonicalCorrectedDefectCount A pair.1.1 pair.1.2 L := by
  have hslack := slack_add_componentCount (A := A) hN pair
  have hrank := residualTau_add_rank_eq_corrected_add_components hN pair
    (nonaligned_of_sector_at_least_five hN pair hlate)
  omega

end
end PaperC.V282.ResidualSectorPartition
