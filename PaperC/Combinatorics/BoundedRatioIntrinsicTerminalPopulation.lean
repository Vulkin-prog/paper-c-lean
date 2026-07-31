import PaperC.Combinatorics.BoundedRatioCanonicalTerminalPopulation

set_option maxHeartbeats 1800000

/-!
# Finite bookkeeping for the intrinsic bounded-ratio terminal population

`BoundedRatioCanonicalTerminalPopulation` defines both the manuscript
rank presentation of `T_K` and the equivalent intrinsic presentation

`B + D# ≤ τ + floor(K sqrt(B) / log(B))`.

The latter is the preferred classifier for the public bounded-ratio theorem:
its nonterminal complement yields the rank saving without assuming the
unformalized arithmetic-kernel equivalence.  This file supplies the symmetric
finite mass and fibre API for its terminal side.
-/

namespace PaperC
namespace BoundedRatioIntrinsicTerminalPopulation

open scoped BigOperators
open BoundedRatioCanonicalTerminalPopulation
open PropositionSixteenOne
open ResidualComponentCounts

noncomputable section

/-- Residual mass of the intrinsic bounded-ratio `T_K`. -/
noncomputable def boundedIntrinsicTerminalResidualMass
    (N M A L : ℕ) (hN : 2 ≤ N) (K : ℝ) : ℕ :=
  ∑ pair ∈ boundedIntrinsicTerminalPairs N M A L hN K,
    residualWeight A hN pair

/-- First starts represented in the intrinsic terminal population. -/
noncomputable def boundedIntrinsicTerminalFirstStarts
    (N M A L : ℕ) (hN : 2 ≤ N) (K : ℝ) :
    Finset ℕ :=
  (boundedIntrinsicTerminalPairs N M A L hN K).image
    (fun pair => pair.1.1)

/-- Every intrinsic terminal pair satisfies `τ≤B+2`. -/
theorem pairTau_le_runLength_add_two_of_mem_intrinsicTerminal
    {N M A L : ℕ} {hN : 2 ≤ N} {K : ℝ}
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈ boundedIntrinsicTerminalPairs N M A L hN K) :
    pairTau A hN pair ≤ L + 1 + 2 := by
  have hdata := mem_boundedIntrinsicTerminalPairs.mp hpair
  have htau :=
    pairTau_le_corrected_add_components
      (A := A) hN pair
  have hc :=
    canonicalResidualComponentCount_le_runLength
      (A := A) hN pair
  unfold boundedTerminalCoreConditions at hdata
  have hD :
      canonicalCorrectedDefectCount
          A pair.1.1 pair.1.2 L ≤ 2 :=
    hdata.1.2.2.2.2
  omega

/-- Nonalignment makes the intrinsic terminal weight exactly `2^τ-1`. -/
theorem residualWeight_eq_two_pow_sub_one_of_mem_intrinsicTerminal
    {N M A L : ℕ} {hN : 2 ≤ N} {K : ℝ}
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈ boundedIntrinsicTerminalPairs N M A L hN K) :
    residualWeight A hN pair =
      2 ^ pairTau A hN pair - 1 := by
  have hdata := mem_boundedIntrinsicTerminalPairs.mp hpair
  unfold boundedTerminalCoreConditions at hdata
  have hsigma :=
    pairSigma_eq_zero_of_isCanonicallyNonaligned
      hdata.1.2.2.2.1
  simp [residualWeight, hsigma]

/-- Terminal mass is bounded by cardinality times `4*2^B`. -/
theorem boundedIntrinsicTerminalResidualMass_le_card_mul_weight
    {N M A L : ℕ} (hN : 2 ≤ N) (K : ℝ) :
    boundedIntrinsicTerminalResidualMass N M A L hN K ≤
      (boundedIntrinsicTerminalPairs N M A L hN K).card *
        (4 * 2 ^ (L + 1)) := by
  unfold boundedIntrinsicTerminalResidualMass
  apply Finset.sum_le_card_nsmul
  intro pair hpair
  rw [residualWeight_eq_two_pow_sub_one_of_mem_intrinsicTerminal
    hpair]
  exact
    TerminalClosureCounting.two_pow_sub_one_le_four_mul_two_pow
      (pairTau_le_runLength_add_two_of_mem_intrinsicTerminal hpair)

/-- Exact disintegration of intrinsic `T_K` over its first coordinate. -/
theorem card_boundedIntrinsicTerminalPairs_eq_sum_partnerFibers
    {N M A L : ℕ} (hN : 2 ≤ N) (K : ℝ) :
    (boundedIntrinsicTerminalPairs N M A L hN K).card =
      ∑ x ∈ boundedIntrinsicTerminalFirstStarts N M A L hN K,
        ((boundedIntrinsicTerminalPairs N M A L hN K).filter
          fun pair => pair.1.1 = x).card := by
  let population :=
    boundedIntrinsicTerminalPairs N M A L hN K
  let first : SeparatedBoundedRatioPair N M L → ℕ :=
    fun pair => pair.1.1
  have hcard :=
    Finset.card_eq_sum_card_image first population
  simpa [population, first,
    boundedIntrinsicTerminalFirstStarts] using hcard

/-- A uniform partner bound controls the intrinsic terminal population. -/
theorem card_boundedIntrinsicTerminalPairs_le_firstStarts_mul
    {N M A L : ℕ} (hN : 2 ≤ N) (K : ℝ) (Q : ℕ)
    (hpartners :
      ∀ x ∈ boundedIntrinsicTerminalFirstStarts N M A L hN K,
        ((boundedIntrinsicTerminalPairs N M A L hN K).filter
          fun pair => pair.1.1 = x).card ≤ Q) :
    (boundedIntrinsicTerminalPairs N M A L hN K).card ≤
      (boundedIntrinsicTerminalFirstStarts N M A L hN K).card * Q := by
  rw [card_boundedIntrinsicTerminalPairs_eq_sum_partnerFibers hN K]
  calc
    (∑ x ∈ boundedIntrinsicTerminalFirstStarts N M A L hN K,
      ((boundedIntrinsicTerminalPairs N M A L hN K).filter
        fun pair => pair.1.1 = x).card) ≤
        ∑ _x ∈ boundedIntrinsicTerminalFirstStarts
          N M A L hN K, Q :=
      Finset.sum_le_sum hpartners
    _ =
        (boundedIntrinsicTerminalFirstStarts
          N M A L hN K).card * Q := by
      simp

/-- Separate first-start and partner bounds imply a product bound. -/
theorem card_boundedIntrinsicTerminalPairs_le
    {N M A L : ℕ} (hN : 2 ≤ N) (K : ℝ)
    (firstBound partnerBound : ℕ)
    (hfirst :
      (boundedIntrinsicTerminalFirstStarts
          N M A L hN K).card ≤ firstBound)
    (hpartners :
      ∀ x ∈ boundedIntrinsicTerminalFirstStarts N M A L hN K,
        ((boundedIntrinsicTerminalPairs N M A L hN K).filter
          fun pair => pair.1.1 = x).card ≤ partnerBound) :
    (boundedIntrinsicTerminalPairs N M A L hN K).card ≤
      firstBound * partnerBound := by
  exact
    (card_boundedIntrinsicTerminalPairs_le_firstStarts_mul
      hN K partnerBound hpartners).trans
      (Nat.mul_le_mul_right partnerBound hfirst)

/-- The intrinsic terminal mass is exactly the public seventh-sector mass. -/
theorem boundedIntrinsicTerminalResidualMass_eq_sectorResidualMassNat
    {N M A L : ℕ} (hN : 2 ≤ N) (K : ℝ) :
    boundedIntrinsicTerminalResidualMass N M A L hN K =
      sectorResidualMassNat
        (M := M) (L := L) A hN
        (boundedIntrinsicTerminalPredicate A K) .terminal := by
  unfold boundedIntrinsicTerminalResidualMass sectorResidualMassNat
  rw [boundedRatioSectorPairs_terminal_eq_intrinsicTerminalPairs]

end

end BoundedRatioIntrinsicTerminalPopulation
end PaperC
