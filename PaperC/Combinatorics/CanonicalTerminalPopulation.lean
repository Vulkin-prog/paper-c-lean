import PaperC.Combinatorics.SectionSevenPartition
import PaperC.Combinatorics.LargePrimeGraphResolution
import PaperC.Combinatorics.SmallComponentExtraction
import PaperC.Combinatorics.TerminalComponentCount
import PaperC.Combinatorics.TerminalClosureCounting
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option maxHeartbeats 1200000

/-!
# The canonical terminal population

This file connects the abstract finite statements proved for Proposition 9.11
and Theorem 10.1 to the canonical residual components of a separated dyadic
pair.

For a pair with residual-component count `c#`, put

`s = (L + 1) - c#`.

The canonical vertex budget proves `c# ≤ L + 1`.  Since every canonical
residual component is nontrivial and the component supports are disjoint,
`TerminalComponentCount` then gives the manuscript's concrete conclusion:
at least `(L + 1) - 3s` residual components have support of cardinality two.

We also define an integer-budget interface for the terminal population.  The
real expression `K * sqrt B / log B` is deliberately represented by an
explicit natural-number parameter `rankBudget`, and the value of `k̃` by a
supplied function.  Choosing that function from the canonical small-row
matrix and estimating the integer threshold remain separate steps.  On this
finite proxy Lean proves `τ ≤ (L + 1) + 2` and the exact weighted bound used
in Step 4 of Theorem 10.1.
-/

namespace PaperC
namespace CanonicalTerminalPopulation

open CanonicalResidualComponents
open LargePrimeGraph
open LargePrimeGraphResolution
open LargePrimeOccurrences
open PinnedGraphResolution
open ResidualComponentCounts
open ResidualMasses
open SectionSevenPartition
open SmallComponentExtraction
open TerminalClosureCounting
open TerminalComponentCount

noncomputable section

noncomputable local instance instDecidableLargePrimeAdj
    (x y L : ℕ) :
    DecidableRel (largePrimeGraph x y L).Adj :=
  Classical.decRel _

/-! ## Canonical two-vertex residual components -/

/-- Canonical residual components whose support has exactly two vertices. -/
noncomputable def canonicalPairComponents
    {N L : ℕ} (A : ℕ) (pair : SeparatedDyadicPair N L) :
    Finset
      (largePrimeGraph pair.1.1 pair.1.2 L).ConnectedComponent :=
  pairComponents
    (canonicalResidualComponents A pair.1.1 pair.1.2 L)
    (fun C ↦ Fintype.card C.supp)

/-- Canonical residual components whose support has at least three vertices. -/
noncomputable def canonicalLargeComponents
    {N L : ℕ} (A : ℕ) (pair : SeparatedDyadicPair N L) :
    Finset
      (largePrimeGraph pair.1.1 pair.1.2 L).ConnectedComponent :=
  largeComponents
    (canonicalResidualComponents A pair.1.1 pair.1.2 L)
    (fun C ↦ Fintype.card C.supp)

/-- The manuscript's terminal slack `s = B - c#`, with `B = L + 1`. -/
noncomputable def terminalSlack
    {N L : ℕ} (A : ℕ) (pair : SeparatedDyadicPair N L) : ℕ :=
  L + 1 -
    canonicalResidualComponentCount
      A pair.1.1 pair.1.2 L

/-- The canonical residual-component count never exceeds `B = L+1`. -/
theorem canonicalResidualComponentCount_le_runLength
    {N A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedDyadicPair N L) :
    canonicalResidualComponentCount
        A pair.1.1 pair.1.2 L ≤
      L + 1 := by
  have hxy := pair_coordinates_two_le hN pair
  have hbudget :=
    canonicalCorrected_add_twice_residual_le
      A pair.1.1 pair.1.2 L
      (by omega) (by omega)
  omega

/--
The canonical residual family has cardinality
`B - terminalSlack = c#`.
-/
theorem card_canonicalResidualComponents_eq_runLength_sub_slack
    {N A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedDyadicPair N L) :
    (canonicalResidualComponents
        A pair.1.1 pair.1.2 L).card =
      L + 1 - terminalSlack A pair := by
  have hxy := pair_coordinates_two_le hN pair
  rw [card_canonicalResidualComponents hxy.1 hxy.2]
  unfold terminalSlack
  have hle :=
    canonicalResidualComponentCount_le_runLength
      (A := A) hN pair
  omega

/--
Concrete Proposition 9.11 component count for the canonical residual family.

The first conclusion bounds components of size at least three by `2s`; the
second gives at least `B-3s` components of size exactly two.
-/
theorem canonical_terminal_component_count
    {N A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedDyadicPair N L) :
    (canonicalLargeComponents A pair).card ≤
        2 * terminalSlack A pair ∧
      L + 1 - 3 * terminalSlack A pair ≤
        (canonicalPairComponents A pair).card := by
  classical
  let family :=
    canonicalResidualComponents
      A pair.1.1 pair.1.2 L
  let size :
      (largePrimeGraph pair.1.1 pair.1.2 L).ConnectedComponent →
        ℕ :=
    fun C ↦ Fintype.card C.supp
  have hxy := pair_coordinates_two_le hN pair
  have hcard :
      family.card =
        L + 1 - terminalSlack A pair := by
    exact
      card_canonicalResidualComponents_eq_runLength_sub_slack
        (A := A) hN pair
  have hsize :
      ∀ C ∈ family, 2 ≤ size C := by
    intro C hC
    exact
      (isNontrivialUnpinnedComponent_of_mem_canonicalResidualComponents
        (show
          C ∈ canonicalResidualComponents
            A pair.1.1 pair.1.2 L
          from hC)).2
  have hmass :
      (∑ C ∈ family, size C) ≤ 2 * (L + 1) := by
    calc
      (∑ C ∈ family, size C) ≤
          Fintype.card (Occurrence L) :=
        sum_component_support_sizes_le
          (largePrimeGraph pair.1.1 pair.1.2 L)
          family
      _ = 2 * (L + 1) := card_occurrence L
  have hcount :=
    terminal_component_count_of_card_eq_sub
      (B := L + 1)
      (s := terminalSlack A pair)
      (components := family)
      (size := size)
      (Nat.sub_le (L + 1)
        (canonicalResidualComponentCount
          A pair.1.1 pair.1.2 L))
      hcard hsize hmass
  simpa [canonicalLargeComponents, canonicalPairComponents,
    family, size] using hcount

/-! ## Integer-budget interface for the terminal population -/

/--
An integer-budget proxy for the terminal set `T_K`.

The parameter `smallRowRank` supplies the manuscript's small-row rank `k̃`;
`rankBudget` supplies a chosen integer upper bound for
`K * sqrt B / log B`.  Neither connection is hidden in the definition.
-/
noncomputable def terminalPairsAtBudget
    (N A L : ℕ) (hN : 2 ≤ N)
    (smallRowRank : SeparatedDyadicPair N L → ℕ)
    (rankBudget : ℕ) :
    Finset (SeparatedDyadicPair N L) :=
  (deepCorePairs N A L hN).filter fun pair ↦
    pairSigma A pair = 0 ∧
      canonicalCorrectedDefectCount
          A pair.1.1 pair.1.2 L ≤ 2 ∧
      terminalSlack A pair + smallRowRank pair ≤ rankBudget

@[simp]
theorem mem_terminalPairsAtBudget
    {N A L : ℕ} {hN : 2 ≤ N}
    {smallRowRank : SeparatedDyadicPair N L → ℕ}
    {rankBudget : ℕ}
    {pair : SeparatedDyadicPair N L} :
    pair ∈ terminalPairsAtBudget
        N A L hN smallRowRank rankBudget ↔
      pair ∈ deepCorePairs N A L hN ∧
        pairSigma A pair = 0 ∧
        canonicalCorrectedDefectCount
            A pair.1.1 pair.1.2 L ≤ 2 ∧
        terminalSlack A pair + smallRowRank pair ≤
          rankBudget := by
  simp [terminalPairsAtBudget, and_assoc]

/-- Every concrete terminal pair satisfies `τ ≤ B+2`. -/
theorem pairTau_le_runLength_add_two
    {N A L : ℕ} {hN : 2 ≤ N}
    {smallRowRank : SeparatedDyadicPair N L → ℕ}
    {rankBudget : ℕ}
    {pair : SeparatedDyadicPair N L}
    (hpair :
      pair ∈ terminalPairsAtBudget
        N A L hN smallRowRank rankBudget) :
    pairTau A hN pair ≤ L + 1 + 2 := by
  have hdata := mem_terminalPairsAtBudget.mp hpair
  have htau :=
    pairTau_le_canonicalCorrected_add_residual
      (A := A) hN pair
  have hc :=
    canonicalResidualComponentCount_le_runLength
      (A := A) hN pair
  omega

/--
On this sigma-zero proxy, the residual weight is literally `2^τ-1`.  No
equivalence between `σ=0` and the manuscript's nonaligned predicate is used.
-/
theorem linearResidualWeight_eq_two_pow_sub_one
    {N A L : ℕ} {hN : 2 ≤ N}
    {smallRowRank : SeparatedDyadicPair N L → ℕ}
    {rankBudget : ℕ}
    {pair : SeparatedDyadicPair N L}
    (hpair :
      pair ∈ terminalPairsAtBudget
        N A L hN smallRowRank rankBudget) :
    linearResidualWeight A hN pair =
      2 ^ pairTau A hN pair - 1 := by
  have hsigma :=
    (mem_terminalPairsAtBudget.mp hpair).2.1
  simp [linearResidualWeight, hsigma]

/-- The finite residual mass of the integer-budget terminal population. -/
noncomputable def terminalResidualMassAtBudget
    (N A L : ℕ) (hN : 2 ≤ N)
    (smallRowRank : SeparatedDyadicPair N L → ℕ)
    (rankBudget : ℕ) : ℕ :=
  ∑ pair ∈
      terminalPairsAtBudget N A L hN smallRowRank rankBudget,
    linearResidualWeight A hN pair

/--
Concrete Step 4 of Theorem 10.1:

`terminal mass ≤ #T * (4 * 2^B)`.
-/
theorem terminalResidualMassAtBudget_le
    {N A L : ℕ} (hN : 2 ≤ N)
    (smallRowRank : SeparatedDyadicPair N L → ℕ)
    (rankBudget : ℕ) :
    terminalResidualMassAtBudget
        N A L hN smallRowRank rankBudget ≤
      (terminalPairsAtBudget
          N A L hN smallRowRank rankBudget).card *
        (4 * 2 ^ (L + 1)) := by
  unfold terminalResidualMassAtBudget
  apply Finset.sum_le_card_nsmul
  intro pair hpair
  rw [linearResidualWeight_eq_two_pow_sub_one hpair]
  exact
    two_pow_sub_one_le_four_mul_two_pow
      (pairTau_le_runLength_add_two hpair)

/-! ## First starts and partner fibres -/

/-- First coordinates occurring in the integer-budget terminal population. -/
noncomputable def terminalFirstStartsAtBudget
    (N A L : ℕ) (hN : 2 ≤ N)
    (smallRowRank : SeparatedDyadicPair N L → ℕ)
    (rankBudget : ℕ) : Finset ℕ :=
  (terminalPairsAtBudget
      N A L hN smallRowRank rankBudget).image
    (fun pair ↦ pair.1.1)

/--
Exact disintegration of the terminal population over its first coordinate.
This is the finite bookkeeping behind Step 3 of Theorem 10.1.
-/
theorem card_terminalPairsAtBudget_eq_sum_partnerFibers
    {N A L : ℕ} (hN : 2 ≤ N)
    (smallRowRank : SeparatedDyadicPair N L → ℕ)
    (rankBudget : ℕ) :
    (terminalPairsAtBudget
        N A L hN smallRowRank rankBudget).card =
      ∑ x ∈ terminalFirstStartsAtBudget
          N A L hN smallRowRank rankBudget,
        ((terminalPairsAtBudget
            N A L hN smallRowRank rankBudget).filter
          fun pair ↦ pair.1.1 = x).card := by
  let population :=
    terminalPairsAtBudget
      N A L hN smallRowRank rankBudget
  let first : SeparatedDyadicPair N L → ℕ :=
    fun pair ↦ pair.1.1
  have hcard :=
    Finset.card_eq_sum_card_image first population
  simpa [population, first,
    terminalFirstStartsAtBudget] using hcard

/--
If every fixed first start has at most `Q` partners, the whole terminal
population has cardinality at most `#firstStarts * Q`.
-/
theorem card_terminalPairsAtBudget_le_firstStarts_mul
    {N A L : ℕ} (hN : 2 ≤ N)
    (smallRowRank : SeparatedDyadicPair N L → ℕ)
    (rankBudget Q : ℕ)
    (hpartners :
      ∀ x ∈ terminalFirstStartsAtBudget
          N A L hN smallRowRank rankBudget,
        ((terminalPairsAtBudget
            N A L hN smallRowRank rankBudget).filter
          fun pair ↦ pair.1.1 = x).card ≤ Q) :
    (terminalPairsAtBudget
        N A L hN smallRowRank rankBudget).card ≤
      (terminalFirstStartsAtBudget
          N A L hN smallRowRank rankBudget).card * Q := by
  rw [card_terminalPairsAtBudget_eq_sum_partnerFibers
    hN smallRowRank rankBudget]
  calc
    (∑ x ∈ terminalFirstStartsAtBudget
        N A L hN smallRowRank rankBudget,
      ((terminalPairsAtBudget
          N A L hN smallRowRank rankBudget).filter
        fun pair ↦ pair.1.1 = x).card) ≤
        ∑ _x ∈ terminalFirstStartsAtBudget
          N A L hN smallRowRank rankBudget, Q :=
      Finset.sum_le_sum hpartners
    _ =
        (terminalFirstStartsAtBudget
          N A L hN smallRowRank rankBudget).card * Q := by
      simp

/-- Step 3 with a separate bound on the number of first starts. -/
theorem card_terminalPairsAtBudget_le
    {N A L : ℕ} (hN : 2 ≤ N)
    (smallRowRank : SeparatedDyadicPair N L → ℕ)
    (rankBudget firstBound partnerBound : ℕ)
    (hfirst :
      (terminalFirstStartsAtBudget
          N A L hN smallRowRank rankBudget).card ≤ firstBound)
    (hpartners :
      ∀ x ∈ terminalFirstStartsAtBudget
          N A L hN smallRowRank rankBudget,
        ((terminalPairsAtBudget
            N A L hN smallRowRank rankBudget).filter
          fun pair ↦ pair.1.1 = x).card ≤ partnerBound) :
    (terminalPairsAtBudget
        N A L hN smallRowRank rankBudget).card ≤
      firstBound * partnerBound := by
  exact
    (card_terminalPairsAtBudget_le_firstStarts_mul
      hN smallRowRank rankBudget partnerBound hpartners).trans
      (Nat.mul_le_mul_right partnerBound hfirst)

end

end CanonicalTerminalPopulation
end PaperC
