import PaperC.Combinatorics.SectionElevenPartition
import PaperC.Combinatorics.CanonicalTerminalPopulation

set_option maxHeartbeats 1800000

/-!
# The canonical seven-sector partition

This file closes the remaining parameter in `SectionElevenPartition` by
using the explicit integer-budget population `terminalPairsAtBudget`.
Consequently all six tests of Lemma 11.1 are concrete functions of
`N`, `A`, `L`, `smallRowRank`, and `rankBudget`.

The terminal population already includes membership in `deepCorePairs`,
vanishing systematic exponent, at most two corrected defects, and the
integer rank budget.  The ordered classifier nevertheless applies its
alignment test first.  Therefore its seventh sector is exactly the
nonaligned part of `terminalPairsAtBudget`; candidates caught by the earlier
alignment test remain, correctly, in sector four.

For nonaligned pairs the systematic exponent is automatically zero.  The
last two characterizations below therefore reduce sectors six and seven to
the strict complement and satisfaction, respectively, of the integer budget
inside the deep, nonaligned, at-most-two-defect population.
-/

namespace PaperC
namespace CanonicalSectionElevenPartition

open Affine.CanonicalRationalCode
open CanonicalTerminalPopulation
open ResidualMasses
open SectionElevenPartition
open SectionSevenPartition
open ShallowCorePairs
open SmallHeightLargeProductPairs

noncomputable section

/-! ## Fully instantiated tests and populations -/

/-- Lemma 11.1 tests with literal membership in the terminal population. -/
noncomputable def canonicalSectionElevenTests
    (N A L : ℕ) (hN : 2 ≤ N)
    (smallRowRank : SeparatedDyadicPair N L → ℕ)
    (rankBudget : ℕ) :
    OrderedSectorTests (SeparatedDyadicPair N L) :=
  sectionElevenTests A hN fun pair ↦
    pair ∈
      terminalPairsAtBudget
        N A L hN smallRowRank rankBudget

/-- The fully concrete sector selected for one separated pair. -/
noncomputable def canonicalSectionElevenSectorOf
    {N L : ℕ} (A : ℕ) (hN : 2 ≤ N)
    (smallRowRank : SeparatedDyadicPair N L → ℕ)
    (rankBudget : ℕ)
    (pair : SeparatedDyadicPair N L) :
    ResidualSector :=
  sectorOf
    (canonicalSectionElevenTests
      N A L hN smallRowRank rankBudget)
    pair

/-- The finite population selected by one of the seven concrete sectors. -/
noncomputable def canonicalSectionElevenSectorPairs
    (N A L : ℕ) (hN : 2 ≤ N)
    (smallRowRank : SeparatedDyadicPair N L → ℕ)
    (rankBudget : ℕ)
    (sector : ResidualSector) :
    Finset (SeparatedDyadicPair N L) :=
  sectorPopulation
    (canonicalSectionElevenTests
      N A L hN smallRowRank rankBudget)
    sector

@[simp]
theorem mem_canonicalSectionElevenSectorPairs
    {N A L : ℕ} {hN : 2 ≤ N}
    {smallRowRank : SeparatedDyadicPair N L → ℕ}
    {rankBudget : ℕ}
    {sector : ResidualSector}
    {pair : SeparatedDyadicPair N L} :
    pair ∈
        canonicalSectionElevenSectorPairs
          N A L hN smallRowRank rankBudget sector ↔
      canonicalSectionElevenSectorOf
          A hN smallRowRank rankBudget pair =
        sector := by
  exact mem_sectorPopulation

/-! ## Exact partition theorem -/

/-- Distinct canonical Section 11 populations are disjoint. -/
theorem canonicalSectionElevenSectorPairs_disjoint
    {N A L : ℕ} (hN : 2 ≤ N)
    (smallRowRank : SeparatedDyadicPair N L → ℕ)
    (rankBudget : ℕ)
    {s t : ResidualSector} (hst : s ≠ t) :
    Disjoint
      (canonicalSectionElevenSectorPairs
        N A L hN smallRowRank rankBudget s)
      (canonicalSectionElevenSectorPairs
        N A L hN smallRowRank rankBudget t) :=
  sectorPopulations_disjoint
    (canonicalSectionElevenTests
      N A L hN smallRowRank rankBudget)
    hst

/-- The seven concrete populations cover every separated dyadic pair. -/
theorem canonical_lemma_eleven_one_populations_cover
    {N A L : ℕ} (hN : 2 ≤ N)
    (smallRowRank : SeparatedDyadicPair N L → ℕ)
    (rankBudget : ℕ) :
    ((((((canonicalSectionElevenSectorPairs
                N A L hN smallRowRank rankBudget
                .smallPrimeProduct ∪
              canonicalSectionElevenSectorPairs
                N A L hN smallRowRank rankBudget
                .smallCanonicalHeight) ∪
            canonicalSectionElevenSectorPairs
              N A L hN smallRowRank rankBudget
              .shallowCore) ∪
          canonicalSectionElevenSectorPairs
            N A L hN smallRowRank rankBudget
            .alignedDeepCore) ∪
        canonicalSectionElevenSectorPairs
          N A L hN smallRowRank rankBudget
          .manyDefects) ∪
      canonicalSectionElevenSectorPairs
        N A L hN smallRowRank rankBudget
        .nonterminal) ∪
      canonicalSectionElevenSectorPairs
        N A L hN smallRowRank rankBudget
        .terminal) =
      Finset.univ :=
  seven_sector_populations_cover
    (canonicalSectionElevenTests
      N A L hN smallRowRank rankBudget)

/-- Every separated pair lies in a unique concrete Section 11 sector. -/
theorem canonical_lemma_eleven_one_existsUnique_sector
    {N A L : ℕ} (hN : 2 ≤ N)
    (smallRowRank : SeparatedDyadicPair N L → ℕ)
    (rankBudget : ℕ)
    (pair : SeparatedDyadicPair N L) :
    ∃! sector : ResidualSector,
      pair ∈
        canonicalSectionElevenSectorPairs
          N A L hN smallRowRank rankBudget sector :=
  existsUnique_sector
    (canonicalSectionElevenTests
      N A L hN smallRowRank rankBudget)
    pair

/--
The last four concrete sectors refine exactly the deep-core population.
-/
theorem canonical_lateSectors_eq_deepCorePairs
    {N A L : ℕ} (hN : 2 ≤ N)
    (smallRowRank : SeparatedDyadicPair N L → ℕ)
    (rankBudget : ℕ) :
    (((canonicalSectionElevenSectorPairs
              N A L hN smallRowRank rankBudget
              .alignedDeepCore ∪
            canonicalSectionElevenSectorPairs
              N A L hN smallRowRank rankBudget
              .manyDefects) ∪
          canonicalSectionElevenSectorPairs
            N A L hN smallRowRank rankBudget
            .nonterminal) ∪
        canonicalSectionElevenSectorPairs
          N A L hN smallRowRank rankBudget
          .terminal) =
      deepCorePairs N A L hN := by
  simpa [canonicalSectionElevenSectorPairs,
    canonicalSectionElevenTests, sectionElevenSectorPairs] using
    (sectionEleven_lateSectors_eq_deepCorePairs
      (N := N) (A := A) (L := L) hN
      (fun pair ↦
        pair ∈ terminalPairsAtBudget
          N A L hN smallRowRank rankBudget))

/-! ## The two terminal branches -/

/-- Sector six with the literal terminal-population test exposed. -/
@[simp]
theorem canonicalSectionElevenSectorOf_eq_six_iff
    {N A L : ℕ} {hN : 2 ≤ N}
    {smallRowRank : SeparatedDyadicPair N L → ℕ}
    {rankBudget : ℕ}
    {pair : SeparatedDyadicPair N L} :
    canonicalSectionElevenSectorOf
        A hN smallRowRank rankBudget pair =
        .nonterminal ↔
      HasLargeCanonicalPrimeProduct A hN pair ∧
        ¬HasSmallCanonicalHeight
          A L pair.1.1 pair.1.2 ∧
        ¬HasCoreDensityAtMostThreeSixteenths
          A L pair.1.1 pair.1.2 ∧
        IsCanonicallyNonaligned
          A L pair.1.1 pair.1.2 ∧
        HasAtMostTwoCorrectedDefects
          A L pair.1.1 pair.1.2 ∧
        pair ∉
          terminalPairsAtBudget
            N A L hN smallRowRank rankBudget := by
  simpa [canonicalSectionElevenSectorOf,
    canonicalSectionElevenTests,
    sectionElevenSectorOf] using
    (sectionElevenSectorOf_eq_six_iff
      (N := N) (A := A) (L := L)
      (hN := hN)
      (isTerminal := fun p ↦
        p ∈ terminalPairsAtBudget
          N A L hN smallRowRank rankBudget)
      (pair := pair))

/-- Sector seven with literal terminal-population membership exposed. -/
@[simp]
theorem canonicalSectionElevenSectorOf_eq_seven_iff
    {N A L : ℕ} {hN : 2 ≤ N}
    {smallRowRank : SeparatedDyadicPair N L → ℕ}
    {rankBudget : ℕ}
    {pair : SeparatedDyadicPair N L} :
    canonicalSectionElevenSectorOf
        A hN smallRowRank rankBudget pair =
        .terminal ↔
      HasLargeCanonicalPrimeProduct A hN pair ∧
        ¬HasSmallCanonicalHeight
          A L pair.1.1 pair.1.2 ∧
        ¬HasCoreDensityAtMostThreeSixteenths
          A L pair.1.1 pair.1.2 ∧
        IsCanonicallyNonaligned
          A L pair.1.1 pair.1.2 ∧
        HasAtMostTwoCorrectedDefects
          A L pair.1.1 pair.1.2 ∧
        pair ∈
          terminalPairsAtBudget
            N A L hN smallRowRank rankBudget := by
  simpa [canonicalSectionElevenSectorOf,
    canonicalSectionElevenTests,
    sectionElevenSectorOf] using
    (sectionElevenSectorOf_eq_seven_iff
      (N := N) (A := A) (L := L)
      (hN := hN)
      (isTerminal := fun p ↦
        p ∈ terminalPairsAtBudget
          N A L hN smallRowRank rankBudget)
      (pair := pair))

/-- No selected canonical channel forces the systematic exponent to vanish. -/
theorem pairSigma_eq_zero_of_isCanonicallyNonaligned
    {N A L : ℕ} {pair : SeparatedDyadicPair N L}
    (hnonaligned :
      IsCanonicallyNonaligned
        A L pair.1.1 pair.1.2) :
    pairSigma A pair = 0 := by
  unfold IsCanonicallyNonaligned at hnonaligned
  simp [pairSigma, RationalMassFinite.canonicalPairSigma,
    canonicalMultiplicity, hnonaligned]

/--
The first three negative tests are exactly membership in the deep core.
-/
theorem mem_deepCorePairs_iff_sectionEleven_prefix
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L} :
    pair ∈ deepCorePairs N A L hN ↔
      HasLargeCanonicalPrimeProduct A hN pair ∧
        ¬HasSmallCanonicalHeight
          A L pair.1.1 pair.1.2 ∧
        ¬HasCoreDensityAtMostThreeSixteenths
          A L pair.1.1 pair.1.2 := by
  rw [mem_deepCorePairs]
  constructor
  · rintro ⟨hlarge, hheight, hdepth⟩
    refine ⟨?_, hheight, ?_⟩
    · simpa [HasLargeCanonicalPrimeProduct] using hlarge
    · unfold HasCoreDensityAtMostThreeSixteenths
      omega
  · rintro ⟨hlarge, hheight, hdensity⟩
    refine ⟨?_, hheight, ?_⟩
    · simpa [HasLargeCanonicalPrimeProduct] using hlarge
    · unfold HasCoreDensityAtMostThreeSixteenths at hdensity
      omega

/--
After the previous five tests fail, sector seven is exactly the explicit
terminal population.  The only additional filter visible here is
nonalignment, because the ordered classifier sends aligned members to
sector four before reaching its terminal test.
-/
theorem canonicalSectionElevenSectorOf_eq_terminal_iff
    {N A L : ℕ} {hN : 2 ≤ N}
    {smallRowRank : SeparatedDyadicPair N L → ℕ}
    {rankBudget : ℕ}
    {pair : SeparatedDyadicPair N L} :
    canonicalSectionElevenSectorOf
        A hN smallRowRank rankBudget pair =
        .terminal ↔
      pair ∈
          terminalPairsAtBudget
            N A L hN smallRowRank rankBudget ∧
        IsCanonicallyNonaligned
          A L pair.1.1 pair.1.2 := by
  constructor
  · intro hsector
    have h :
        HasLargeCanonicalPrimeProduct A hN pair ∧
          ¬HasSmallCanonicalHeight
            A L pair.1.1 pair.1.2 ∧
          ¬HasCoreDensityAtMostThreeSixteenths
            A L pair.1.1 pair.1.2 ∧
          IsCanonicallyNonaligned
            A L pair.1.1 pair.1.2 ∧
          HasAtMostTwoCorrectedDefects
            A L pair.1.1 pair.1.2 ∧
          pair ∈
            terminalPairsAtBudget
              N A L hN smallRowRank rankBudget :=
      canonicalSectionElevenSectorOf_eq_seven_iff.mp
        hsector
    exact ⟨h.2.2.2.2.2, h.2.2.2.1⟩
  · rintro ⟨hterminal, hnonaligned⟩
    have ht :=
      mem_terminalPairsAtBudget.mp hterminal
    have hprefix :=
      mem_deepCorePairs_iff_sectionEleven_prefix.mp
        ht.1
    exact
      canonicalSectionElevenSectorOf_eq_seven_iff.mpr
        ⟨hprefix.1, hprefix.2.1, hprefix.2.2,
          hnonaligned, ht.2.2.1, hterminal⟩

/--
Concrete sector seven: a deep, nonaligned pair with at most two corrected
defects is terminal exactly when it satisfies the integer rank budget.
-/
theorem canonicalSectionElevenSectorOf_eq_terminal_budget_iff
    {N A L : ℕ} {hN : 2 ≤ N}
    {smallRowRank : SeparatedDyadicPair N L → ℕ}
    {rankBudget : ℕ}
    {pair : SeparatedDyadicPair N L} :
    canonicalSectionElevenSectorOf
        A hN smallRowRank rankBudget pair =
        .terminal ↔
      pair ∈ deepCorePairs N A L hN ∧
        IsCanonicallyNonaligned
          A L pair.1.1 pair.1.2 ∧
        HasAtMostTwoCorrectedDefects
          A L pair.1.1 pair.1.2 ∧
        terminalSlack A pair + smallRowRank pair ≤
          rankBudget := by
  rw [canonicalSectionElevenSectorOf_eq_terminal_iff]
  constructor
  · rintro ⟨hterminal, hnonaligned⟩
    have ht := mem_terminalPairsAtBudget.mp hterminal
    exact ⟨ht.1, hnonaligned, ht.2.2.1, ht.2.2.2⟩
  · rintro ⟨hdeep, hnonaligned, hfew, hbudget⟩
    refine ⟨?_, hnonaligned⟩
    exact mem_terminalPairsAtBudget.mpr
      ⟨hdeep,
        pairSigma_eq_zero_of_isCanonicallyNonaligned
          hnonaligned,
        hfew, hbudget⟩

/--
Concrete sector six is the strict budget complement of sector seven after
the previous four structural tests have failed.
-/
theorem canonicalSectionElevenSectorOf_eq_nonterminal_budget_iff
    {N A L : ℕ} {hN : 2 ≤ N}
    {smallRowRank : SeparatedDyadicPair N L → ℕ}
    {rankBudget : ℕ}
    {pair : SeparatedDyadicPair N L} :
    canonicalSectionElevenSectorOf
        A hN smallRowRank rankBudget pair =
        .nonterminal ↔
      pair ∈ deepCorePairs N A L hN ∧
        IsCanonicallyNonaligned
          A L pair.1.1 pair.1.2 ∧
        HasAtMostTwoCorrectedDefects
          A L pair.1.1 pair.1.2 ∧
        rankBudget <
          terminalSlack A pair + smallRowRank pair := by
  constructor
  · intro hsector
    have h :
        HasLargeCanonicalPrimeProduct A hN pair ∧
          ¬HasSmallCanonicalHeight
            A L pair.1.1 pair.1.2 ∧
          ¬HasCoreDensityAtMostThreeSixteenths
            A L pair.1.1 pair.1.2 ∧
          IsCanonicallyNonaligned
            A L pair.1.1 pair.1.2 ∧
          HasAtMostTwoCorrectedDefects
            A L pair.1.1 pair.1.2 ∧
          pair ∉
            terminalPairsAtBudget
              N A L hN smallRowRank rankBudget :=
      canonicalSectionElevenSectorOf_eq_six_iff.mp
        hsector
    have hdeep :=
      mem_deepCorePairs_iff_sectionEleven_prefix.mpr
        ⟨h.1, h.2.1, h.2.2.1⟩
    refine ⟨hdeep, h.2.2.2.1, h.2.2.2.2.1, ?_⟩
    by_contra hnot
    have hbudget :
        terminalSlack A pair + smallRowRank pair ≤
          rankBudget := by omega
    have hterminal :
        pair ∈ terminalPairsAtBudget
          N A L hN smallRowRank rankBudget :=
      mem_terminalPairsAtBudget.mpr
        ⟨hdeep,
          pairSigma_eq_zero_of_isCanonicallyNonaligned
            h.2.2.2.1,
          h.2.2.2.2.1, hbudget⟩
    exact h.2.2.2.2.2 hterminal
  · rintro ⟨hdeep, hnonaligned, hfew, hbudget⟩
    have hprefix :=
      mem_deepCorePairs_iff_sectionEleven_prefix.mp
        hdeep
    apply canonicalSectionElevenSectorOf_eq_six_iff.mpr
    refine ⟨hprefix.1, hprefix.2.1, hprefix.2.2,
      hnonaligned, hfew, ?_⟩
    intro hterminal
    have ht := mem_terminalPairsAtBudget.mp hterminal
    omega

/-- The nonaligned part of the integer-budget terminal population. -/
noncomputable def nonalignedTerminalPairsAtBudget
    (N A L : ℕ) (hN : 2 ≤ N)
    (smallRowRank : SeparatedDyadicPair N L → ℕ)
    (rankBudget : ℕ) :
    Finset (SeparatedDyadicPair N L) := by
  classical
  exact
    (terminalPairsAtBudget
      N A L hN smallRowRank rankBudget).filter
      fun pair ↦
        IsCanonicallyNonaligned
          A L pair.1.1 pair.1.2

@[simp]
theorem mem_nonalignedTerminalPairsAtBudget
    {N A L : ℕ} {hN : 2 ≤ N}
    {smallRowRank : SeparatedDyadicPair N L → ℕ}
    {rankBudget : ℕ}
    {pair : SeparatedDyadicPair N L} :
    pair ∈
        nonalignedTerminalPairsAtBudget
          N A L hN smallRowRank rankBudget ↔
      pair ∈ terminalPairsAtBudget
          N A L hN smallRowRank rankBudget ∧
        IsCanonicallyNonaligned
          A L pair.1.1 pair.1.2 := by
  classical
  simp [nonalignedTerminalPairsAtBudget]

/--
The seventh finite sector is the nonaligned filter of the canonical terminal
population.
-/
theorem canonicalSectionElevenSectorPairs_terminal_eq_filter
    {N A L : ℕ} (hN : 2 ≤ N)
    (smallRowRank : SeparatedDyadicPair N L → ℕ)
    (rankBudget : ℕ) :
    canonicalSectionElevenSectorPairs
        N A L hN smallRowRank rankBudget
        .terminal =
      nonalignedTerminalPairsAtBudget
        N A L hN smallRowRank rankBudget := by
  classical
  ext pair
  rw [mem_canonicalSectionElevenSectorPairs]
  rw [canonicalSectionElevenSectorOf_eq_terminal_iff]
  rw [mem_nonalignedTerminalPairsAtBudget]

end

end CanonicalSectionElevenPartition
end PaperC
