import PaperC.Combinatorics.SectionSevenPartition

set_option maxHeartbeats 1800000

/-!
# The seven-sector partition of Section 11

Lemma 11.1 classifies every separated pair by six successive tests:

1. `P# ≤ N`;
2. existence of a canonical channel of height at most `sqrt (log B)`;
3. `c# ≤ 3B/16`;
4. alignment;
5. `D# ≥ 3`;
6. membership in the terminal population `T_K`.

The first five tests already have concrete definitions in the formalization.
The population `T_K` itself has not yet been assembled from Proposition 9.11,
so this file keeps its membership predicate as an explicit parameter.  No
property of that parameter is assumed.

The generic first part below records the order of the tests once and for all.
It proves exact characterizations of all seven branches, exhaustive coverage,
pairwise disjointness, and uniqueness of the selected sector.  The second part
instantiates the first five tests with the canonical objects of Paper C and
therefore leaves only `isTerminal` as a visible formalization obligation.
-/

namespace PaperC
namespace SectionElevenPartition

open Affine.CanonicalRationalCode
open CanonicalResidualComponents
open ResidualComponentCounts
open ResidualMasses
open ShallowCorePairs
open SmallHeightLargeProductPairs

noncomputable section

/-! ## An ordered seven-way classifier -/

/-- The seven residual sectors in the order of Lemma 11.1. -/
inductive ResidualSector
  | smallPrimeProduct
  | smallCanonicalHeight
  | shallowCore
  | alignedDeepCore
  | manyDefects
  | nonterminal
  | terminal
  deriving DecidableEq, Fintype, Repr

/--
The six yes/no tests needed for the seven-sector partition.

The field names describe the positive answer to each test.  Their order is
part of the classifier `sectorOf`; consequently later predicates need not be
made artificially disjoint from earlier ones.
-/
structure OrderedSectorTests (Ω : Type*) where
  smallPrimeProduct : Ω → Prop
  smallCanonicalHeight : Ω → Prop
  shallowCore : Ω → Prop
  aligned : Ω → Prop
  manyDefects : Ω → Prop
  terminal : Ω → Prop

/--
Apply the tests in the manuscript order.  The terminal test is reached only
after all preceding tests have failed.
-/
noncomputable def sectorOf
    {Ω : Type*} (tests : OrderedSectorTests Ω) (z : Ω) :
    ResidualSector := by
  classical
  exact
    if tests.smallPrimeProduct z then
      .smallPrimeProduct
    else if tests.smallCanonicalHeight z then
      .smallCanonicalHeight
    else if tests.shallowCore z then
      .shallowCore
    else if tests.aligned z then
      .alignedDeepCore
    else if tests.manyDefects z then
      .manyDefects
    else if tests.terminal z then
      .terminal
    else
      .nonterminal

@[simp]
theorem sectorOf_eq_smallPrimeProduct_iff
    {Ω : Type*} {tests : OrderedSectorTests Ω} {z : Ω} :
    sectorOf tests z = .smallPrimeProduct ↔
      tests.smallPrimeProduct z := by
  classical
  by_cases h₁ : tests.smallPrimeProduct z <;>
    by_cases h₂ : tests.smallCanonicalHeight z <;>
      by_cases h₃ : tests.shallowCore z <;>
        by_cases h₄ : tests.aligned z <;>
          by_cases h₅ : tests.manyDefects z <;>
            by_cases h₆ : tests.terminal z <;>
              simp [sectorOf, h₁, h₂, h₃, h₄, h₅, h₆]

@[simp]
theorem sectorOf_eq_smallCanonicalHeight_iff
    {Ω : Type*} {tests : OrderedSectorTests Ω} {z : Ω} :
    sectorOf tests z = .smallCanonicalHeight ↔
      ¬tests.smallPrimeProduct z ∧
        tests.smallCanonicalHeight z := by
  classical
  by_cases h₁ : tests.smallPrimeProduct z <;>
    by_cases h₂ : tests.smallCanonicalHeight z <;>
      by_cases h₃ : tests.shallowCore z <;>
        by_cases h₄ : tests.aligned z <;>
          by_cases h₅ : tests.manyDefects z <;>
            by_cases h₆ : tests.terminal z <;>
              simp [sectorOf, h₁, h₂, h₃, h₄, h₅, h₆]

@[simp]
theorem sectorOf_eq_shallowCore_iff
    {Ω : Type*} {tests : OrderedSectorTests Ω} {z : Ω} :
    sectorOf tests z = .shallowCore ↔
      ¬tests.smallPrimeProduct z ∧
        ¬tests.smallCanonicalHeight z ∧
          tests.shallowCore z := by
  classical
  by_cases h₁ : tests.smallPrimeProduct z <;>
    by_cases h₂ : tests.smallCanonicalHeight z <;>
      by_cases h₃ : tests.shallowCore z <;>
        by_cases h₄ : tests.aligned z <;>
          by_cases h₅ : tests.manyDefects z <;>
            by_cases h₆ : tests.terminal z <;>
              simp [sectorOf, h₁, h₂, h₃, h₄, h₅, h₆]

@[simp]
theorem sectorOf_eq_alignedDeepCore_iff
    {Ω : Type*} {tests : OrderedSectorTests Ω} {z : Ω} :
    sectorOf tests z = .alignedDeepCore ↔
      ¬tests.smallPrimeProduct z ∧
        ¬tests.smallCanonicalHeight z ∧
          ¬tests.shallowCore z ∧
            tests.aligned z := by
  classical
  by_cases h₁ : tests.smallPrimeProduct z <;>
    by_cases h₂ : tests.smallCanonicalHeight z <;>
      by_cases h₃ : tests.shallowCore z <;>
        by_cases h₄ : tests.aligned z <;>
          by_cases h₅ : tests.manyDefects z <;>
            by_cases h₆ : tests.terminal z <;>
              simp [sectorOf, h₁, h₂, h₃, h₄, h₅, h₆]

@[simp]
theorem sectorOf_eq_manyDefects_iff
    {Ω : Type*} {tests : OrderedSectorTests Ω} {z : Ω} :
    sectorOf tests z = .manyDefects ↔
      ¬tests.smallPrimeProduct z ∧
        ¬tests.smallCanonicalHeight z ∧
          ¬tests.shallowCore z ∧
            ¬tests.aligned z ∧
              tests.manyDefects z := by
  classical
  by_cases h₁ : tests.smallPrimeProduct z <;>
    by_cases h₂ : tests.smallCanonicalHeight z <;>
      by_cases h₃ : tests.shallowCore z <;>
        by_cases h₄ : tests.aligned z <;>
          by_cases h₅ : tests.manyDefects z <;>
            by_cases h₆ : tests.terminal z <;>
              simp [sectorOf, h₁, h₂, h₃, h₄, h₅, h₆]

@[simp]
theorem sectorOf_eq_nonterminal_iff
    {Ω : Type*} {tests : OrderedSectorTests Ω} {z : Ω} :
    sectorOf tests z = .nonterminal ↔
      ¬tests.smallPrimeProduct z ∧
        ¬tests.smallCanonicalHeight z ∧
          ¬tests.shallowCore z ∧
            ¬tests.aligned z ∧
              ¬tests.manyDefects z ∧
                ¬tests.terminal z := by
  classical
  by_cases h₁ : tests.smallPrimeProduct z <;>
    by_cases h₂ : tests.smallCanonicalHeight z <;>
      by_cases h₃ : tests.shallowCore z <;>
        by_cases h₄ : tests.aligned z <;>
          by_cases h₅ : tests.manyDefects z <;>
            by_cases h₆ : tests.terminal z <;>
              simp [sectorOf, h₁, h₂, h₃, h₄, h₅, h₆]

@[simp]
theorem sectorOf_eq_terminal_iff
    {Ω : Type*} {tests : OrderedSectorTests Ω} {z : Ω} :
    sectorOf tests z = .terminal ↔
      ¬tests.smallPrimeProduct z ∧
        ¬tests.smallCanonicalHeight z ∧
          ¬tests.shallowCore z ∧
            ¬tests.aligned z ∧
              ¬tests.manyDefects z ∧
                tests.terminal z := by
  classical
  by_cases h₁ : tests.smallPrimeProduct z <;>
    by_cases h₂ : tests.smallCanonicalHeight z <;>
      by_cases h₃ : tests.shallowCore z <;>
        by_cases h₄ : tests.aligned z <;>
          by_cases h₅ : tests.manyDefects z <;>
            by_cases h₆ : tests.terminal z <;>
              simp [sectorOf, h₁, h₂, h₃, h₄, h₅, h₆]

/-- The finite population assigned to one sector. -/
noncomputable def sectorPopulation
    {Ω : Type*} [Fintype Ω]
    (tests : OrderedSectorTests Ω) (sector : ResidualSector) :
    Finset Ω := by
  classical
  exact Finset.univ.filter fun z ↦ sectorOf tests z = sector

@[simp]
theorem mem_sectorPopulation
    {Ω : Type*} [Fintype Ω]
    {tests : OrderedSectorTests Ω}
    {sector : ResidualSector} {z : Ω} :
    z ∈ sectorPopulation tests sector ↔
      sectorOf tests z = sector := by
  classical
  simp [sectorPopulation]

/-- Different sectors contain no common object. -/
theorem sectorPopulations_disjoint
    {Ω : Type*} [Fintype Ω]
    (tests : OrderedSectorTests Ω)
    {s t : ResidualSector} (hst : s ≠ t) :
    Disjoint
      (sectorPopulation tests s)
      (sectorPopulation tests t) := by
  classical
  rw [Finset.disjoint_left]
  intro z hzs hzt
  have hs : sectorOf tests z = s :=
    mem_sectorPopulation.mp hzs
  have ht : sectorOf tests z = t :=
    mem_sectorPopulation.mp hzt
  exact hst (hs.symm.trans ht)

/--
The seven populations cover the whole finite ambient type.  The displayed
union follows the exact order of Lemma 11.1.
-/
theorem seven_sector_populations_cover
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (tests : OrderedSectorTests Ω) :
    ((((((sectorPopulation tests .smallPrimeProduct ∪
              sectorPopulation tests .smallCanonicalHeight) ∪
            sectorPopulation tests .shallowCore) ∪
          sectorPopulation tests .alignedDeepCore) ∪
        sectorPopulation tests .manyDefects) ∪
      sectorPopulation tests .nonterminal) ∪
      sectorPopulation tests .terminal) =
        Finset.univ := by
  classical
  ext z
  simp only [Finset.mem_union, mem_sectorPopulation,
    Finset.mem_univ, iff_true]
  cases hsector : sectorOf tests z <;> simp [hsector]

/-- Every object belongs to a unique one of the seven populations. -/
theorem existsUnique_sector
    {Ω : Type*} [Fintype Ω]
    (tests : OrderedSectorTests Ω) (z : Ω) :
    ∃! sector : ResidualSector,
      z ∈ sectorPopulation tests sector := by
  classical
  refine ⟨sectorOf tests z, ?_, ?_⟩
  · exact mem_sectorPopulation.mpr rfl
  · intro sector hsector
    exact (mem_sectorPopulation.mp hsector).symm

/-! ## Concrete tests for separated dyadic pairs -/

/-- Literal first test `P# ≤ N`. -/
def HasSmallCanonicalPrimeProduct
    {N L : ℕ} (A : ℕ) (hN : 2 ≤ N)
    (pair : SeparatedDyadicPair N L) : Prop :=
  CanonicalResidualPrimeProductAtMost
    (A := A) (L := L)
    (show 1 ≤ pair.1.1 by
      exact le_trans (by omega : 1 ≤ 2)
        (pair_coordinates_two_le hN pair).1)
    (show 1 ≤ pair.1.2 by
      exact le_trans (by omega : 1 ≤ 2)
        (pair_coordinates_two_le hN pair).2)
    N

/-- Literal complementary test `N < P#`. -/
def HasLargeCanonicalPrimeProduct
    {N L : ℕ} (A : ℕ) (hN : 2 ≤ N)
    (pair : SeparatedDyadicPair N L) : Prop :=
  CanonicalResidualPrimeProductExceeds
    (A := A) (L := L)
    (show 1 ≤ pair.1.1 by
      exact le_trans (by omega : 1 ≤ 2)
        (pair_coordinates_two_le hN pair).1)
    (show 1 ≤ pair.1.2 by
      exact le_trans (by omega : 1 ≤ 2)
        (pair_coordinates_two_le hN pair).2)
    N

@[simp]
theorem not_smallCanonicalPrimeProduct_iff_large
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L} :
    ¬HasSmallCanonicalPrimeProduct A hN pair ↔
      HasLargeCanonicalPrimeProduct A hN pair := by
  unfold HasSmallCanonicalPrimeProduct
    HasLargeCanonicalPrimeProduct
  rw [canonicalResidualPrimeProductExceeds_iff_not_atMost]

/--
Alignment in the exact sense of Section 5: the finite canonical selector has
found a reduced channel satisfying (5.1).
-/
def IsCanonicallyAligned
    (A L x y : ℕ) : Prop :=
  ∃ c : ReducedCandidate x y (L + 1) ((L + 1) ^ A),
    canonicalReducedCandidate?
        x y (L + 1) ((L + 1) ^ A) = some c

/-- The literal complementary branch: no canonical channel exists. -/
def IsCanonicallyNonaligned
    (A L x y : ℕ) : Prop :=
  canonicalReducedCandidate?
      x y (L + 1) ((L + 1) ^ A) = none

@[simp]
theorem not_isCanonicallyAligned_iff_nonaligned
    {A L x y : ℕ} :
    ¬IsCanonicallyAligned A L x y ↔
      IsCanonicallyNonaligned A L x y := by
  unfold IsCanonicallyAligned IsCanonicallyNonaligned
  generalize hchoice :
    canonicalReducedCandidate?
        x y (L + 1) ((L + 1) ^ A) = choice
  cases choice <;> simp [hchoice]

@[simp]
theorem not_isCanonicallyNonaligned_iff_aligned
    {A L x y : ℕ} :
    ¬IsCanonicallyNonaligned A L x y ↔
      IsCanonicallyAligned A L x y := by
  unfold IsCanonicallyAligned IsCanonicallyNonaligned
  generalize hchoice :
    canonicalReducedCandidate?
        x y (L + 1) ((L + 1) ^ A) = choice
  cases choice <;> simp [hchoice]

/-- The concrete high-defect test `D# ≥ 3`. -/
def HasAtLeastThreeCorrectedDefects
    (A L x y : ℕ) : Prop :=
  3 ≤ canonicalCorrectedDefectCount A x y L

/-- Its exact natural-number complement `D# ≤ 2`. -/
def HasAtMostTwoCorrectedDefects
    (A L x y : ℕ) : Prop :=
  canonicalCorrectedDefectCount A x y L ≤ 2

@[simp]
theorem not_atLeastThreeCorrectedDefects_iff_atMostTwo
    {A L x y : ℕ} :
    ¬HasAtLeastThreeCorrectedDefects A L x y ↔
      HasAtMostTwoCorrectedDefects A L x y := by
  unfold HasAtLeastThreeCorrectedDefects
    HasAtMostTwoCorrectedDefects
  omega

/--
The concrete Section 11 tests.

Only `isTerminal` is supplied by the caller.  It is intended to become the
literal population `T_K` when the remaining assembly of Proposition 9.11 is
formalized.
-/
noncomputable def sectionElevenTests
    {N L : ℕ} (A : ℕ) (hN : 2 ≤ N)
    (isTerminal : SeparatedDyadicPair N L → Prop) :
    OrderedSectorTests (SeparatedDyadicPair N L) where
  smallPrimeProduct :=
    HasSmallCanonicalPrimeProduct A hN
  smallCanonicalHeight := fun pair ↦
    HasSmallCanonicalHeight A L pair.1.1 pair.1.2
  shallowCore := fun pair ↦
    HasCoreDensityAtMostThreeSixteenths
      A L pair.1.1 pair.1.2
  aligned := fun pair ↦
    IsCanonicallyAligned A L pair.1.1 pair.1.2
  manyDefects := fun pair ↦
    HasAtLeastThreeCorrectedDefects
      A L pair.1.1 pair.1.2
  terminal := isTerminal

/-- The sector selected for one separated pair. -/
noncomputable def sectionElevenSectorOf
    {N L : ℕ} (A : ℕ) (hN : 2 ≤ N)
    (isTerminal : SeparatedDyadicPair N L → Prop)
    (pair : SeparatedDyadicPair N L) :
    ResidualSector :=
  sectorOf (sectionElevenTests A hN isTerminal) pair

/-- The concrete finite population in one Section 11 sector. -/
noncomputable def sectionElevenSectorPairs
    {N L : ℕ} (A : ℕ) (hN : 2 ≤ N)
    (isTerminal : SeparatedDyadicPair N L → Prop)
    (sector : ResidualSector) :
    Finset (SeparatedDyadicPair N L) :=
  sectorPopulation
    (sectionElevenTests A hN isTerminal) sector

@[simp]
theorem mem_sectionElevenSectorPairs
    {N A L : ℕ} {hN : 2 ≤ N}
    {isTerminal : SeparatedDyadicPair N L → Prop}
    {sector : ResidualSector}
    {pair : SeparatedDyadicPair N L} :
    pair ∈
        sectionElevenSectorPairs A hN isTerminal sector ↔
      sectionElevenSectorOf A hN isTerminal pair = sector := by
  exact mem_sectorPopulation

/-! ## Manuscript-facing characterizations -/

@[simp]
theorem sectionElevenSectorOf_eq_one_iff
    {N A L : ℕ} {hN : 2 ≤ N}
    {isTerminal : SeparatedDyadicPair N L → Prop}
    {pair : SeparatedDyadicPair N L} :
    sectionElevenSectorOf A hN isTerminal pair =
        .smallPrimeProduct ↔
      HasSmallCanonicalPrimeProduct A hN pair := by
  simp [sectionElevenSectorOf, sectionElevenTests]

@[simp]
theorem sectionElevenSectorOf_eq_two_iff
    {N A L : ℕ} {hN : 2 ≤ N}
    {isTerminal : SeparatedDyadicPair N L → Prop}
    {pair : SeparatedDyadicPair N L} :
    sectionElevenSectorOf A hN isTerminal pair =
        .smallCanonicalHeight ↔
      HasLargeCanonicalPrimeProduct A hN pair ∧
        HasSmallCanonicalHeight
          A L pair.1.1 pair.1.2 := by
  simp [sectionElevenSectorOf, sectionElevenTests]

@[simp]
theorem sectionElevenSectorOf_eq_three_iff
    {N A L : ℕ} {hN : 2 ≤ N}
    {isTerminal : SeparatedDyadicPair N L → Prop}
    {pair : SeparatedDyadicPair N L} :
    sectionElevenSectorOf A hN isTerminal pair =
        .shallowCore ↔
      HasLargeCanonicalPrimeProduct A hN pair ∧
        ¬HasSmallCanonicalHeight
          A L pair.1.1 pair.1.2 ∧
        HasCoreDensityAtMostThreeSixteenths
          A L pair.1.1 pair.1.2 := by
  simp [sectionElevenSectorOf, sectionElevenTests]

@[simp]
theorem sectionElevenSectorOf_eq_four_iff
    {N A L : ℕ} {hN : 2 ≤ N}
    {isTerminal : SeparatedDyadicPair N L → Prop}
    {pair : SeparatedDyadicPair N L} :
    sectionElevenSectorOf A hN isTerminal pair =
        .alignedDeepCore ↔
      HasLargeCanonicalPrimeProduct A hN pair ∧
        ¬HasSmallCanonicalHeight
          A L pair.1.1 pair.1.2 ∧
        ¬HasCoreDensityAtMostThreeSixteenths
          A L pair.1.1 pair.1.2 ∧
        IsCanonicallyAligned
          A L pair.1.1 pair.1.2 := by
  simp [sectionElevenSectorOf, sectionElevenTests]

@[simp]
theorem sectionElevenSectorOf_eq_five_iff
    {N A L : ℕ} {hN : 2 ≤ N}
    {isTerminal : SeparatedDyadicPair N L → Prop}
    {pair : SeparatedDyadicPair N L} :
    sectionElevenSectorOf A hN isTerminal pair =
        .manyDefects ↔
      HasLargeCanonicalPrimeProduct A hN pair ∧
        ¬HasSmallCanonicalHeight
          A L pair.1.1 pair.1.2 ∧
        ¬HasCoreDensityAtMostThreeSixteenths
          A L pair.1.1 pair.1.2 ∧
        IsCanonicallyNonaligned
          A L pair.1.1 pair.1.2 ∧
        HasAtLeastThreeCorrectedDefects
          A L pair.1.1 pair.1.2 := by
  simp [sectionElevenSectorOf, sectionElevenTests]

@[simp]
theorem sectionElevenSectorOf_eq_six_iff
    {N A L : ℕ} {hN : 2 ≤ N}
    {isTerminal : SeparatedDyadicPair N L → Prop}
    {pair : SeparatedDyadicPair N L} :
    sectionElevenSectorOf A hN isTerminal pair =
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
        ¬isTerminal pair := by
  simp [sectionElevenSectorOf, sectionElevenTests]

@[simp]
theorem sectionElevenSectorOf_eq_seven_iff
    {N A L : ℕ} {hN : 2 ≤ N}
    {isTerminal : SeparatedDyadicPair N L → Prop}
    {pair : SeparatedDyadicPair N L} :
    sectionElevenSectorOf A hN isTerminal pair =
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
        isTerminal pair := by
  simp [sectionElevenSectorOf, sectionElevenTests]

/-! ## Compatibility with the exact Section 7 partition -/

/--
The first Section 11 population is definitionally the population of
Proposition 7.3.
-/
theorem sectionElevenSectorPairs_one_eq_smallProductPairs
    {N A L : ℕ} (hN : 2 ≤ N)
    (isTerminal : SeparatedDyadicPair N L → Prop) :
    sectionElevenSectorPairs A hN isTerminal
        .smallPrimeProduct =
      smallProductPairs N A L hN := by
  classical
  ext pair
  simp [HasSmallCanonicalPrimeProduct]

/--
The second Section 11 population is exactly the large-product,
small-canonical-height population of Proposition 7.4.
-/
theorem sectionElevenSectorPairs_two_eq_smallHeightLargeProductPairs
    {N A L : ℕ} (hN : 2 ≤ N)
    (isTerminal : SeparatedDyadicPair N L → Prop) :
    sectionElevenSectorPairs A hN isTerminal
        .smallCanonicalHeight =
      smallHeightLargeProductPairs N A L hN := by
  classical
  ext pair
  simp [HasSmallCanonicalPrimeProduct,
    HasLargeCanonicalPrimeProduct]

/--
The third Section 11 population is exactly the shallow-core population of
Proposition 7.5.
-/
theorem sectionElevenSectorPairs_three_eq_shallowCorePairs
    {N A L : ℕ} (hN : 2 ≤ N)
    (isTerminal : SeparatedDyadicPair N L → Prop) :
    sectionElevenSectorPairs A hN isTerminal
        .shallowCore =
      shallowCorePairs N A L hN := by
  classical
  ext pair
  simp [HasSmallCanonicalPrimeProduct,
    HasLargeCanonicalPrimeProduct]

/--
The last four Section 11 populations split exactly the `deepCorePairs`
complement left by Section 7.  Thus Lemma 11.1 genuinely refines the
previous formal partition instead of introducing a parallel ambient set.
-/
theorem sectionEleven_lateSectors_eq_deepCorePairs
    {N A L : ℕ} (hN : 2 ≤ N)
    (isTerminal : SeparatedDyadicPair N L → Prop) :
    (((sectionElevenSectorPairs A hN isTerminal
              .alignedDeepCore ∪
            sectionElevenSectorPairs A hN isTerminal
              .manyDefects) ∪
          sectionElevenSectorPairs A hN isTerminal
            .nonterminal) ∪
        sectionElevenSectorPairs A hN isTerminal
          .terminal) =
      SectionSevenPartition.deepCorePairs N A L hN := by
  classical
  ext pair
  simp only [Finset.mem_union, mem_sectionElevenSectorPairs,
    SectionSevenPartition.mem_deepCorePairs]
  constructor
  · rintro (((hfour | hfive) | hsix) | hseven)
    · have h :=
        sectionElevenSectorOf_eq_four_iff.mp hfour
      refine ⟨?_, h.2.1, ?_⟩
      · simpa [HasLargeCanonicalPrimeProduct] using h.1
      · unfold HasCoreDensityAtMostThreeSixteenths at h
        omega
    · have h :=
        sectionElevenSectorOf_eq_five_iff.mp hfive
      refine ⟨?_, h.2.1, ?_⟩
      · simpa [HasLargeCanonicalPrimeProduct] using h.1
      · unfold HasCoreDensityAtMostThreeSixteenths at h
        omega
    · have h :=
        sectionElevenSectorOf_eq_six_iff.mp hsix
      refine ⟨?_, h.2.1, ?_⟩
      · simpa [HasLargeCanonicalPrimeProduct] using h.1
      · unfold HasCoreDensityAtMostThreeSixteenths at h
        omega
    · have h :=
        sectionElevenSectorOf_eq_seven_iff.mp hseven
      refine ⟨?_, h.2.1, ?_⟩
      · simpa [HasLargeCanonicalPrimeProduct] using h.1
      · unfold HasCoreDensityAtMostThreeSixteenths at h
        omega
  · rintro ⟨hlarge, hheight, hdepth⟩
    have hproduct :
        HasLargeCanonicalPrimeProduct A hN pair := by
      simpa [HasLargeCanonicalPrimeProduct] using hlarge
    have hdensity :
        ¬HasCoreDensityAtMostThreeSixteenths
          A L pair.1.1 pair.1.2 := by
      unfold HasCoreDensityAtMostThreeSixteenths
      omega
    by_cases haligned :
        IsCanonicallyAligned A L pair.1.1 pair.1.2
    · apply Or.inl
      apply Or.inl
      apply Or.inl
      exact sectionElevenSectorOf_eq_four_iff.mpr
        ⟨hproduct, hheight, hdensity, haligned⟩
    · have hnonaligned :
          IsCanonicallyNonaligned
            A L pair.1.1 pair.1.2 :=
        not_isCanonicallyAligned_iff_nonaligned.mp
          haligned
      by_cases hdefects :
          HasAtLeastThreeCorrectedDefects
            A L pair.1.1 pair.1.2
      · apply Or.inl
        apply Or.inl
        apply Or.inr
        exact sectionElevenSectorOf_eq_five_iff.mpr
          ⟨hproduct, hheight, hdensity, hnonaligned,
            hdefects⟩
      · have hfew :
            HasAtMostTwoCorrectedDefects
              A L pair.1.1 pair.1.2 :=
          not_atLeastThreeCorrectedDefects_iff_atMostTwo.mp
            hdefects
        by_cases hterminal : isTerminal pair
        · apply Or.inr
          exact sectionElevenSectorOf_eq_seven_iff.mpr
            ⟨hproduct, hheight, hdensity, hnonaligned,
              hfew, hterminal⟩
        · apply Or.inl
          apply Or.inr
          exact sectionElevenSectorOf_eq_six_iff.mpr
            ⟨hproduct, hheight, hdensity, hnonaligned,
              hfew, hterminal⟩

/-! ## Exact partition statements for separated pairs -/

/-- Distinct concrete Section 11 populations are disjoint. -/
theorem sectionElevenSectorPairs_disjoint
    {N A L : ℕ} (hN : 2 ≤ N)
    (isTerminal : SeparatedDyadicPair N L → Prop)
    {s t : ResidualSector} (hst : s ≠ t) :
    Disjoint
      (sectionElevenSectorPairs A hN isTerminal s)
      (sectionElevenSectorPairs A hN isTerminal t) :=
  sectorPopulations_disjoint
    (sectionElevenTests A hN isTerminal) hst

/--
Parameterized form of Lemma 11.1: for every explicit terminal predicate, the
seven ordered populations cover every separated dyadic pair.
-/
theorem lemma_eleven_one_populations_cover
    {N A L : ℕ} (hN : 2 ≤ N)
    (isTerminal : SeparatedDyadicPair N L → Prop) :
    ((((((sectionElevenSectorPairs A hN isTerminal
                .smallPrimeProduct ∪
              sectionElevenSectorPairs A hN isTerminal
                .smallCanonicalHeight) ∪
            sectionElevenSectorPairs A hN isTerminal
              .shallowCore) ∪
          sectionElevenSectorPairs A hN isTerminal
            .alignedDeepCore) ∪
        sectionElevenSectorPairs A hN isTerminal
          .manyDefects) ∪
      sectionElevenSectorPairs A hN isTerminal
        .nonterminal) ∪
      sectionElevenSectorPairs A hN isTerminal
        .terminal) =
      Finset.univ :=
  seven_sector_populations_cover
    (sectionElevenTests A hN isTerminal)

/--
Parameterized uniqueness form of Lemma 11.1: for every explicit terminal
predicate, each separated pair belongs to exactly one residual sector.
-/
theorem lemma_eleven_one_existsUnique_sector
    {N A L : ℕ} (hN : 2 ≤ N)
    (isTerminal : SeparatedDyadicPair N L → Prop)
    (pair : SeparatedDyadicPair N L) :
    ∃! sector : ResidualSector,
      pair ∈
        sectionElevenSectorPairs A hN isTerminal sector :=
  existsUnique_sector
    (sectionElevenTests A hN isTerminal) pair

end

end SectionElevenPartition
end PaperC
