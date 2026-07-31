import PaperC.Asymptotics.PropositionSixteenOneCore
import PaperC.Combinatorics.CanonicalTerminalPopulation
import PaperC.LinearAlgebra.CanonicalSmallRows

set_option maxHeartbeats 2400000

/-!
# The canonical terminal population on a bounded-ratio interval

The bounded-ratio partition in `PropositionSixteenOneCore` deliberately
accepts an arbitrary last predicate.  This file supplies the canonical
choice used in Lemmas 17.28--17.30.

For a separated pair, put

* `s = B - c#`, where `B = L+1`;
* `k̃` equal to the rank of the concrete arithmetic small-row matrix;
* `R_K(B) = floor (K sqrt(B) / log(B))`.

The literal rank form of `T_K` is `s + k̃ ≤ R_K(B)`.  We also expose the
intrinsic, bridge-free form

`B + D# ≤ τ + R_K(B)`.

The proved source-scoped arithmetic equivalence of Lemma 9.10 makes the two
conditions equivalent on the nonaligned core where they are used.  Keeping
the intrinsic condition available lets the analytic estimate for Lemma
17.28 use the actual residual exponent directly.

No asymptotic estimate is postulated here.  The module proves only exact
finite identities, the ordered-sector characterizations, and the
automatic `B-3s` count of isolated two-vertex components.
-/

namespace PaperC
namespace BoundedRatioCanonicalTerminalPopulation

open scoped BigOperators
open Affine
open Affine.CanonicalRationalCode
open CanonicalExactRank
open CanonicalResidualComponents
open CanonicalResidualQuotient
open CanonicalSmallRows
open LargePrimeGraph
open LargePrimeGraphResolution
open LargePrimeOccurrences
open PinnedGraphResolution
open PropositionSixteenOne
open ResidualComponentCounts
open SectionElevenPartition
open SmallComponentExtraction
open TerminalComponentCount

noncomputable section

noncomputable local instance instDecidableLargePrimeAdj
    (x y L : ℕ) :
    DecidableRel (largePrimeGraph x y L).Adj :=
  Classical.decRel _

/-! ## The canonical rank and the manuscript threshold -/

/-- The terminal slack `s = B-c#`, with `B=L+1`. -/
noncomputable def boundedTerminalSlack
    {N M L : ℕ} (A : ℕ)
    (pair : SeparatedBoundedRatioPair N M L) : ℕ :=
  L + 1 -
    canonicalResidualComponentCount
      A pair.1.1 pair.1.2 L

/-- The literal canonical small-row rank `k̃`. -/
noncomputable def boundedCanonicalSmallRowRank
    {N M L : ℕ} (A : ℕ)
    (pair : SeparatedBoundedRatioPair N M L) : ℕ :=
  canonicalSmallRowRank
    (canonicalArithmeticSmallRowMatrix
      A pair.1.1 pair.1.2 L)

/-- The real threshold `K sqrt(B)/log(B)` from (9.10). -/
noncomputable def terminalRankScale
    (K : ℝ) (L : ℕ) : ℝ :=
  K * Real.sqrt ((L + 1 : ℕ) : ℝ) /
    Real.log ((L + 1 : ℕ) : ℝ)

/-- Its exact natural-number realization. -/
noncomputable def terminalRankBudget
    (K : ℝ) (L : ℕ) : ℕ :=
  ⌊terminalRankScale K L⌋₊

/-- The rank scale is nonnegative once `K≥0` and `B≥2`. -/
theorem terminalRankScale_nonneg
    {K : ℝ} {L : ℕ} (hK : 0 ≤ K) (hB : 2 ≤ L + 1) :
    0 ≤ terminalRankScale K L := by
  unfold terminalRankScale
  have hlog : 0 < Real.log ((L + 1 : ℕ) : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hB
  positivity

/-- The floor budget lies below the real manuscript threshold. -/
theorem terminalRankBudget_cast_le_scale
    {K : ℝ} {L : ℕ} (hK : 0 ≤ K) (hB : 2 ≤ L + 1) :
    (terminalRankBudget K L : ℝ) ≤ terminalRankScale K L := by
  unfold terminalRankBudget
  exact Nat.floor_le (terminalRankScale_nonneg hK hB)

/-- Exact conversion between the natural and real rank thresholds. -/
theorem le_terminalRankBudget_iff_cast_le_scale
    {K : ℝ} {L r : ℕ} (hK : 0 ≤ K) (hB : 2 ≤ L + 1) :
    r ≤ terminalRankBudget K L ↔
      (r : ℝ) ≤ terminalRankScale K L := by
  constructor
  · intro hr
    have hcast :
        (r : ℝ) ≤ (terminalRankBudget K L : ℝ) := by
      exact_mod_cast hr
    exact hcast.trans
      (terminalRankBudget_cast_le_scale hK hB)
  · intro hr
    unfold terminalRankBudget
    exact Nat.le_floor hr

/-! ## Bounds independent of the small-row presentation -/

/-- The canonical component count is at most `B=L+1`. -/
theorem canonicalResidualComponentCount_le_runLength
    {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) :
    canonicalResidualComponentCount
        A pair.1.1 pair.1.2 L ≤
      L + 1 := by
  have hxy := pair_coordinates_two_le hN pair
  have hbudget :=
    canonicalCorrected_add_twice_residual_le
      A pair.1.1 pair.1.2 L
      (by omega) (by omega)
  omega

/-- Every represented small prime lies below the bounded-ratio cutoff. -/
theorem runLength_le_boundedRatioCutoff
    {N M L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) :
    L + 1 ≤ boundedRatioCutoff M L := by
  have hpair :=
    mem_separatedBoundedRatioPairs.mp pair.2
  have hx := mem_boundedRatioBlock.mp hpair.1
  unfold boundedRatioCutoff
  omega

/--
Source-exact Lemma 9.10 provider on a bounded-ratio pair in the canonical
nonaligned branch.  Both endpoint-coverage hypotheses required by the
finite-cylinder boundary map follow from membership in the bounded-ratio
block.
-/
theorem arithmeticKernelEquivalence_of_isCanonicallyNonaligned
    {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L)
    (hnonaligned :
      IsCanonicallyNonaligned
        A L pair.1.1 pair.1.2) :
    Nonempty
      (ResidualQuotient
          (boundedRatioCutoff M L) A
          pair.1.1 pair.1.2 L
          (pair_coordinates_two_le hN pair).1
          (pair_coordinates_two_le hN pair).2 ≃ₗ[F₂]
        LinearMap.ker
          (canonicalArithmeticSmallRowMatrix
            A pair.1.1 pair.1.2 L).mulVecLin) := by
  have hpair :=
    mem_separatedBoundedRatioPairs.mp pair.2
  exact
    canonicalArithmeticKernelEquivalence_of_choice_none
      (pair_coordinates_two_le hN pair).1
      (pair_coordinates_two_le hN pair).2
      (runLength_le_boundedRatioCutoff hN pair)
      (startWindow_le_boundedRatioCutoff
        hpair.1 (le_refl L))
      (startWindow_le_boundedRatioCutoff
        hpair.2.1 (le_refl L))
      hnonaligned

/-- The general quotient-core estimate `τ≤D#+c#` on `[N,M)`. -/
theorem pairTau_le_corrected_add_components
    {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) :
    pairTau A hN pair ≤
      canonicalCorrectedDefectCount
          A pair.1.1 pair.1.2 L +
        canonicalResidualComponentCount
          A pair.1.1 pair.1.2 L := by
  have hpair :=
    mem_separatedBoundedRatioPairs.mp pair.2
  have hxy := pair_coordinates_two_le hN pair
  unfold pairTau
  apply
    residualTau_le_canonicalCorrected_add_residual
      hxy.1 hxy.2
  · exact
      startWindow_le_boundedRatioCutoff
        hpair.1 (le_refl L)
  · exact
      startWindow_le_boundedRatioCutoff
        hpair.2.1 (le_refl L)

/--
The intrinsic terminal slack `B+D#-τ`.  It is defined from the actual
bounded-ratio relation rank and therefore uses no small-row presentation.
-/
noncomputable def boundedIntrinsicTerminalSlack
    {N M L : ℕ} (A : ℕ) (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) : ℕ :=
  L + 1 +
      canonicalCorrectedDefectCount
        A pair.1.1 pair.1.2 L -
    pairTau A hN pair

/-- The ordinary slack `s` is always bounded by the intrinsic slack. -/
theorem boundedTerminalSlack_le_intrinsic
    {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) :
    boundedTerminalSlack A pair ≤
      boundedIntrinsicTerminalSlack A hN pair := by
  have hc :=
    canonicalResidualComponentCount_le_runLength
      (A := A) hN pair
  have htau :=
    pairTau_le_corrected_add_components
      (A := A) hN pair
  unfold boundedTerminalSlack boundedIntrinsicTerminalSlack
  omega

/-- Subtraction-free form of the intrinsic terminal budget. -/
theorem intrinsicSlack_le_iff
    {N M A L R : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) :
    boundedIntrinsicTerminalSlack A hN pair ≤ R ↔
      L + 1 +
          canonicalCorrectedDefectCount
            A pair.1.1 pair.1.2 L ≤
        pairTau A hN pair + R := by
  have htau :=
    pairTau_le_corrected_add_components
      (A := A) hN pair
  have hc :=
    canonicalResidualComponentCount_le_runLength
      (A := A) hN pair
  unfold boundedIntrinsicTerminalSlack
  omega

/-! ## Lemma 17.27 from the source-exact Lemma 9.10 -/

/--
Bounded-ratio form of the exact rank formula in its manuscript scope.
-/
theorem pairTau_eq_corrected_add_components_sub_canonicalRank
    {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L)
    (hnonaligned :
      IsCanonicallyNonaligned
        A L pair.1.1 pair.1.2) :
    pairTau A hN pair =
      canonicalCorrectedDefectCount
          A pair.1.1 pair.1.2 L +
        canonicalResidualComponentCount
          A pair.1.1 pair.1.2 L -
        boundedCanonicalSmallRowRank A pair := by
  unfold pairTau boundedCanonicalSmallRowRank
  have hpair :=
    mem_separatedBoundedRatioPairs.mp pair.2
  exact
    residualTau_eq_corrected_add_components_sub_arithmeticRank_of_choice_none
      (pair_coordinates_two_le hN pair).1
      (pair_coordinates_two_le hN pair).2
      (runLength_le_boundedRatioCutoff hN pair)
      (startWindow_le_boundedRatioCutoff
        hpair.1 (le_refl L))
      (startWindow_le_boundedRatioCutoff
        hpair.2.1 (le_refl L))
      hnonaligned

/-- Non-truncated form `τ+k̃=D#+c#`. -/
theorem pairTau_add_canonicalRank_eq_corrected_add_components
    {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L)
    (hnonaligned :
      IsCanonicallyNonaligned
        A L pair.1.1 pair.1.2) :
    pairTau A hN pair +
        boundedCanonicalSmallRowRank A pair =
      canonicalCorrectedDefectCount
          A pair.1.1 pair.1.2 L +
        canonicalResidualComponentCount
          A pair.1.1 pair.1.2 L := by
  have heq :=
    pairTau_eq_corrected_add_components_sub_canonicalRank
      hN pair hnonaligned
  have hxy := pair_coordinates_two_le hN pair
  have hrank :
      boundedCanonicalSmallRowRank A pair ≤
        canonicalCorrectedDefectCount
            A pair.1.1 pair.1.2 L +
          canonicalResidualComponentCount
            A pair.1.1 pair.1.2 L := by
    unfold boundedCanonicalSmallRowRank
    exact
      canonicalSmallRowRank_le_corrected_add_components
        hxy.1 hxy.2
        (canonicalArithmeticSmallRowMatrix
          A pair.1.1 pair.1.2 L)
  omega

/-- Under Lemma 9.10, `B+D#-τ` is literally `s+k̃`. -/
theorem boundedIntrinsicTerminalSlack_eq_slack_add_canonicalRank
    {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L)
    (hnonaligned :
      IsCanonicallyNonaligned
        A L pair.1.1 pair.1.2) :
    boundedIntrinsicTerminalSlack A hN pair =
      boundedTerminalSlack A pair +
        boundedCanonicalSmallRowRank A pair := by
  have hc :=
    canonicalResidualComponentCount_le_runLength
      (A := A) hN pair
  have hrank :=
    pairTau_add_canonicalRank_eq_corrected_add_components
      hN pair hnonaligned
  unfold boundedIntrinsicTerminalSlack boundedTerminalSlack
  omega

/-- Exact equivalence of the intrinsic and manuscript rank budgets. -/
theorem intrinsicBudget_iff_slack_add_rank_budget
    {N M A L R : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L)
    (hnonaligned :
      IsCanonicallyNonaligned
        A L pair.1.1 pair.1.2) :
    L + 1 +
          canonicalCorrectedDefectCount
            A pair.1.1 pair.1.2 L ≤
        pairTau A hN pair + R ↔
      boundedTerminalSlack A pair +
          boundedCanonicalSmallRowRank A pair ≤ R := by
  rw [← intrinsicSlack_le_iff hN pair,
    boundedIntrinsicTerminalSlack_eq_slack_add_canonicalRank
      hN pair hnonaligned]

/-! ## Canonical terminal predicates -/

/-- Literal `s+k̃≤floor(K sqrt(B)/log(B))` predicate. -/
noncomputable def boundedRankTerminalPredicate
    (A : ℕ) (K : ℝ) : TerminalPredicateFamily :=
  fun _N _M L pair ↦
    boundedTerminalSlack A pair +
        boundedCanonicalSmallRowRank A pair ≤
      terminalRankBudget K L

/--
Intrinsic terminal predicate, expressed only with `τ`, `D#`, and the
integer threshold.  Below `N=2` it is set to `False`.
-/
noncomputable def boundedIntrinsicTerminalPredicate
    (A : ℕ) (K : ℝ) : TerminalPredicateFamily :=
  fun N _M L pair ↦
    if hN : 2 ≤ N then
      L + 1 +
          canonicalCorrectedDefectCount
            A pair.1.1 pair.1.2 L ≤
        pairTau A hN pair + terminalRankBudget K L
    else False

/-- The five structural conditions preceding the terminal test. -/
def boundedTerminalCoreConditions
    {N M L : ℕ} (A : ℕ) (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) : Prop :=
  ¬HasSmallCanonicalPrimeProduct A hN pair ∧
    ¬SmallHeightLargeProductPairs.HasSmallCanonicalHeight
        A L pair.1.1 pair.1.2 ∧
    ¬ShallowCorePairs.HasCoreDensityAtMostThreeSixteenths
        A L pair.1.1 pair.1.2 ∧
    IsCanonicallyNonaligned
        A L pair.1.1 pair.1.2 ∧
    HasAtMostTwoCorrectedDefects
        A L pair.1.1 pair.1.2

/-- Exact seventh-fibre characterization for the literal rank predicate. -/
theorem boundedRatioSectorOf_eq_terminal_rank_iff
    {N M A L : ℕ} {hN : 2 ≤ N}
    {K : ℝ} {pair : SeparatedBoundedRatioPair N M L} :
    boundedRatioSectorOf A hN
        (boundedRankTerminalPredicate A K) pair =
        .terminal ↔
      boundedTerminalCoreConditions A hN pair ∧
        boundedTerminalSlack A pair +
            boundedCanonicalSmallRowRank A pair ≤
          terminalRankBudget K L := by
  rw [boundedRatioSectorOf]
  rw [sectorOf_eq_terminal_iff]
  simp only [boundedRatioSectorTests,
    boundedRankTerminalPredicate,
    not_isCanonicallyAligned_iff_nonaligned,
    not_atLeastThreeCorrectedDefects_iff_atMostTwo]
  simp only [boundedTerminalCoreConditions, and_assoc]

/-- Exact sixth-fibre characterization for the literal rank predicate. -/
theorem boundedRatioSectorOf_eq_nonterminal_rank_iff
    {N M A L : ℕ} {hN : 2 ≤ N}
    {K : ℝ} {pair : SeparatedBoundedRatioPair N M L} :
    boundedRatioSectorOf A hN
        (boundedRankTerminalPredicate A K) pair =
        .nonterminal ↔
      boundedTerminalCoreConditions A hN pair ∧
        terminalRankBudget K L <
          boundedTerminalSlack A pair +
            boundedCanonicalSmallRowRank A pair := by
  rw [boundedRatioSectorOf]
  rw [sectorOf_eq_nonterminal_iff]
  simp only [boundedRatioSectorTests,
    boundedRankTerminalPredicate,
    not_isCanonicallyAligned_iff_nonaligned,
    not_atLeastThreeCorrectedDefects_iff_atMostTwo,
    not_le]
  simp only [boundedTerminalCoreConditions, and_assoc]

/-- Exact seventh-fibre characterization for the intrinsic predicate. -/
theorem boundedRatioSectorOf_eq_terminal_intrinsic_iff
    {N M A L : ℕ} {hN : 2 ≤ N}
    {K : ℝ} {pair : SeparatedBoundedRatioPair N M L} :
    boundedRatioSectorOf A hN
        (boundedIntrinsicTerminalPredicate A K) pair =
        .terminal ↔
      boundedTerminalCoreConditions A hN pair ∧
        L + 1 +
            canonicalCorrectedDefectCount
              A pair.1.1 pair.1.2 L ≤
          pairTau A hN pair + terminalRankBudget K L := by
  rw [boundedRatioSectorOf]
  rw [sectorOf_eq_terminal_iff]
  simp only [boundedRatioSectorTests,
    boundedIntrinsicTerminalPredicate, dif_pos hN,
    not_isCanonicallyAligned_iff_nonaligned,
    not_atLeastThreeCorrectedDefects_iff_atMostTwo]
  simp only [boundedTerminalCoreConditions, and_assoc]

/-- Exact sixth-fibre characterization for the intrinsic predicate. -/
theorem boundedRatioSectorOf_eq_nonterminal_intrinsic_iff
    {N M A L : ℕ} {hN : 2 ≤ N}
    {K : ℝ} {pair : SeparatedBoundedRatioPair N M L} :
    boundedRatioSectorOf A hN
        (boundedIntrinsicTerminalPredicate A K) pair =
        .nonterminal ↔
      boundedTerminalCoreConditions A hN pair ∧
        pairTau A hN pair + terminalRankBudget K L <
          L + 1 +
            canonicalCorrectedDefectCount
              A pair.1.1 pair.1.2 L := by
  rw [boundedRatioSectorOf]
  rw [sectorOf_eq_nonterminal_iff]
  simp only [boundedRatioSectorTests,
    boundedIntrinsicTerminalPredicate, dif_pos hN,
    not_isCanonicallyAligned_iff_nonaligned,
    not_atLeastThreeCorrectedDefects_iff_atMostTwo,
    not_le]
  simp only [boundedTerminalCoreConditions, and_assoc]

/--
On every pair satisfying Lemma 9.10, the two canonical terminal tests agree.
-/
theorem boundedRankTerminalPredicate_iff_intrinsic
    {N M A L : ℕ} (hN : 2 ≤ N) (K : ℝ)
    (pair : SeparatedBoundedRatioPair N M L)
    (hnonaligned :
      IsCanonicallyNonaligned
        A L pair.1.1 pair.1.2) :
    boundedRankTerminalPredicate A K N M L pair ↔
      boundedIntrinsicTerminalPredicate A K N M L pair := by
  unfold boundedRankTerminalPredicate
    boundedIntrinsicTerminalPredicate
  rw [dif_pos hN]
  exact
    (intrinsicBudget_iff_slack_add_rank_budget
      (R := terminalRankBudget K L) hN pair hnonaligned).symm

/-! ## Literal finite populations and masses -/

/-- The rank-defined bounded-ratio `T_K`. -/
noncomputable def boundedRankTerminalPairs
    (N M A L : ℕ) (hN : 2 ≤ N) (K : ℝ) :
    Finset (SeparatedBoundedRatioPair N M L) := by
  classical
  exact Finset.univ.filter fun pair ↦
    boundedTerminalCoreConditions A hN pair ∧
      boundedTerminalSlack A pair +
          boundedCanonicalSmallRowRank A pair ≤
        terminalRankBudget K L

/-- The sixth fibre, i.e. the structural core outside the rank-defined `T_K`. -/
noncomputable def boundedRankNonterminalPairs
    (N M A L : ℕ) (hN : 2 ≤ N) (K : ℝ) :
    Finset (SeparatedBoundedRatioPair N M L) := by
  classical
  exact Finset.univ.filter fun pair ↦
    boundedTerminalCoreConditions A hN pair ∧
      terminalRankBudget K L <
        boundedTerminalSlack A pair +
          boundedCanonicalSmallRowRank A pair

/-- The intrinsic realization of the bounded-ratio terminal population. -/
noncomputable def boundedIntrinsicTerminalPairs
    (N M A L : ℕ) (hN : 2 ≤ N) (K : ℝ) :
    Finset (SeparatedBoundedRatioPair N M L) := by
  classical
  exact Finset.univ.filter fun pair ↦
    boundedTerminalCoreConditions A hN pair ∧
      L + 1 +
          canonicalCorrectedDefectCount
            A pair.1.1 pair.1.2 L ≤
        pairTau A hN pair + terminalRankBudget K L

/-- The intrinsic sixth fibre, with the rank saving written using `τ`. -/
noncomputable def boundedIntrinsicNonterminalPairs
    (N M A L : ℕ) (hN : 2 ≤ N) (K : ℝ) :
    Finset (SeparatedBoundedRatioPair N M L) := by
  classical
  exact Finset.univ.filter fun pair ↦
    boundedTerminalCoreConditions A hN pair ∧
      pairTau A hN pair + terminalRankBudget K L <
        L + 1 +
          canonicalCorrectedDefectCount
            A pair.1.1 pair.1.2 L

@[simp]
theorem mem_boundedRankTerminalPairs
    {N M A L : ℕ} {hN : 2 ≤ N} {K : ℝ}
    {pair : SeparatedBoundedRatioPair N M L} :
    pair ∈ boundedRankTerminalPairs N M A L hN K ↔
      boundedTerminalCoreConditions A hN pair ∧
        boundedTerminalSlack A pair +
            boundedCanonicalSmallRowRank A pair ≤
          terminalRankBudget K L := by
  simp [boundedRankTerminalPairs]

@[simp]
theorem mem_boundedRankNonterminalPairs
    {N M A L : ℕ} {hN : 2 ≤ N} {K : ℝ}
    {pair : SeparatedBoundedRatioPair N M L} :
    pair ∈ boundedRankNonterminalPairs N M A L hN K ↔
      boundedTerminalCoreConditions A hN pair ∧
        terminalRankBudget K L <
          boundedTerminalSlack A pair +
            boundedCanonicalSmallRowRank A pair := by
  simp [boundedRankNonterminalPairs]

@[simp]
theorem mem_boundedIntrinsicTerminalPairs
    {N M A L : ℕ} {hN : 2 ≤ N} {K : ℝ}
    {pair : SeparatedBoundedRatioPair N M L} :
    pair ∈ boundedIntrinsicTerminalPairs N M A L hN K ↔
      boundedTerminalCoreConditions A hN pair ∧
        L + 1 +
            canonicalCorrectedDefectCount
              A pair.1.1 pair.1.2 L ≤
          pairTau A hN pair + terminalRankBudget K L := by
  simp [boundedIntrinsicTerminalPairs]

@[simp]
theorem mem_boundedIntrinsicNonterminalPairs
    {N M A L : ℕ} {hN : 2 ≤ N} {K : ℝ}
    {pair : SeparatedBoundedRatioPair N M L} :
    pair ∈ boundedIntrinsicNonterminalPairs N M A L hN K ↔
      boundedTerminalCoreConditions A hN pair ∧
        pairTau A hN pair + terminalRankBudget K L <
          L + 1 +
            canonicalCorrectedDefectCount
              A pair.1.1 pair.1.2 L := by
  simp [boundedIntrinsicNonterminalPairs]

/-- Sector seven is exactly the literal rank-defined `T_K`. -/
theorem boundedRatioSectorPairs_terminal_eq_rankTerminalPairs
    {N M A L : ℕ} (hN : 2 ≤ N) (K : ℝ) :
    boundedRatioSectorPairs
        N M A L hN (boundedRankTerminalPredicate A K)
        .terminal =
      boundedRankTerminalPairs N M A L hN K := by
  classical
  ext pair
  rw [mem_boundedRatioSectorPairs,
    boundedRatioSectorOf_eq_terminal_rank_iff,
    mem_boundedRankTerminalPairs]

/-- Sector six is exactly the structural complement of `T_K`. -/
theorem boundedRatioSectorPairs_nonterminal_eq_rankNonterminalPairs
    {N M A L : ℕ} (hN : 2 ≤ N) (K : ℝ) :
    boundedRatioSectorPairs
        N M A L hN (boundedRankTerminalPredicate A K)
        .nonterminal =
      boundedRankNonterminalPairs N M A L hN K := by
  classical
  ext pair
  rw [mem_boundedRatioSectorPairs,
    boundedRatioSectorOf_eq_nonterminal_rank_iff,
    mem_boundedRankNonterminalPairs]

/-- Sector seven for the intrinsic predicate is its literal finite set. -/
theorem boundedRatioSectorPairs_terminal_eq_intrinsicTerminalPairs
    {N M A L : ℕ} (hN : 2 ≤ N) (K : ℝ) :
    boundedRatioSectorPairs
        N M A L hN (boundedIntrinsicTerminalPredicate A K)
        .terminal =
      boundedIntrinsicTerminalPairs N M A L hN K := by
  classical
  ext pair
  rw [mem_boundedRatioSectorPairs,
    boundedRatioSectorOf_eq_terminal_intrinsic_iff,
    mem_boundedIntrinsicTerminalPairs]

/-- Sector six for the intrinsic predicate is its literal finite complement. -/
theorem boundedRatioSectorPairs_nonterminal_eq_intrinsicNonterminalPairs
    {N M A L : ℕ} (hN : 2 ≤ N) (K : ℝ) :
    boundedRatioSectorPairs
        N M A L hN (boundedIntrinsicTerminalPredicate A K)
        .nonterminal =
      boundedIntrinsicNonterminalPairs N M A L hN K := by
  classical
  ext pair
  rw [mem_boundedRatioSectorPairs,
    boundedRatioSectorOf_eq_nonterminal_intrinsic_iff,
    mem_boundedIntrinsicNonterminalPairs]

/-- Pairwise equality of the two terminal populations under Lemma 9.10. -/
theorem mem_rankTerminalPairs_iff_mem_intrinsicTerminalPairs
    {N M A L : ℕ} (hN : 2 ≤ N) (K : ℝ)
    (pair : SeparatedBoundedRatioPair N M L) :
    pair ∈ boundedRankTerminalPairs N M A L hN K ↔
      pair ∈ boundedIntrinsicTerminalPairs N M A L hN K := by
  rw [mem_boundedRankTerminalPairs,
    mem_boundedIntrinsicTerminalPairs]
  exact and_congr_right fun hcore ↦
    (intrinsicBudget_iff_slack_add_rank_budget
      (R := terminalRankBudget K L) hN pair
      hcore.2.2.2.1).symm

/-- Pairwise equality of the two nonterminal populations under Lemma 9.10. -/
theorem mem_rankNonterminalPairs_iff_mem_intrinsicNonterminalPairs
    {N M A L : ℕ} (hN : 2 ≤ N) (K : ℝ)
    (pair : SeparatedBoundedRatioPair N M L) :
    pair ∈ boundedRankNonterminalPairs N M A L hN K ↔
      pair ∈ boundedIntrinsicNonterminalPairs N M A L hN K := by
  rw [mem_boundedRankNonterminalPairs,
    mem_boundedIntrinsicNonterminalPairs]
  apply and_congr_right
  intro hcore
  have heq :=
    intrinsicBudget_iff_slack_add_rank_budget
      (R := terminalRankBudget K L) hN pair
      hcore.2.2.2.1
  omega

/-- Residual mass of the literal bounded-ratio `T_K`. -/
noncomputable def boundedRankTerminalResidualMass
    (N M A L : ℕ) (hN : 2 ≤ N) (K : ℝ) : ℕ :=
  ∑ pair ∈ boundedRankTerminalPairs N M A L hN K,
    residualWeight A hN pair

/-- Residual mass of the intrinsic sixth fibre. -/
noncomputable def boundedIntrinsicNonterminalResidualMass
    (N M A L : ℕ) (hN : 2 ≤ N) (K : ℝ) : ℕ :=
  ∑ pair ∈ boundedIntrinsicNonterminalPairs N M A L hN K,
    residualWeight A hN pair

/-- First starts represented in the literal bounded-ratio `T_K`. -/
noncomputable def boundedRankTerminalFirstStarts
    (N M A L : ℕ) (hN : 2 ≤ N) (K : ℝ) :
    Finset ℕ :=
  (boundedRankTerminalPairs N M A L hN K).image
    (fun pair ↦ pair.1.1)

/-- Canonical nonalignment forces the bounded-ratio systematic rank to vanish. -/
theorem pairSigma_eq_zero_of_isCanonicallyNonaligned
    {N M A L : ℕ}
    {pair : SeparatedBoundedRatioPair N M L}
    (hnonaligned :
      IsCanonicallyNonaligned
        A L pair.1.1 pair.1.2) :
    pairSigma A pair = 0 := by
  unfold IsCanonicallyNonaligned at hnonaligned
  simp [pairSigma, RationalMassFinite.canonicalPairSigma,
    canonicalMultiplicity, hnonaligned]

/-- Every rank-terminal pair satisfies the elementary bound `τ≤B+2`. -/
theorem pairTau_le_runLength_add_two_of_mem_rankTerminal
    {N M A L : ℕ} {hN : 2 ≤ N} {K : ℝ}
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈ boundedRankTerminalPairs N M A L hN K) :
    pairTau A hN pair ≤ L + 1 + 2 := by
  have hdata := mem_boundedRankTerminalPairs.mp hpair
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

/--
The intrinsic nonterminal condition gives one full extra unit beyond the
integer budget in the exponent.
-/
theorem pairTau_add_budget_succ_le_corrected_runLength
    {N M A L : ℕ} {hN : 2 ≤ N} {K : ℝ}
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈ boundedIntrinsicNonterminalPairs
        N M A L hN K) :
    pairTau A hN pair + (terminalRankBudget K L + 1) ≤
      L + 1 +
        canonicalCorrectedDefectCount
          A pair.1.1 pair.1.2 L := by
  have hdata :=
    mem_boundedIntrinsicNonterminalPairs.mp hpair
  omega

/-- The intrinsic sixth fibre is canonically nonaligned. -/
theorem pairSigma_eq_zero_of_mem_intrinsicNonterminal
    {N M A L : ℕ} {hN : 2 ≤ N} {K : ℝ}
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈ boundedIntrinsicNonterminalPairs
        N M A L hN K) :
    pairSigma A pair = 0 := by
  have hdata :=
    mem_boundedIntrinsicNonterminalPairs.mp hpair
  unfold boundedTerminalCoreConditions at hdata
  exact
    pairSigma_eq_zero_of_isCanonicallyNonaligned
      hdata.1.2.2.2.1

/--
Exact pointwise saving behind Lemma 17.28.  The factor
`2^(R_K(B)+1)` has been extracted without any rank-presentation hypothesis.
-/
theorem residualWeight_mul_two_pow_budget_succ_le
    {N M A L : ℕ} {hN : 2 ≤ N} {K : ℝ}
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈ boundedIntrinsicNonterminalPairs
        N M A L hN K) :
    residualWeight A hN pair *
        2 ^ (terminalRankBudget K L + 1) ≤
      4 * 2 ^ (L + 1) := by
  have hexponent :=
    pairTau_add_budget_succ_le_corrected_runLength hpair
  have hdata :=
    mem_boundedIntrinsicNonterminalPairs.mp hpair
  unfold boundedTerminalCoreConditions at hdata
  have hD :
      canonicalCorrectedDefectCount
          A pair.1.1 pair.1.2 L ≤ 2 :=
    hdata.1.2.2.2.2
  have hsigma :=
    pairSigma_eq_zero_of_mem_intrinsicNonterminal hpair
  have hweight :
      residualWeight A hN pair ≤
        2 ^ pairTau A hN pair := by
    unfold residualWeight
    simp only [hsigma, pow_zero, one_mul]
    exact Nat.sub_le _ _
  calc
    residualWeight A hN pair *
          2 ^ (terminalRankBudget K L + 1) ≤
        2 ^ pairTau A hN pair *
          2 ^ (terminalRankBudget K L + 1) :=
      Nat.mul_le_mul_right _ hweight
    _ =
        2 ^
          (pairTau A hN pair +
            (terminalRankBudget K L + 1)) := by
      rw [← pow_add]
    _ ≤
        2 ^
          (L + 1 +
            canonicalCorrectedDefectCount
              A pair.1.1 pair.1.2 L) :=
      Nat.pow_le_pow_right (by norm_num) hexponent
    _ ≤ 2 ^ (L + 1 + 2) :=
      Nat.pow_le_pow_right (by norm_num)
        (Nat.add_le_add_left hD (L + 1))
    _ = 4 * 2 ^ (L + 1) := by
      rw [show L + 1 + 2 = 2 + (L + 1) by omega, pow_add]
      norm_num

/-- On the canonical terminal fibre, the residual weight is `2^τ-1`. -/
theorem residualWeight_eq_two_pow_sub_one_of_mem_rankTerminal
    {N M A L : ℕ} {hN : 2 ≤ N} {K : ℝ}
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈ boundedRankTerminalPairs N M A L hN K) :
    residualWeight A hN pair =
      2 ^ pairTau A hN pair - 1 := by
  have hdata := mem_boundedRankTerminalPairs.mp hpair
  unfold boundedTerminalCoreConditions at hdata
  have hsigma :=
    pairSigma_eq_zero_of_isCanonicallyNonaligned
      hdata.1.2.2.2.1
  simp [residualWeight, hsigma]

/--
Finite Step 4 of Lemma 17.30:
terminal mass is at most `#T_K * (4 * 2^B)`.
-/
theorem boundedRankTerminalResidualMass_le_card_mul_weight
    {N M A L : ℕ} (hN : 2 ≤ N) (K : ℝ) :
    boundedRankTerminalResidualMass N M A L hN K ≤
      (boundedRankTerminalPairs N M A L hN K).card *
        (4 * 2 ^ (L + 1)) := by
  unfold boundedRankTerminalResidualMass
  apply Finset.sum_le_card_nsmul
  intro pair hpair
  rw [residualWeight_eq_two_pow_sub_one_of_mem_rankTerminal
    hpair]
  exact
    TerminalClosureCounting.two_pow_sub_one_le_four_mul_two_pow
      (pairTau_le_runLength_add_two_of_mem_rankTerminal hpair)

/-- Exact disintegration of `T_K` over its first coordinate. -/
theorem card_boundedRankTerminalPairs_eq_sum_partnerFibers
    {N M A L : ℕ} (hN : 2 ≤ N) (K : ℝ) :
    (boundedRankTerminalPairs N M A L hN K).card =
      ∑ x ∈ boundedRankTerminalFirstStarts N M A L hN K,
        ((boundedRankTerminalPairs N M A L hN K).filter
          fun pair ↦ pair.1.1 = x).card := by
  let population :=
    boundedRankTerminalPairs N M A L hN K
  let first : SeparatedBoundedRatioPair N M L → ℕ :=
    fun pair ↦ pair.1.1
  have hcard :=
    Finset.card_eq_sum_card_image first population
  simpa [population, first,
    boundedRankTerminalFirstStarts] using hcard

/-- A uniform partner-fibre bound controls the whole terminal population. -/
theorem card_boundedRankTerminalPairs_le_firstStarts_mul
    {N M A L : ℕ} (hN : 2 ≤ N) (K : ℝ) (Q : ℕ)
    (hpartners :
      ∀ x ∈ boundedRankTerminalFirstStarts N M A L hN K,
        ((boundedRankTerminalPairs N M A L hN K).filter
          fun pair ↦ pair.1.1 = x).card ≤ Q) :
    (boundedRankTerminalPairs N M A L hN K).card ≤
      (boundedRankTerminalFirstStarts N M A L hN K).card * Q := by
  rw [card_boundedRankTerminalPairs_eq_sum_partnerFibers hN K]
  calc
    (∑ x ∈ boundedRankTerminalFirstStarts N M A L hN K,
      ((boundedRankTerminalPairs N M A L hN K).filter
        fun pair ↦ pair.1.1 = x).card) ≤
        ∑ _x ∈ boundedRankTerminalFirstStarts
          N M A L hN K, Q :=
      Finset.sum_le_sum hpartners
    _ =
        (boundedRankTerminalFirstStarts
          N M A L hN K).card * Q := by
      simp

/-- Separate first-start and partner bounds imply a product bound. -/
theorem card_boundedRankTerminalPairs_le
    {N M A L : ℕ} (hN : 2 ≤ N) (K : ℝ)
    (firstBound partnerBound : ℕ)
    (hfirst :
      (boundedRankTerminalFirstStarts
          N M A L hN K).card ≤ firstBound)
    (hpartners :
      ∀ x ∈ boundedRankTerminalFirstStarts N M A L hN K,
        ((boundedRankTerminalPairs N M A L hN K).filter
          fun pair ↦ pair.1.1 = x).card ≤ partnerBound) :
    (boundedRankTerminalPairs N M A L hN K).card ≤
      firstBound * partnerBound := by
  exact
    (card_boundedRankTerminalPairs_le_firstStarts_mul
      hN K partnerBound hpartners).trans
      (Nat.mul_le_mul_right partnerBound hfirst)

/-- The literal terminal mass is exactly the public seventh-sector mass. -/
theorem boundedRankTerminalResidualMass_eq_sectorResidualMassNat
    {N M A L : ℕ} (hN : 2 ≤ N) (K : ℝ) :
    boundedRankTerminalResidualMass N M A L hN K =
      sectorResidualMassNat
        (M := M) (L := L) A hN
        (boundedRankTerminalPredicate A K) .terminal := by
  unfold boundedRankTerminalResidualMass sectorResidualMassNat
  rw [boundedRatioSectorPairs_terminal_eq_rankTerminalPairs]

/-! ## The automatic isolated-component conclusion -/

/-- Canonical residual components with exactly two vertices. -/
noncomputable def boundedCanonicalPairComponents
    {N M L : ℕ} (A : ℕ)
    (pair : SeparatedBoundedRatioPair N M L) :
    Finset
      (largePrimeGraph pair.1.1 pair.1.2 L).ConnectedComponent :=
  pairComponents
    (canonicalResidualComponents A pair.1.1 pair.1.2 L)
    (fun C ↦ Fintype.card C.supp)

/-- Canonical residual components with at least three vertices. -/
noncomputable def boundedCanonicalLargeComponents
    {N M L : ℕ} (A : ℕ)
    (pair : SeparatedBoundedRatioPair N M L) :
    Finset
      (largePrimeGraph pair.1.1 pair.1.2 L).ConnectedComponent :=
  largeComponents
    (canonicalResidualComponents A pair.1.1 pair.1.2 L)
    (fun C ↦ Fintype.card C.supp)

/-- The canonical residual family has cardinality `B-s=c#`. -/
theorem card_canonicalResidualComponents_eq_runLength_sub_slack
    {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) :
    (canonicalResidualComponents
        A pair.1.1 pair.1.2 L).card =
      L + 1 - boundedTerminalSlack A pair := by
  have hxy := pair_coordinates_two_le hN pair
  rw [card_canonicalResidualComponents hxy.1 hxy.2]
  unfold boundedTerminalSlack
  have hle :=
    canonicalResidualComponentCount_le_runLength
      (A := A) hN pair
  omega

/--
Proposition 9.11's terminal component count on a bounded-ratio pair:
at most `2s` large components and at least `B-3s` isolated components of
size two.
-/
theorem bounded_terminal_component_count
    {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) :
    (boundedCanonicalLargeComponents A pair).card ≤
        2 * boundedTerminalSlack A pair ∧
      L + 1 - 3 * boundedTerminalSlack A pair ≤
        (boundedCanonicalPairComponents A pair).card := by
  classical
  let family :=
    canonicalResidualComponents
      A pair.1.1 pair.1.2 L
  let size :
      (largePrimeGraph pair.1.1 pair.1.2 L).ConnectedComponent →
        ℕ :=
    fun C ↦ Fintype.card C.supp
  have hcard :
      family.card =
        L + 1 - boundedTerminalSlack A pair :=
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
      (s := boundedTerminalSlack A pair)
      (components := family)
      (size := size)
      (Nat.sub_le (L + 1)
        (canonicalResidualComponentCount
          A pair.1.1 pair.1.2 L))
      hcard hsize hmass
  simpa [boundedCanonicalLargeComponents,
    boundedCanonicalPairComponents, family, size] using hcount

end

end BoundedRatioCanonicalTerminalPopulation
end PaperC
