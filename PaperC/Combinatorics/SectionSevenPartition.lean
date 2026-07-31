import PaperC.Combinatorics.ShallowCorePairs

set_option maxHeartbeats 1800000

/-!
# Exact partition after Proposition 7.5

The first three propositions of Section 7 remove, in order,

1. the branch `P# ≤ N`;
2. the branch `N < P#` with a canonical height at most
   `sqrt(log(L+1))`;
3. the remaining branch with `16*c# ≤ 3(L+1)`.

This file defines the literal complement and proves that these four finite
populations cover every separated ordered pair.  A member of the complement
therefore has `N < P#`, is either non-aligned or aligned above the
square-root logarithmic height, and satisfies
`3(L+1) < 16*c#`.
-/

namespace PaperC
namespace SectionSevenPartition

open CanonicalResidualComponents
open RationalMassFinite
open ResidualComponentCounts
open ResidualMasses
open ShallowCorePairs
open SmallHeightLargeProductPairs

noncomputable section

/--
The exact population left after Propositions 7.3--7.5:

`N < P#`, outside the small-height sector, and
`3(L+1) < 16*c#`.
-/
noncomputable def deepCorePairs
    (N A L : ℕ) (hN : 2 ≤ N) :
    Finset (SeparatedDyadicPair N L) := by
  classical
  exact Finset.univ.filter fun pair ↦
    CanonicalResidualPrimeProductExceeds
        (A := A) (L := L)
        (show 1 ≤ pair.1.1 by
          exact le_trans (by omega : 1 ≤ 2)
            (pair_coordinates_two_le hN pair).1)
        (show 1 ≤ pair.1.2 by
          exact le_trans (by omega : 1 ≤ 2)
            (pair_coordinates_two_le hN pair).2)
        N ∧
      ¬ HasSmallCanonicalHeight A L pair.1.1 pair.1.2 ∧
      3 * (L + 1) <
        16 * canonicalResidualComponentCount
          A pair.1.1 pair.1.2 L

@[simp]
theorem mem_deepCorePairs
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L} :
    pair ∈ deepCorePairs N A L hN ↔
      CanonicalResidualPrimeProductExceeds
          (A := A) (L := L)
          (show 1 ≤ pair.1.1 by
            exact le_trans (by omega : 1 ≤ 2)
              (pair_coordinates_two_le hN pair).1)
          (show 1 ≤ pair.1.2 by
            exact le_trans (by omega : 1 ≤ 2)
              (pair_coordinates_two_le hN pair).2)
          N ∧
        ¬ HasSmallCanonicalHeight A L pair.1.1 pair.1.2 ∧
        3 * (L + 1) <
          16 * canonicalResidualComponentCount
            A pair.1.1 pair.1.2 L := by
  simp [deepCorePairs]

/--
The four Section 7 populations cover exactly all separated ordered pairs.
The union is written in the chronological order of Propositions 7.3, 7.4,
7.5 and the remaining deep-core sector.
-/
theorem sectionSeven_populations_cover
    {N A L : ℕ} (hN : 2 ≤ N) :
    ((smallProductPairs N A L hN ∪
        smallHeightLargeProductPairs N A L hN) ∪
        shallowCorePairs N A L hN) ∪
        deepCorePairs N A L hN =
      Finset.univ := by
  ext pair
  simp only [Finset.mem_union, Finset.mem_univ, iff_true]
  let hx : 1 ≤ pair.1.1 :=
    le_trans (by omega : 1 ≤ 2)
      (pair_coordinates_two_le hN pair).1
  let hy : 1 ≤ pair.1.2 :=
    le_trans (by omega : 1 ≤ 2)
      (pair_coordinates_two_le hN pair).2
  by_cases hproduct :
      CanonicalResidualPrimeProductAtMost
        (A := A) (L := L) hx hy N
  · exact Or.inl
      (Or.inl
        (Or.inl
          (mem_smallProductPairs.mpr hproduct)))
  · have hlarge :
        CanonicalResidualPrimeProductExceeds
          (A := A) (L := L) hx hy N := by
      exact
        (canonicalResidualPrimeProductExceeds_iff_not_atMost
          hx hy N).2 hproduct
    by_cases hheight :
        HasSmallCanonicalHeight A L pair.1.1 pair.1.2
    · exact Or.inl
        (Or.inl
          (Or.inr
            (mem_smallHeightLargeProductPairs.mpr
              ⟨hlarge, hheight⟩)))
    · by_cases hdensity :
        HasCoreDensityAtMostThreeSixteenths
          A L pair.1.1 pair.1.2
      · exact Or.inl
          (Or.inr
            (mem_shallowCorePairs.mpr
              ⟨hlarge, hheight, hdensity⟩))
      · right
        rw [mem_deepCorePairs]
        refine ⟨hlarge, hheight, ?_⟩
        unfold HasCoreDensityAtMostThreeSixteenths at hdensity
        omega

end

end SectionSevenPartition
end PaperC
