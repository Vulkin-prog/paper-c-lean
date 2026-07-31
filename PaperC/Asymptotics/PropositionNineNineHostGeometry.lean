import PaperC.Combinatorics.DeepCoreSmallComponent
import PaperC.Combinatorics.DefectiveVertexIntervalBound
import PaperC.Combinatorics.SectionSevenPartition

set_option maxHeartbeats 1800000

/-!
# Concrete host geometry for Proposition 9.9

This module connects the literal finite population left by Section 7 to the
two structural inputs used in the proof of Proposition 9.9.

* Since `D# ≥ 3` and `D#` is bounded by the two interval defect counts, one
  of the two blocks contains at least two concrete defective values.
* More generally, a rational density

  `alphaNum * (L + 1) ≤ alphaDen * c#`

  supplies a component of size at most `K` whenever

  `2 * alphaDen < alphaNum * (K + 1)`.

  The literal deep-core inequality is

  `3 * (L + 1) < 16 * c#`,

  so the canonical residual family contains a nontrivial component with at
  most ten vertices.  The integer `10` is the first cutoff for which
  `2 * 16 < 3 * (10 + 1)`.

These are exact finite reductions.  They do not perform the remaining
Diophantine summation over the two-defect start, the component offsets and
its squarefree coefficient.
-/

namespace PaperC
namespace PropositionNineNineHostGeometry

open Affine
open CanonicalResidualComponents
open DefectiveVertexIntervalBound
open LargePrimeGraph
open LargePrimeGraphResolution
open LargePrimeOccurrences
open ResidualComponentCounts
open ResidualMasses
open SectionSevenPartition

noncomputable section

noncomputable local instance instDecidableLargePrimeAdj
    (x y L : ℕ) :
    DecidableRel (largePrimeGraph x y L).Adj :=
  Classical.decRel _

/-! ## The block carrying two defects -/

/--
If the corrected defect count is at least three, one of the two concrete
complete-boundary intervals contains at least two defective values.
-/
theorem two_le_one_defectInterval_of_three_le_corrected
    (A : ℕ) {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hD :
      3 ≤ canonicalCorrectedDefectCount A x y L) :
    2 ≤
        (IntervalDefectBound.defectsInInterval
          (L + 1) (x - 1)).card ∨
      2 ≤
        (IntervalDefectBound.defectsInInterval
          (L + 1) (y - 1)).card := by
  have hsum :=
    canonicalCorrectedDefectCount_le_interval_sum
      (L := L) A hx hy
  omega

/-! ## The bounded canonical residual component -/

/--
An elementary transfer from the literal strict `3/16` density to every
weaker rational density.  The cross-multiplication condition says
`alphaNum / alphaDen ≤ 3 / 16`, without introducing rational numbers.
-/
theorem rational_density_of_three_sixteenths
    {B c alphaNum alphaDen : ℕ}
    (hden : 0 < alphaDen)
    (hdensity : 3 * B < 16 * c)
    (hratio : 16 * alphaNum ≤ 3 * alphaDen) :
    alphaNum * B ≤ alphaDen * c := by
  have hleft :
      16 * (alphaNum * B) ≤ alphaDen * (3 * B) := by
    calc
      16 * (alphaNum * B) = (16 * alphaNum) * B := by
        ring
      _ ≤ (3 * alphaDen) * B :=
        Nat.mul_le_mul_right B hratio
      _ = alphaDen * (3 * B) := by
        ring
  have hright :
      alphaDen * (3 * B) < 16 * (alphaDen * c) := by
    calc
      alphaDen * (3 * B) < alphaDen * (16 * c) :=
        (Nat.mul_lt_mul_left hden).2 hdensity
      _ = 16 * (alphaDen * c) := by
        ring
  have hscaled :
      16 * (alphaNum * B) < 16 * (alphaDen * c) :=
    hleft.trans_lt hright
  exact
    ((Nat.mul_lt_mul_left (by norm_num : 0 < 16)).mp
      hscaled).le

/--
Exact rational-density extraction for the canonical residual family.
This is the parameterized finite core behind the `3/16`, cutoff-`10`
instance used in Proposition 9.9.
-/
theorem exists_canonicalResidualComponent_support_le_of_rational_density
    {N A L alphaNum alphaDen K : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedDyadicPair N L)
    (hden : 0 < alphaDen)
    (hdensity :
      alphaNum * (L + 1) ≤
        alphaDen * canonicalResidualComponentCount
          A pair.1.1 pair.1.2 L)
    (hcutoff :
      2 * alphaDen < alphaNum * (K + 1)) :
    ∃ C ∈
        canonicalResidualComponents
          A pair.1.1 pair.1.2 L,
      2 ≤ Fintype.card C.supp ∧
        Fintype.card C.supp ≤ K := by
  classical
  have hcoords := pair_coordinates_two_le hN pair
  have hcard :
      (canonicalResidualComponents
          A pair.1.1 pair.1.2 L).card =
        canonicalResidualComponentCount
          A pair.1.1 pair.1.2 L :=
    card_canonicalResidualComponents hcoords.1 hcoords.2
  have hdensityFamily :
      alphaNum * (L + 1) ≤
        alphaDen *
          (canonicalResidualComponents
            A pair.1.1 pair.1.2 L).card := by
    rw [hcard]
    exact hdensity
  have hambient :
      Fintype.card (Occurrence L) ≤ 2 * (L + 1) := by
    rw [card_occurrence]
  apply
    PaperC.DeepCoreSmallComponent.exists_bounded_connectedComponent_of_rational_density
      (largePrimeGraph pair.1.1 pair.1.2 L)
      (canonicalResidualComponents
        A pair.1.1 pair.1.2 L)
      (B := L + 1) (alphaNum := alphaNum)
      (alphaDen := alphaDen) (K := K)
      (Nat.succ_pos L) hden hambient
  · intro C hC
    exact
      (isNontrivialUnpinnedComponent_of_mem_canonicalResidualComponents
        hC).2
  · exact hdensityFamily
  · exact hcutoff

/--
The strict `3/16` deep-core test implies every weaker rational density and
therefore any cutoff satisfying the exact integer inequality.
-/
theorem exists_canonicalResidualComponent_support_le_of_deepCore_rational_density
    {N A L alphaNum alphaDen K : ℕ} (hN : 2 ≤ N)
    {pair : SeparatedDyadicPair N L}
    (hpair : pair ∈ deepCorePairs N A L hN)
    (hden : 0 < alphaDen)
    (hratio : 16 * alphaNum ≤ 3 * alphaDen)
    (hcutoff :
      2 * alphaDen < alphaNum * (K + 1)) :
    ∃ C ∈
        canonicalResidualComponents
          A pair.1.1 pair.1.2 L,
      2 ≤ Fintype.card C.supp ∧
        Fintype.card C.supp ≤ K := by
  apply
    exists_canonicalResidualComponent_support_le_of_rational_density
      hN pair hden
  · exact
      rational_density_of_three_sixteenths
        hden (mem_deepCorePairs.mp hpair).2.2 hratio
  · exact hcutoff

/--
The strict deep-core density forces a canonical residual component with
between two and ten vertices.  This is the literal `3/16` corollary of the
parameterized rational-density theorem.
-/
theorem exists_canonicalResidualComponent_support_le_ten_of_deepCore
    {N A L : ℕ} (hN : 2 ≤ N)
    {pair : SeparatedDyadicPair N L}
    (hpair : pair ∈ deepCorePairs N A L hN) :
    ∃ C ∈
        canonicalResidualComponents
          A pair.1.1 pair.1.2 L,
      2 ≤ Fintype.card C.supp ∧
        Fintype.card C.supp ≤ 10 := by
  exact
    exists_canonicalResidualComponent_support_le_of_deepCore_rational_density
      (alphaNum := 3) (alphaDen := 16) (K := 10)
      hN hpair (by omega) (by omega) (by omega)

/--
The two structural certificates from an explicitly supplied rational
density: a heavy defect interval and a bounded canonical residual
component.
-/
theorem defectInterval_and_boundedComponent_of_rational_density
    {N A L alphaNum alphaDen K : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedDyadicPair N L)
    (hD :
      3 ≤ canonicalCorrectedDefectCount
        A pair.1.1 pair.1.2 L)
    (hden : 0 < alphaDen)
    (hdensity :
      alphaNum * (L + 1) ≤
        alphaDen * canonicalResidualComponentCount
          A pair.1.1 pair.1.2 L)
    (hcutoff :
      2 * alphaDen < alphaNum * (K + 1)) :
    (2 ≤
          (IntervalDefectBound.defectsInInterval
            (L + 1) (pair.1.1 - 1)).card ∨
        2 ≤
          (IntervalDefectBound.defectsInInterval
            (L + 1) (pair.1.2 - 1)).card) ∧
      ∃ C ∈
          canonicalResidualComponents
            A pair.1.1 pair.1.2 L,
        2 ≤ Fintype.card C.supp ∧
          Fintype.card C.supp ≤ K := by
  have hcoords := pair_coordinates_two_le hN pair
  exact
    ⟨two_le_one_defectInterval_of_three_le_corrected
        A (by omega) (by omega) hD,
      exists_canonicalResidualComponent_support_le_of_rational_density
        hN pair hden hdensity hcutoff⟩

/--
The two structural certificates at an arbitrary rational cutoff.  Here the
density parameters may be any fraction no stronger than the literal `3/16`
deep-core threshold.
-/
theorem defectInterval_and_boundedComponent_of_deepCore_rational_density
    {N A L alphaNum alphaDen K : ℕ} (hN : 2 ≤ N)
    {pair : SeparatedDyadicPair N L}
    (hdeep : pair ∈ deepCorePairs N A L hN)
    (hD :
      3 ≤ canonicalCorrectedDefectCount
        A pair.1.1 pair.1.2 L)
    (hden : 0 < alphaDen)
    (hratio : 16 * alphaNum ≤ 3 * alphaDen)
    (hcutoff :
      2 * alphaDen < alphaNum * (K + 1)) :
    (2 ≤
          (IntervalDefectBound.defectsInInterval
            (L + 1) (pair.1.1 - 1)).card ∨
        2 ≤
          (IntervalDefectBound.defectsInInterval
            (L + 1) (pair.1.2 - 1)).card) ∧
      ∃ C ∈
          canonicalResidualComponents
            A pair.1.1 pair.1.2 L,
        2 ≤ Fintype.card C.supp ∧
          Fintype.card C.supp ≤ K := by
  exact
    defectInterval_and_boundedComponent_of_rational_density
      hN pair hD hden
      (rational_density_of_three_sixteenths
        hden (mem_deepCorePairs.mp hdeep).2.2 hratio)
      hcutoff

/--
The two exact structural alternatives attached to a member of the
Proposition 9.9 population.  This preserves the manuscript's `3/16`,
cutoff-`10` interface as a corollary of the rational theorem.
-/
theorem defectInterval_and_boundedComponent_of_deepCore
    {N A L : ℕ} (hN : 2 ≤ N)
    {pair : SeparatedDyadicPair N L}
    (hdeep : pair ∈ deepCorePairs N A L hN)
    (hD :
      3 ≤ canonicalCorrectedDefectCount
        A pair.1.1 pair.1.2 L) :
    (2 ≤
          (IntervalDefectBound.defectsInInterval
            (L + 1) (pair.1.1 - 1)).card ∨
        2 ≤
          (IntervalDefectBound.defectsInInterval
            (L + 1) (pair.1.2 - 1)).card) ∧
      ∃ C ∈
          canonicalResidualComponents
            A pair.1.1 pair.1.2 L,
        2 ≤ Fintype.card C.supp ∧
          Fintype.card C.supp ≤ 10 := by
  exact
    defectInterval_and_boundedComponent_of_deepCore_rational_density
      (alphaNum := 3) (alphaDen := 16) (K := 10)
      hN hdeep hD (by omega) (by omega) (by omega)

end

end PropositionNineNineHostGeometry
end PaperC
