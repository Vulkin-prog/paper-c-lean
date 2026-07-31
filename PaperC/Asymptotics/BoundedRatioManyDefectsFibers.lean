import PaperC.Asymptotics.BoundedRatioManyDefectsReduction
import PaperC.Asymptotics.BoundedRatioTwoDefectStarts
import PaperC.Asymptotics.BoundedRatioDistinctKernelTwoDefects
import PaperC.Asymptotics.BoundedRatioComponentHosts
import PaperC.Asymptotics.LogLogRunWindow

set_option maxHeartbeats 3600000

/-!
# Literal fibres for the bounded-ratio many-defects sector

This module connects the three finite reductions used around Lemma 17.26.
For an active fifth-sector pair, one of the two start windows contains two
defective values and the dense canonical core contains a component on at
most ten occurrences.  The two defective values have either equal or
distinct canonical squarefree kernels.  Hence each oriented active host
belongs to a finite fibre indexed by

* one actual two-defect base;
* one bounded left/right offset shape.

In the genuine high zone the equal-kernel base set is empty, so the base
index is exactly the distinct-kernel population already bounded by
generalized Pell in `BoundedRatioDistinctKernelTwoDefects`.

The final finite inequalities isolate the remaining invariant strictly more
finely than the former global host envelope: it is enough to bound a fibre
with one defective coordinate and one component shape fixed.  No new bridge
or opaque arithmetic statement is introduced here.
-/

namespace PaperC
namespace BoundedRatioManyDefectsFibers

open Affine
open BoundedRatioComponentHosts
open BoundedRatioDistinctKernelTwoDefects
open BoundedRatioManyDefectsReduction
open BoundedRatioTwoDefectStarts
open BoundedRatioResidualMasses
open CanonicalResidualComponents
open ComponentNormalization
open DefectCounting
open DefectivePredicate
open PropositionSixteenOne

noncomputable section

/-! ## The exact two-defect base cover -/

/-- Equal- and distinct-kernel actual two-defect bases, before the high-zone
equal-kernel elimination. -/
def twoDefectBaseCover
    (N M B : ℕ) : Finset ℕ :=
  equalKernelDefectBases N M B ∪
    distinctKernelDefectBases N M B

@[simp]
theorem mem_twoDefectBaseCover
    {N M B base : ℕ} :
    base ∈ twoDefectBaseCover N M B ↔
      base ∈ equalKernelDefectBases N M B ∨
        base ∈ distinctKernelDefectBases N M B := by
  simp [twoDefectBaseCover]

private theorem hDefective_of_mem_defectsInInterval
    {B U n : ℕ}
    (hn : n ∈ IntervalDefectBound.defectsInInterval B U) :
    HDefective B n := by
  have hvalue :=
    (IntervalDefectBound.mem_defectsInInterval.mp hn).1
  obtain ⟨_hnBound, support, hsupport, a, _ha, hrep⟩ :=
    DefectCounting.mem_defectValues_iff.mp hvalue
  let rep : HDefectRepresentation B n :=
    { support := support
      support_subset := hsupport
      squarePart := a
      value_eq := hrep }
  exact hDefective_of_HDefectRepresentation rep

/--
Two concrete defective values in the inclusive window
`[x-1,x-1+B]` place the shifted start `x-1` in the literal equal/distinct
kernel base cover.
-/
theorem shiftedBase_mem_twoDefectBaseCover_of_two_defects
    {N M B x : ℕ}
    (hxN : N ≤ x) (hxM : x < M) (hxpos : 1 ≤ x)
    (htwo :
      2 ≤
        (IntervalDefectBound.defectsInInterval
          B (x - 1)).card) :
    x - 1 ∈ twoDefectBaseCover N M B := by
  classical
  have hone :
      1 <
        (IntervalDefectBound.defectsInInterval
          B (x - 1)).card := by
    omega
  obtain ⟨n₁, hn₁, n₂, hn₂, hnNe⟩ :=
    Finset.one_lt_card.mp hone
  have hn₁Data :=
    IntervalDefectBound.mem_defectsInInterval.mp hn₁
  have hn₂Data :=
    IntervalDefectBound.mem_defectsInInterval.mp hn₂
  let i₁ := n₁ - (x - 1)
  let i₂ := n₂ - (x - 1)
  have hi₁B : i₁ ≤ B := by
    dsimp only [i₁]
    omega
  have hi₂B : i₂ ≤ B := by
    dsimp only [i₂]
    omega
  have hi₁Mem : i₁ ∈ Finset.range (B + 1) := by
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact hi₁B
  have hi₂Mem : i₂ ∈ Finset.range (B + 1) := by
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact hi₂B
  have hn₁Eq : n₁ = (x - 1) + i₁ := by
    dsimp only [i₁]
    omega
  have hn₂Eq : n₂ = (x - 1) + i₂ := by
    dsimp only [i₂]
    omega
  have hiNe : i₁ ≠ i₂ := by
    intro h
    apply hnNe
    omega
  have hdef₁ : HDefective B ((x - 1) + i₁) := by
    rw [← hn₁Eq]
    exact hDefective_of_mem_defectsInInterval hn₁
  have hdef₂ : HDefective B ((x - 1) + i₂) := by
    rw [← hn₂Eq]
    exact hDefective_of_mem_defectsInInterval hn₂
  have hbaseM : x - 1 < M := by omega
  have hbaseN : N ≤ x - 1 + 1 := by omega
  rw [mem_twoDefectBaseCover]
  by_cases hkernel :
      squarefreeKernel ((x - 1) + i₁) =
        squarefreeKernel ((x - 1) + i₂)
  · left
    rw [mem_equalKernelDefectBases]
    exact
      ⟨hbaseM, hbaseN, i₁, hi₁Mem, i₂, hi₂Mem,
        hiNe, hdef₁, hdef₂, hkernel⟩
  · right
    rw [mem_distinctKernelDefectBases]
    exact
      ⟨hbaseM, hbaseN, i₁, hi₁Mem, i₂, hi₂Mem,
        hiNe, hdef₁, hdef₂, hkernel⟩

/-- The equal-kernel part disappears in the genuine high zone. -/
theorem twoDefectBaseCover_eq_distinctKernel
    {N M B : ℕ}
    (hhigh : B ^ 2 + 1 < N) :
    twoDefectBaseCover N M B =
      distinctKernelDefectBases N M B := by
  rw [twoDefectBaseCover,
    equalKernelDefectBases_eq_empty hhigh]
  simp

/-! ## Fixed-coordinate, fixed-shape component fibres -/

/--
Bounded-component hosts with their first shifted start and their component
offset shape fixed.
-/
noncomputable def leftBaseShapeFiber
    (N M A L K base : ℕ)
    (shape :
      Finset (Fin (L + 1)) × Finset (Fin (L + 1))) :
    Finset (SeparatedBoundedRatioPair N M L) :=
  (boundedComponentHostsOfShape
    N M A L K shape).filter fun pair =>
      pair.1.1 - 1 = base

/--
Bounded-component hosts with their second shifted start and their component
offset shape fixed.
-/
noncomputable def rightBaseShapeFiber
    (N M A L K base : ℕ)
    (shape :
      Finset (Fin (L + 1)) × Finset (Fin (L + 1))) :
    Finset (SeparatedBoundedRatioPair N M L) :=
  (boundedComponentHostsOfShape
    N M A L K shape).filter fun pair =>
      pair.1.2 - 1 = base

@[simp]
theorem mem_leftBaseShapeFiber
    {N M A L K base : ℕ}
    {shape :
      Finset (Fin (L + 1)) × Finset (Fin (L + 1))}
    {pair : SeparatedBoundedRatioPair N M L} :
    pair ∈ leftBaseShapeFiber
        N M A L K base shape ↔
      pair ∈ boundedComponentHostsOfShape
          N M A L K shape ∧
        pair.1.1 - 1 = base := by
  simp [leftBaseShapeFiber]

@[simp]
theorem mem_rightBaseShapeFiber
    {N M A L K base : ℕ}
    {shape :
      Finset (Fin (L + 1)) × Finset (Fin (L + 1))}
    {pair : SeparatedBoundedRatioPair N M L} :
    pair ∈ rightBaseShapeFiber
        N M A L K base shape ↔
      pair ∈ boundedComponentHostsOfShape
          N M A L K shape ∧
        pair.1.2 - 1 = base := by
  simp [rightBaseShapeFiber]

/--
Trivial benchmark for the remaining left fibre: fixing the first shifted
start leaves at most the interval width many choices for the second start.
The sought arithmetic estimate in Lemma 17.26 must improve this linear
benchmark to square-root scale.
-/
theorem card_leftBaseShapeFiber_le_width
    {N M A L K base : ℕ} (hN : 2 ≤ N)
    (shape :
      Finset (Fin (L + 1)) × Finset (Fin (L + 1))) :
    (leftBaseShapeFiber
        N M A L K base shape).card ≤ M - N := by
  classical
  let coordinate :
      SeparatedBoundedRatioPair N M L → ℕ :=
    fun pair => pair.1.2
  have hinjective :
      ∀ ⦃u⦄,
        u ∈ leftBaseShapeFiber
          N M A L K base shape →
      ∀ ⦃v⦄,
        v ∈ leftBaseShapeFiber
          N M A L K base shape →
        coordinate u = coordinate v → u = v := by
    intro u hu v hv huv
    have huBase : u.1.1 - 1 = base :=
      (mem_leftBaseShapeFiber.mp hu).2
    have hvBase : v.1.1 - 1 = base :=
      (mem_leftBaseShapeFiber.mp hv).2
    have huLower : N ≤ u.1.1 :=
      (BoundedRatioGeometry.mem_boundedRatioBlock.mp
        (mem_separatedBoundedRatioPairs.mp u.2).1).1
    have hvLower : N ≤ v.1.1 :=
      (BoundedRatioGeometry.mem_boundedRatioBlock.mp
        (mem_separatedBoundedRatioPairs.mp v.2).1).1
    apply Subtype.ext
    apply Prod.ext
    · omega
    · exact huv
  have hsubset :
      (leftBaseShapeFiber
        N M A L K base shape).image coordinate ⊆
        BoundedRatioGeometry.boundedRatioBlock N M := by
    intro y hy
    obtain ⟨pair, hpair, rfl⟩ :=
      Finset.mem_image.mp hy
    exact
      (mem_separatedBoundedRatioPairs.mp pair.2).2.1
  calc
    (leftBaseShapeFiber
        N M A L K base shape).card =
        ((leftBaseShapeFiber
          N M A L K base shape).image coordinate).card := by
      symm
      rw [Finset.card_image_iff]
      exact hinjective
    _ ≤ (BoundedRatioGeometry.boundedRatioBlock N M).card :=
      Finset.card_le_card hsubset
    _ = M - N :=
      BoundedRatioGeometry.card_boundedRatioBlock N M

/-- Symmetric linear benchmark when the second shifted start is fixed. -/
theorem card_rightBaseShapeFiber_le_width
    {N M A L K base : ℕ} (hN : 2 ≤ N)
    (shape :
      Finset (Fin (L + 1)) × Finset (Fin (L + 1))) :
    (rightBaseShapeFiber
        N M A L K base shape).card ≤ M - N := by
  classical
  let coordinate :
      SeparatedBoundedRatioPair N M L → ℕ :=
    fun pair => pair.1.1
  have hinjective :
      ∀ ⦃u⦄,
        u ∈ rightBaseShapeFiber
          N M A L K base shape →
      ∀ ⦃v⦄,
        v ∈ rightBaseShapeFiber
          N M A L K base shape →
        coordinate u = coordinate v → u = v := by
    intro u hu v hv huv
    have huBase : u.1.2 - 1 = base :=
      (mem_rightBaseShapeFiber.mp hu).2
    have hvBase : v.1.2 - 1 = base :=
      (mem_rightBaseShapeFiber.mp hv).2
    have huLower : N ≤ u.1.2 :=
      (BoundedRatioGeometry.mem_boundedRatioBlock.mp
        (mem_separatedBoundedRatioPairs.mp u.2).2.1).1
    have hvLower : N ≤ v.1.2 :=
      (BoundedRatioGeometry.mem_boundedRatioBlock.mp
        (mem_separatedBoundedRatioPairs.mp v.2).2.1).1
    apply Subtype.ext
    apply Prod.ext
    · exact huv
    · omega
  have hsubset :
      (rightBaseShapeFiber
        N M A L K base shape).image coordinate ⊆
        BoundedRatioGeometry.boundedRatioBlock N M := by
    intro x hx
    obtain ⟨pair, hpair, rfl⟩ :=
      Finset.mem_image.mp hx
    exact
      (mem_separatedBoundedRatioPairs.mp pair.2).1
  calc
    (rightBaseShapeFiber
        N M A L K base shape).card =
        ((rightBaseShapeFiber
          N M A L K base shape).image coordinate).card := by
      symm
      rw [Finset.card_image_iff]
      exact hinjective
    _ ≤ (BoundedRatioGeometry.boundedRatioBlock N M).card :=
      Finset.card_le_card hsubset
    _ = M - N :=
      BoundedRatioGeometry.card_boundedRatioBlock N M

private theorem active_mem_boundedComponentHostsTen
    {N M A L : ℕ} {hN : 2 ≤ N}
    {terminal : TerminalPredicateFamily}
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈ activeSectorPairs
        N M A L hN terminal .manyDefects) :
    pair ∈ boundedComponentHosts N M A L 10 := by
  obtain ⟨C, hC, _htwo, hten⟩ :=
    exists_bounded_component_of_mem_active hpair
  exact mem_boundedComponentHosts.mpr ⟨C, hC, hten⟩

/--
The literal left-oriented active population is covered by fibres indexed by
an actual two-defect base and a component shape on at most ten occurrences.
-/
theorem leftTwoDefectActiveHosts_subset_baseShapeFibers
    {N M A L : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily) :
    leftTwoDefectActiveHosts N M A L hN terminal ⊆
      (twoDefectBaseCover N M (L + 1)).biUnion fun base =>
        (boundedOffsetShapes L 10).biUnion fun shape =>
          leftBaseShapeFiber
            N M A L 10 base shape := by
  classical
  intro pair hpair
  have hpairData := mem_leftTwoDefectActiveHosts.mp hpair
  have hp :=
    mem_separatedBoundedRatioPairs.mp pair.2
  have hbase :
      pair.1.1 - 1 ∈
        twoDefectBaseCover N M (L + 1) :=
    shiftedBase_mem_twoDefectBaseCover_of_two_defects
      (BoundedRatioGeometry.mem_boundedRatioBlock.mp hp.1).1
      (BoundedRatioGeometry.mem_boundedRatioBlock.mp hp.1).2
      (by
        have := (pair_coordinates_two_le hN pair).1
        omega)
      hpairData.2
  have hbounded :
      pair ∈ boundedComponentHosts N M A L 10 :=
    active_mem_boundedComponentHostsTen hpairData.1
  have hshapeUnion :=
    boundedComponentHosts_subset_shapeUnion
      (N := N) (M := M) (A := A) (L := L) (K := 10)
      hN hbounded
  obtain ⟨shape, hshape, hpairShape⟩ :=
    Finset.mem_biUnion.mp hshapeUnion
  apply Finset.mem_biUnion.mpr
  refine ⟨pair.1.1 - 1, hbase, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨shape, hshape, ?_⟩
  exact mem_leftBaseShapeFiber.mpr
    ⟨hpairShape, rfl⟩

/--
The literal right-oriented active population has the symmetric fixed-base,
fixed-shape cover.
-/
theorem rightTwoDefectActiveHosts_subset_baseShapeFibers
    {N M A L : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily) :
    rightTwoDefectActiveHosts N M A L hN terminal ⊆
      (twoDefectBaseCover N M (L + 1)).biUnion fun base =>
        (boundedOffsetShapes L 10).biUnion fun shape =>
          rightBaseShapeFiber
            N M A L 10 base shape := by
  classical
  intro pair hpair
  have hpairData := mem_rightTwoDefectActiveHosts.mp hpair
  have hp :=
    mem_separatedBoundedRatioPairs.mp pair.2
  have hbase :
      pair.1.2 - 1 ∈
        twoDefectBaseCover N M (L + 1) :=
    shiftedBase_mem_twoDefectBaseCover_of_two_defects
      (BoundedRatioGeometry.mem_boundedRatioBlock.mp hp.2.1).1
      (BoundedRatioGeometry.mem_boundedRatioBlock.mp hp.2.1).2
      (by
        have := (pair_coordinates_two_le hN pair).2
        omega)
      hpairData.2
  have hbounded :
      pair ∈ boundedComponentHosts N M A L 10 :=
    active_mem_boundedComponentHostsTen hpairData.1
  have hshapeUnion :=
    boundedComponentHosts_subset_shapeUnion
      (N := N) (M := M) (A := A) (L := L) (K := 10)
      hN hbounded
  obtain ⟨shape, hshape, hpairShape⟩ :=
    Finset.mem_biUnion.mp hshapeUnion
  apply Finset.mem_biUnion.mpr
  refine ⟨pair.1.2 - 1, hbase, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨shape, hshape, ?_⟩
  exact mem_rightBaseShapeFiber.mpr
    ⟨hpairShape, rfl⟩

/-! ## Exact finite summation -/

/--
Fixed-base, fixed-shape fibre bounds sum to a bound for the literal left
oriented active hosts.
-/
theorem card_leftTwoDefectActiveHosts_le_of_baseShapeFibers
    {N M A L Q : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily)
    (hfiber :
      ∀ base ∈ twoDefectBaseCover N M (L + 1),
      ∀ shape ∈ boundedOffsetShapes L 10,
        (leftBaseShapeFiber
          N M A L 10 base shape).card ≤ Q) :
    (leftTwoDefectActiveHosts
        N M A L hN terminal).card ≤
      (twoDefectBaseCover N M (L + 1)).card *
        (boundedOffsetShapes L 10).card * Q := by
  classical
  calc
    (leftTwoDefectActiveHosts
        N M A L hN terminal).card ≤
        ((twoDefectBaseCover N M (L + 1)).biUnion fun base =>
          (boundedOffsetShapes L 10).biUnion fun shape =>
            leftBaseShapeFiber
              N M A L 10 base shape).card :=
      Finset.card_le_card
        (leftTwoDefectActiveHosts_subset_baseShapeFibers
          hN terminal)
    _ ≤
        ∑ base ∈ twoDefectBaseCover N M (L + 1),
          ((boundedOffsetShapes L 10).biUnion fun shape =>
            leftBaseShapeFiber
              N M A L 10 base shape).card :=
      Finset.card_biUnion_le
    _ ≤
        ∑ base ∈ twoDefectBaseCover N M (L + 1),
          ∑ shape ∈ boundedOffsetShapes L 10,
            (leftBaseShapeFiber
              N M A L 10 base shape).card := by
      apply Finset.sum_le_sum
      intro base hbase
      exact Finset.card_biUnion_le
    _ ≤
        ∑ _base ∈ twoDefectBaseCover N M (L + 1),
          ∑ _shape ∈ boundedOffsetShapes L 10, Q := by
      apply Finset.sum_le_sum
      intro base hbase
      exact Finset.sum_le_sum fun shape hshape =>
        hfiber base hbase shape hshape
    _ =
        (twoDefectBaseCover N M (L + 1)).card *
          (boundedOffsetShapes L 10).card * Q := by
      simp
      ring

/-- Symmetric finite summation for right-oriented active hosts. -/
theorem card_rightTwoDefectActiveHosts_le_of_baseShapeFibers
    {N M A L Q : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily)
    (hfiber :
      ∀ base ∈ twoDefectBaseCover N M (L + 1),
      ∀ shape ∈ boundedOffsetShapes L 10,
        (rightBaseShapeFiber
          N M A L 10 base shape).card ≤ Q) :
    (rightTwoDefectActiveHosts
        N M A L hN terminal).card ≤
      (twoDefectBaseCover N M (L + 1)).card *
        (boundedOffsetShapes L 10).card * Q := by
  classical
  calc
    (rightTwoDefectActiveHosts
        N M A L hN terminal).card ≤
        ((twoDefectBaseCover N M (L + 1)).biUnion fun base =>
          (boundedOffsetShapes L 10).biUnion fun shape =>
            rightBaseShapeFiber
              N M A L 10 base shape).card :=
      Finset.card_le_card
        (rightTwoDefectActiveHosts_subset_baseShapeFibers
          hN terminal)
    _ ≤
        ∑ base ∈ twoDefectBaseCover N M (L + 1),
          ((boundedOffsetShapes L 10).biUnion fun shape =>
            rightBaseShapeFiber
              N M A L 10 base shape).card :=
      Finset.card_biUnion_le
    _ ≤
        ∑ base ∈ twoDefectBaseCover N M (L + 1),
          ∑ shape ∈ boundedOffsetShapes L 10,
            (rightBaseShapeFiber
              N M A L 10 base shape).card := by
      apply Finset.sum_le_sum
      intro base hbase
      exact Finset.card_biUnion_le
    _ ≤
        ∑ _base ∈ twoDefectBaseCover N M (L + 1),
          ∑ _shape ∈ boundedOffsetShapes L 10, Q := by
      apply Finset.sum_le_sum
      intro base hbase
      exact Finset.sum_le_sum fun shape hshape =>
        hfiber base hbase shape hshape
    _ =
        (twoDefectBaseCover N M (L + 1)).card *
          (boundedOffsetShapes L 10).card * Q := by
      simp
      ring

/--
The exact remaining finite invariant for the oriented cover: it suffices to
bound every fixed defective-coordinate/fixed-shape fibre.
-/
theorem orientedHostCover_card_le_of_baseShapeFibers
    {N M A L Q : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily)
    (hleft :
      ∀ base ∈ twoDefectBaseCover N M (L + 1),
      ∀ shape ∈ boundedOffsetShapes L 10,
        (leftBaseShapeFiber
          N M A L 10 base shape).card ≤ Q)
    (hright :
      ∀ base ∈ twoDefectBaseCover N M (L + 1),
      ∀ shape ∈ boundedOffsetShapes L 10,
        (rightBaseShapeFiber
          N M A L 10 base shape).card ≤ Q) :
    (leftTwoDefectActiveHosts
        N M A L hN terminal).card +
      (rightTwoDefectActiveHosts
        N M A L hN terminal).card ≤
      2 *
        ((twoDefectBaseCover N M (L + 1)).card *
          (boundedOffsetShapes L 10).card * Q) := by
  have hleftBound :=
    card_leftTwoDefectActiveHosts_le_of_baseShapeFibers
      hN terminal hleft
  have hrightBound :=
    card_rightTwoDefectActiveHosts_le_of_baseShapeFibers
      hN terminal hright
  omega

/--
High-zone specialization: only distinct-kernel bases remain.  Combined with
`distinctKernelDefectBases_uniformSubpolynomial`, this leaves precisely the
fixed-coordinate/fixed-shape component fibre as the unsummed arithmetic
quantity in Lemma 17.26.
-/
theorem orientedHostCover_card_le_of_distinctBaseShapeFibers
    {N M A L Q : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily)
    (hhigh : (L + 1) ^ 2 + 1 < N)
    (hleft :
      ∀ base ∈ distinctKernelDefectBases N M (L + 1),
      ∀ shape ∈ boundedOffsetShapes L 10,
        (leftBaseShapeFiber
          N M A L 10 base shape).card ≤ Q)
    (hright :
      ∀ base ∈ distinctKernelDefectBases N M (L + 1),
      ∀ shape ∈ boundedOffsetShapes L 10,
        (rightBaseShapeFiber
          N M A L 10 base shape).card ≤ Q) :
    (leftTwoDefectActiveHosts
        N M A L hN terminal).card +
      (rightTwoDefectActiveHosts
        N M A L hN terminal).card ≤
      2 *
        ((distinctKernelDefectBases
            N M (L + 1)).card *
          (boundedOffsetShapes L 10).card * Q) := by
  have hcover :=
    twoDefectBaseCover_eq_distinctKernel
      (N := N) (M := M) hhigh
  rw [← hcover]
  apply orientedHostCover_card_le_of_baseShapeFibers
    hN terminal
  · simpa only [hcover] using hleft
  · simpa only [hcover] using hright

/--
Completely explicit polynomial shape overcount.  The arithmetic input is now
localized to a fibre with the defective coordinate and both finite offset
sets fixed.
-/
theorem orientedHostCover_card_le_explicit_of_distinctBaseShapeFibers
    {N M A L Q : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily)
    (hhigh : (L + 1) ^ 2 + 1 < N)
    (hleft :
      ∀ base ∈ distinctKernelDefectBases N M (L + 1),
      ∀ shape ∈ boundedOffsetShapes L 10,
        (leftBaseShapeFiber
          N M A L 10 base shape).card ≤ Q)
    (hright :
      ∀ base ∈ distinctKernelDefectBases N M (L + 1),
      ∀ shape ∈ boundedOffsetShapes L 10,
        (rightBaseShapeFiber
          N M A L 10 base shape).card ≤ Q) :
    (leftTwoDefectActiveHosts
        N M A L hN terminal).card +
      (rightTwoDefectActiveHosts
        N M A L hN terminal).card ≤
      2 *
        ((distinctKernelDefectBases
            N M (L + 1)).card *
          ((11 * (L + 1) ^ 10) ^ 2) * Q) := by
  have hfinite :=
    orientedHostCover_card_le_of_distinctBaseShapeFibers
      hN terminal hhigh hleft hright
  have hshapes :=
    card_boundedOffsetShapes_le L 10
  calc
    (leftTwoDefectActiveHosts
        N M A L hN terminal).card +
          (rightTwoDefectActiveHosts
            N M A L hN terminal).card ≤
        2 *
          ((distinctKernelDefectBases
              N M (L + 1)).card *
            (boundedOffsetShapes L 10).card * Q) :=
      hfinite
    _ ≤
        2 *
          ((distinctKernelDefectBases
              N M (L + 1)).card *
            ((11 * (L + 1) ^ 10) ^ 2) * Q) := by
      gcongr

/--
Unconditional high-zone benchmark obtained by inserting the trivial
interval-width fibre bound.  It is exact but one square-root factor too
large for Lemma 17.26, which pinpoints the quantitative gain still needed.
-/
theorem orientedHostCover_card_le_trivial_width
    {N M A L : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily)
    (hhigh : (L + 1) ^ 2 + 1 < N) :
    (leftTwoDefectActiveHosts
        N M A L hN terminal).card +
      (rightTwoDefectActiveHosts
        N M A L hN terminal).card ≤
      2 *
        ((distinctKernelDefectBases
            N M (L + 1)).card *
          ((11 * (L + 1) ^ 10) ^ 2) * (M - N)) := by
  apply
    orientedHostCover_card_le_explicit_of_distinctBaseShapeFibers
      hN terminal hhigh
  · intro base hbase shape hshape
    exact card_leftBaseShapeFiber_le_width hN shape
  · intro base hbase shape hshape
    exact card_rightBaseShapeFiber_le_width hN shape

/--
The same fixed-fibre invariant controls the literal active fifth-sector
population, with no intermediate asymptotic abstraction.
-/
theorem card_activeManyDefects_le_explicit_of_distinctBaseShapeFibers
    {N M A L Q : ℕ} (hN : 2 ≤ N)
    (terminal : TerminalPredicateFamily)
    (hhigh : (L + 1) ^ 2 + 1 < N)
    (hleft :
      ∀ base ∈ distinctKernelDefectBases N M (L + 1),
      ∀ shape ∈ boundedOffsetShapes L 10,
        (leftBaseShapeFiber
          N M A L 10 base shape).card ≤ Q)
    (hright :
      ∀ base ∈ distinctKernelDefectBases N M (L + 1),
      ∀ shape ∈ boundedOffsetShapes L 10,
        (rightBaseShapeFiber
          N M A L 10 base shape).card ≤ Q) :
    (activeSectorPairs
        N M A L hN terminal .manyDefects).card ≤
      2 *
        ((distinctKernelDefectBases
            N M (L + 1)).card *
          ((11 * (L + 1) ^ 10) ^ 2) * Q) := by
  exact
    (card_activeHosts_le_oriented_sum hN terminal).trans
      (orientedHostCover_card_le_explicit_of_distinctBaseShapeFibers
        hN terminal hhigh hleft hright)

/--
Finite mass form of the complete reduction.  Once the fixed
coordinate/shape fibres are bounded by `Q`, all other factors in the
fifth-sector mass are explicit.
-/
theorem sectorResidualMassNat_le_explicit_of_distinctBaseShapeFibers
    {κ₀ N M A L Q : ℕ} (hN : 2 ≤ N)
    (hMκ : M ≤ κ₀ * N)
    (terminal : TerminalPredicateFamily)
    (hhigh : (L + 1) ^ 2 + 1 < N)
    (hleft :
      ∀ base ∈ distinctKernelDefectBases N M (L + 1),
      ∀ shape ∈ boundedOffsetShapes L 10,
        (leftBaseShapeFiber
          N M A L 10 base shape).card ≤ Q)
    (hright :
      ∀ base ∈ distinctKernelDefectBases N M (L + 1),
      ∀ shape ∈ boundedOffsetShapes L 10,
        (rightBaseShapeFiber
          N M A L 10 base shape).card ≤ Q) :
    sectorResidualMassNat
        (M := M) (L := L) A hN terminal .manyDefects ≤
      (2 *
        ((distinctKernelDefectBases
            N M (L + 1)).card *
          ((11 * (L + 1) ^ 10) ^ 2) * Q)) *
        residualWeightEnvelopeNat κ₀ A N L := by
  have hmass :=
    sectorResidualMassNat_le_active_card_mul_envelope
      (κ₀ := κ₀) (M := M) (A := A) (L := L)
      hN hMκ terminal
  have hcard :=
    card_activeManyDefects_le_explicit_of_distinctBaseShapeFibers
      hN terminal hhigh hleft hright
  exact hmass.trans
    (Nat.mul_le_mul_right
      (residualWeightEnvelopeNat κ₀ A N L) hcard)

/-! ## Asymptotic closure from the localized fibre invariant -/

/-- Fixed positive powers preserve reciprocal-power subpolynomiality. -/
theorem uniformSubpolynomialOn_pow_fixed
    {admissible : ℕ → ℕ → Prop}
    {f : ℕ → ℕ → ℝ}
    (hf : UniformSubpolynomialOn admissible f)
    (d : ℕ) (hd : 0 < d) :
    UniformSubpolynomialOn admissible
      (fun N L => f N L ^ d) := by
  intro k hk
  have hdk : 0 < d * k :=
    Nat.mul_pos hd hk
  obtain ⟨N₀, hN₀⟩ := hf (d * k) hdk
  refine ⟨N₀, ?_⟩
  intro N hN L hNL
  simpa only [abs_pow, pow_mul] using
    hN₀ N hN L hNL

/-- Real version of the explicit component-shape overcount. -/
noncomputable def componentShapeEnvelope
    (_N L : ℕ) : ℝ :=
  (11 * (((L + 1 : ℕ) : ℝ)) ^ 10) ^ 2

/-- The finite shape overcount is uniformly subpolynomial. -/
theorem componentShapeEnvelope_uniformSubpolynomial
    {C : ℝ} (hC : 0 ≤ C) :
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      componentShapeEnvelope := by
  have hheight :=
    CriticalRationalMassEnvelopes.runLengthAddOne_uniformSubpolynomial
      hC
  have hheightTen :=
    uniformSubpolynomialOn_pow_fixed
      hheight 10 (by omega)
  have hscaled :=
    ExpSqrtLog.uniformSubpolynomialOn_const_mul
      11 hheightTen
  have hsquared :=
    uniformSubpolynomialOn_pow_fixed
      hscaled 2 (by omega)
  change
    UniformSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (fun _ L ↦ (11 * (((L + 1 : ℕ) : ℝ)) ^ 10) ^ 2)
  exact hsquared

/-- The literal run-length window eventually lies in the genuine high zone
needed to eliminate equal squarefree kernels. -/
theorem twoDefect_highZone_eventually
    {C : ℝ} (hC : 0 ≤ C) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L,
      CriticalRunWindow.InRunLengthWindow C N L →
        (L + 1) ^ 2 + 1 < N := by
  have hheight :=
    CriticalRationalMassEnvelopes.runLengthAddOne_uniformSubpolynomial
      hC
  obtain ⟨Ncube, hcube⟩ :=
    hheight 3 (by omega)
  obtain ⟨Nthree, hthree⟩ :=
    DependencyEdgesCritical.runLengthAddOne_tends_to_infinity
      hC 3
  refine ⟨max Ncube Nthree, ?_⟩
  intro N hN L hrun
  have hcubeBound :=
    hcube N ((le_max_left _ _).trans hN) L hrun
  have hBthree :
      3 ≤ L + 1 :=
    hthree N ((le_max_right _ _).trans hN) L hrun
  have hcubeNat :
      (L + 1) ^ 3 ≤ N := by
    have hnonneg :
        0 ≤ (((L + 1 : ℕ) : ℝ)) := by
      positivity
    rw [abs_of_nonneg hnonneg] at hcubeBound
    exact_mod_cast hcubeBound
  have hstrict :
      (L + 1) ^ 2 + 1 < (L + 1) ^ 3 := by
    nlinarith
  exact hstrict.trans_le hcubeNat

/--
Strong localized form of the remaining Lemma 17.26 invariant.

Assume one endpoint and one bounded component shape are fixed.  If every
such fibre is dominated by a common `N^(1/2+o)` natural-valued envelope,
then generalized Pell and the already proved two-defect summation close the
entire fifth-sector mass.  This premise is strictly narrower than the former
global oriented-host envelope.
-/
theorem manyDefectsSector_uniformLittleO_of_baseShapeFiberEnvelope
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ)
    (terminal : TerminalPredicateFamily)
    (hPell : PellInput.GeneralizedPellPolynomialBoxStatement)
    {fiberEnvelopeNat : ℕ → ℕ → ℕ}
    (hfiberRate :
      UniformHalfPowerSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L => (fiberEnvelopeNat N L : ℝ)))
    (hfiberDom :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ M L,
        2 * N ≤ M →
        M ≤ κ₀ * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        (∀ base ∈
            distinctKernelDefectBases N M (L + 1),
          ∀ shape ∈ boundedOffsetShapes L 10,
            (leftBaseShapeFiber
              N M A L 10 base shape).card ≤
                fiberEnvelopeNat N L) ∧
        (∀ base ∈
            distinctKernelDefectBases N M (L + 1),
          ∀ shape ∈ boundedOffsetShapes L 10,
            (rightBaseShapeFiber
              N M A L 10 base shape).card ≤
                fiberEnvelopeNat N L)) :
    UniformLittleOInBoundedRatioWindow C κ₀
      (sectorResidualMass A terminal .manyDefects) := by
  obtain ⟨c, hc, Nbase, hbase⟩ :=
    generalizedPell_implies_card_distinctKernelDefectBases_le_residual
      hC κ₀ hPell
  obtain ⟨Nfiber, hfiber⟩ := hfiberDom
  obtain ⟨Nhigh, hhigh⟩ :=
    twoDefect_highZone_eventually hC
  let subpolynomialFactor : ℕ → ℕ → ℝ :=
    fun N L =>
      2 *
        (distinctKernelTwoDefectResidual c N L *
          componentShapeEnvelope N L)
  let hostEnvelope : ℕ → ℕ → ℝ :=
    fun N L =>
      subpolynomialFactor N L *
        (fiberEnvelopeNat N L : ℝ)
  have hbaseRate :=
    distinctKernelTwoDefectResidual_uniformSubpolynomial
      hC hc
  have hshapeRate :=
    componentShapeEnvelope_uniformSubpolynomial hC
  have hfactorRate :
      UniformSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        subpolynomialFactor := by
    simpa only [subpolynomialFactor] using
      ExpSqrtLog.uniformSubpolynomialOn_const_mul 2
        (ExpSqrtLog.uniformSubpolynomialOn_mul
          hbaseRate hshapeRate)
  have hhostRate :
      UniformHalfPowerSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        hostEnvelope := by
    have hproduct :=
      UniformHalfPower.mul_subpolynomial
        hfiberRate hfactorRate
    simpa only [hostEnvelope, mul_comm] using hproduct
  have hhostNonneg :
      ∀ N L, 0 ≤ hostEnvelope N L := by
    intro N L
    dsimp only [hostEnvelope, subpolynomialFactor]
    unfold distinctKernelTwoDefectResidual
      smoothKernelChebyshevEnvelope
      PellInput.expLogLogBound
      componentShapeEnvelope
    positivity
  have hhostDom :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ M L,
        2 * N ≤ M →
        M ≤ κ₀ * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        orientedHostCoverCount A terminal N M L ≤
          hostEnvelope N L := by
    refine
      ⟨max Nbase (max Nfiber (max Nhigh 2)), ?_⟩
    intro N hN M L hNM hMκ hrun
    have hNbase :
        Nbase ≤ N :=
      (le_max_left _ _).trans hN
    have htail :
        max Nfiber (max Nhigh 2) ≤ N :=
      (le_max_right _ _).trans hN
    have hNfiber :
        Nfiber ≤ N :=
      (le_max_left _ _).trans htail
    have htail₂ :
        max Nhigh 2 ≤ N :=
      (le_max_right _ _).trans htail
    have hNhigh :
        Nhigh ≤ N :=
      (le_max_left _ _).trans htail₂
    have hNtwo :
        2 ≤ N :=
      (le_max_right _ _).trans htail₂
    have hbaseBound :=
      hbase N hNbase M L hNM hMκ hrun
    have hfibers :=
      hfiber N hNfiber M L hNM hMκ hrun
    have hfinite :=
      orientedHostCover_card_le_explicit_of_distinctBaseShapeFibers
        hNtwo terminal (hhigh N hNhigh L hrun)
        hfibers.1 hfibers.2
    have hfiniteReal :
        (((leftTwoDefectActiveHosts
              N M A L hNtwo terminal).card +
            (rightTwoDefectActiveHosts
              N M A L hNtwo terminal).card : ℕ) : ℝ) ≤
          ((2 *
            ((distinctKernelDefectBases
                N M (L + 1)).card *
              ((11 * (L + 1) ^ 10) ^ 2) *
              fiberEnvelopeNat N L) : ℕ) : ℝ) := by
      exact_mod_cast hfinite
    simp only [orientedHostCoverCount, dif_pos hNtwo]
    calc
      (((leftTwoDefectActiveHosts
            N M A L hNtwo terminal).card +
          (rightTwoDefectActiveHosts
            N M A L hNtwo terminal).card : ℕ) : ℝ) ≤
          ((2 *
            ((distinctKernelDefectBases
                N M (L + 1)).card *
              ((11 * (L + 1) ^ 10) ^ 2) *
              fiberEnvelopeNat N L) : ℕ) : ℝ) :=
        hfiniteReal
      _ =
          2 *
            (((distinctKernelDefectBases
                N M (L + 1)).card : ℝ) *
              componentShapeEnvelope N L) *
            (fiberEnvelopeNat N L : ℝ) := by
        unfold componentShapeEnvelope
        push_cast
        ring
      _ ≤
          2 *
            (distinctKernelTwoDefectResidual c N L *
              componentShapeEnvelope N L) *
            (fiberEnvelopeNat N L : ℝ) := by
        gcongr
        unfold componentShapeEnvelope
        positivity
      _ = hostEnvelope N L := by
        rfl
  exact
    manyDefectsSector_uniformLittleO_of_orientedHostEnvelope
      hC κ₀ A terminal hhostRate hhostNonneg hhostDom

/--
Interface wrapper for Lemma 17.26.  Evertse--Silverman remains an antecedent
of the historical public statement but is not needed by this sharper
two-defect-base reduction; generalized Pell controls the distinct-kernel
base population.
-/
theorem manyDefectsSectorStability_of_baseShapeFiberEnvelope
    {C : ℝ} (hC : 0 ≤ C) (κ₀ A : ℕ)
    (terminal : TerminalPredicateFamily)
    {fiberEnvelopeNat : ℕ → ℕ → ℕ}
    (hfiberRate :
      UniformHalfPowerSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun N L => (fiberEnvelopeNat N L : ℝ)))
    (hfiberDom :
      ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ M L,
        2 * N ≤ M →
        M ≤ κ₀ * N →
        CriticalRunWindow.InRunLengthWindow C N L →
        (∀ base ∈
            distinctKernelDefectBases N M (L + 1),
          ∀ shape ∈ boundedOffsetShapes L 10,
            (leftBaseShapeFiber
              N M A L 10 base shape).card ≤
                fiberEnvelopeNat N L) ∧
        (∀ base ∈
            distinctKernelDefectBases N M (L + 1),
          ∀ shape ∈ boundedOffsetShapes L 10,
            (rightBaseShapeFiber
              N M A L 10 base shape).card ≤
                fiberEnvelopeNat N L)) :
    ManyDefectsSectorStabilityStatement
      C κ₀ A terminal := by
  intro _hES hPell
  exact
    manyDefectsSector_uniformLittleO_of_baseShapeFiberEnvelope
      hC κ₀ A terminal hPell hfiberRate hfiberDom

end

end BoundedRatioManyDefectsFibers
end PaperC
