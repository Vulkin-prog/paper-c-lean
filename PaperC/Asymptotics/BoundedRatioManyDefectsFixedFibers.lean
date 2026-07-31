import PaperC.Asymptotics.BoundedRatioManyDefectsFibers
import PaperC.Arithmetic.SquarefreeSmoothCount

set_option maxHeartbeats 3600000

/-!
# Fixed square-class fibres in the bounded-ratio many-defects sector

The last input isolated in `BoundedRatioManyDefectsFibers` fixes one start
window and one component offset shape, but still leaves the squarefree
component coefficient implicit.  Lemma 17.26 sums that coefficient before
applying the one-sided count of Lemma 17.21.

This file performs that missing finite disintegration.  A fixed-base,
fixed-shape fibre is covered by squarefree `(L+1)`-smooth coefficients `d`
of explicitly bounded height.  Once `d` is fixed, the mobile start maps
injectively to the normalized shifted-product equation determined only by
the fixed base, the two offset sets and `d`.

The degree-one branch is then closed unconditionally by the existing
square-root count.  In degree two, the exceptional coefficient `e=1`
injects into the signed divisor pairs of the offset discriminant, while
`e ≥ 2` is sent directly to the registered generalized-Pell polynomial
box at an explicit quadratic height.  For degree at least three, the same
finite fibre is mapped to the existing Evertse--Silverman equation; no new
Diophantine statement is introduced.  On every nonempty degree-two fibre,
the three required polynomial-height inequalities are discharged
automatically.  The remaining uniform work is the subpolynomial summation
of the displayed divisor and Evertse--Silverman bounds, followed by the
degree-by-degree assembly.
-/

namespace PaperC
namespace BoundedRatioManyDefectsFixedFibers

open scoped BigOperators
open Affine
open BoundedRatioComponentHosts
open BoundedRatioComponentNormalization
open BoundedRatioDistinctKernelTwoDefects
open BoundedRatioManyDefectsFibers
open CanonicalResidualComponents
open ComponentNormalization
open DefectivePredicate
open EvertseSilvermanInput
open LargePrimeGraph
open PropositionSixteenOne
open SquarefreeSmoothCount

noncomputable section

noncomputable local instance instDecidableLargePrimeAdj
    (x y L : ℕ) :
    DecidableRel (largePrimeGraph x y L).Adj :=
  Classical.decRel _

/-! ## Products determined by a fixed offset shape -/

/-- Product in the block whose start is fixed. -/
def shapeLeftProduct
    {L : ℕ}
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (x : ℕ) : ℕ :=
  ∏ i ∈ shape.1, startCompleteVertexLabel x L i

/-- Product in the mobile block. -/
def shapeRightProduct
    {L : ℕ}
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (y : ℕ) : ℕ :=
  ∏ j ∈ shape.2, startCompleteVertexLabel y L j

/-- The canonical normalized coefficient after fixing the left start. -/
def leftNormalizedCoefficient
    {L : ℕ}
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (base d : ℕ) : ℕ :=
  squarefreeKernel (d * shapeLeftProduct shape (base + 1))

/-- The symmetric normalized coefficient after fixing the right start. -/
def rightNormalizedCoefficient
    {L : ℕ}
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (base d : ℕ) : ℕ :=
  squarefreeKernel (d * shapeRightProduct shape (base + 1))

theorem leftNormalizedCoefficient_pos
    {L : ℕ}
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (base d : ℕ) :
    0 < leftNormalizedCoefficient shape base d := by
  exact squarefreeKernel_pos _

theorem rightNormalizedCoefficient_pos
    {L : ℕ}
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (base d : ℕ) :
    0 < rightNormalizedCoefficient shape base d := by
  exact squarefreeKernel_pos _

/-! ## Fixed square-class subfibres -/

/--
A component of the specified shape carrying the specified squarefree
component coefficient.
-/
def CarriesShapeSquareClass
    {N M A L K : ℕ}
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (d : ℕ) (pair : SeparatedBoundedRatioPair N M L) : Prop :=
  0 < d ∧
    Squarefree d ∧
    (∀ p : ℕ, p.Prime → p ∣ d → p ≤ L + 1) ∧
    d ≤ boundedRatioCutoff M L ^ K ∧
    ∃ C ∈ canonicalResidualComponents
        A pair.1.1 pair.1.2 L,
      Fintype.card C.supp ≤ K ∧
      componentLeftOffsets pair.1.1 pair.1.2 L C = shape.1 ∧
      componentRightOffsets pair.1.1 pair.1.2 L C = shape.2 ∧
      ∃ z : ℕ, 0 < z ∧
        componentLeftProduct pair.1.1 pair.1.2 L C *
            componentRightProduct pair.1.1 pair.1.2 L C =
          d * z ^ 2

/-- Left-oriented fixed-base/fixed-shape fibre with `d` fixed. -/
noncomputable def leftFixedSquareClassFiber
    (N M A L K base : ℕ)
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (d : ℕ) :
    Finset (SeparatedBoundedRatioPair N M L) := by
  classical
  exact
    (leftBaseShapeFiber N M A L K base shape).filter
      (CarriesShapeSquareClass (N := N) (M := M) (A := A)
        (L := L) (K := K) shape d)

/-- Right-oriented fixed-base/fixed-shape fibre with `d` fixed. -/
noncomputable def rightFixedSquareClassFiber
    (N M A L K base : ℕ)
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (d : ℕ) :
    Finset (SeparatedBoundedRatioPair N M L) := by
  classical
  exact
    (rightBaseShapeFiber N M A L K base shape).filter
      (CarriesShapeSquareClass (N := N) (M := M) (A := A)
        (L := L) (K := K) shape d)

@[simp]
theorem mem_leftFixedSquareClassFiber
    {N M A L K base d : ℕ}
    {shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1))}
    {pair : SeparatedBoundedRatioPair N M L} :
    pair ∈ leftFixedSquareClassFiber
        N M A L K base shape d ↔
      pair ∈ leftBaseShapeFiber N M A L K base shape ∧
      CarriesShapeSquareClass
        (N := N) (M := M) (A := A) (L := L) (K := K)
        shape d pair := by
  simp [leftFixedSquareClassFiber]

@[simp]
theorem mem_rightFixedSquareClassFiber
    {N M A L K base d : ℕ}
    {shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1))}
    {pair : SeparatedBoundedRatioPair N M L} :
    pair ∈ rightFixedSquareClassFiber
        N M A L K base shape d ↔
      pair ∈ rightBaseShapeFiber N M A L K base shape ∧
      CarriesShapeSquareClass
        (N := N) (M := M) (A := A) (L := L) (K := K)
        shape d pair := by
  simp [rightFixedSquareClassFiber]

/-! ## Every shape fibre is covered by its smooth square classes -/

theorem leftBaseShapeFiber_subset_squareClassUnion
    {N M A L K base : ℕ} (hN : 2 ≤ N)
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1))) :
    leftBaseShapeFiber N M A L K base shape ⊆
      (squarefreeSmoothUpTo
        (L + 1) (boundedRatioCutoff M L ^ K)).biUnion fun d =>
          leftFixedSquareClassFiber
            N M A L K base shape d := by
  classical
  intro pair hpair
  rcases (mem_leftBaseShapeFiber.mp hpair).1 with
    hhost
  rcases (mem_boundedComponentHostsOfShape.mp hhost).2 with
    ⟨C, hC, hcard, hleft, hright⟩
  obtain ⟨d, z, _e, _v, hd, hdsq, hdsmooth, hz,
      _he, _hesq, _hv, hwhole, _hrightEq, _heCanonical,
      hdBound, _hleftBound, _hrightBound, _heBound⟩ :=
    exists_normalized_component_equation_with_height
      hN pair hC hcard
  have hdMem :
      d ∈ squarefreeSmoothUpTo
        (L + 1) (boundedRatioCutoff M L ^ K) := by
    rw [mem_squarefreeSmoothUpTo]
    refine ⟨hd, hdBound, hdsq, ?_⟩
    intro p hp
    exact hdsmooth p
      (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)
  apply Finset.mem_biUnion.mpr
  refine ⟨d, hdMem, ?_⟩
  rw [mem_leftFixedSquareClassFiber]
  refine ⟨hpair, hd, hdsq, hdsmooth, hdBound, ?_⟩
  exact ⟨C, hC, hcard, hleft, hright, z, hz, hwhole⟩

theorem rightBaseShapeFiber_subset_squareClassUnion
    {N M A L K base : ℕ} (hN : 2 ≤ N)
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1))) :
    rightBaseShapeFiber N M A L K base shape ⊆
      (squarefreeSmoothUpTo
        (L + 1) (boundedRatioCutoff M L ^ K)).biUnion fun d =>
          rightFixedSquareClassFiber
            N M A L K base shape d := by
  classical
  intro pair hpair
  rcases (mem_rightBaseShapeFiber.mp hpair).1 with
    hhost
  rcases (mem_boundedComponentHostsOfShape.mp hhost).2 with
    ⟨C, hC, hcard, hleft, hright⟩
  obtain ⟨d, z, _e, _v, hd, hdsq, hdsmooth, hz,
      _he, _hesq, _hv, hwhole, _hrightEq, _heCanonical,
      hdBound, _hleftBound, _hrightBound, _heBound⟩ :=
    exists_normalized_component_equation_with_height
      hN pair hC hcard
  have hdMem :
      d ∈ squarefreeSmoothUpTo
        (L + 1) (boundedRatioCutoff M L ^ K) := by
    rw [mem_squarefreeSmoothUpTo]
    refine ⟨hd, hdBound, hdsq, ?_⟩
    intro p hp
    exact hdsmooth p
      (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)
  apply Finset.mem_biUnion.mpr
  refine ⟨d, hdMem, ?_⟩
  rw [mem_rightFixedSquareClassFiber]
  refine ⟨hpair, hd, hdsq, hdsmooth, hdBound, ?_⟩
  exact ⟨C, hC, hcard, hleft, hright, z, hz, hwhole⟩

/-! ## Injection into the normalized mobile equation -/

/-- Deterministic normalized solution attached to a left-oriented pair. -/
def leftFixedSquareClassSolution
    {N M L : ℕ}
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (pair : SeparatedBoundedRatioPair N M L) : ℕ × ℕ :=
  (pair.1.2, canonicalSquarePart (shapeRightProduct shape pair.1.2))

/-- Deterministic normalized solution attached to a right-oriented pair. -/
def rightFixedSquareClassSolution
    {N M L : ℕ}
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (pair : SeparatedBoundedRatioPair N M L) : ℕ × ℕ :=
  (pair.1.1, canonicalSquarePart (shapeLeftProduct shape pair.1.1))

private theorem first_eq_base_succ
    {N M L base : ℕ}
    (hN : 2 ≤ N)
    {pair : SeparatedBoundedRatioPair N M L}
    (hbase : pair.1.1 - 1 = base) :
    pair.1.1 = base + 1 := by
  have hx := (pair_coordinates_two_le hN pair).1
  omega

private theorem second_eq_base_succ
    {N M L base : ℕ}
    (hN : 2 ≤ N)
    {pair : SeparatedBoundedRatioPair N M L}
    (hbase : pair.1.2 - 1 = base) :
    pair.1.2 = base + 1 := by
  have hy := (pair_coordinates_two_le hN pair).2
  omega

theorem leftFixedSquareClassSolution_mem
    {N M A L K base d : ℕ} (hN : 2 ≤ N)
    {shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1))}
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈ leftFixedSquareClassFiber
        N M A L K base shape d) :
    offsetProductNatFiber shape.2
      (leftNormalizedCoefficient shape base d) M
      (leftFixedSquareClassSolution shape pair) := by
  rcases mem_leftFixedSquareClassFiber.mp hpair with
    ⟨hbaseFiber, hd, hdsq, _hdsmooth, _hdBound,
      C, hC, _hcard, hleft, hright, z, hz, hwhole⟩
  have hbase := (mem_leftBaseShapeFiber.mp hbaseFiber).2
  have hxEq : pair.1.1 = base + 1 :=
    first_eq_base_succ hN hbase
  have hcoords := pair_coordinates_two_le hN pair
  have hblock :=
    mem_separatedBoundedRatioPairs.mp pair.2
  have hP :
      0 < componentLeftProduct pair.1.1 pair.1.2 L C :=
    componentLeftProduct_pos hcoords.1 C
  have hQ :
      0 < componentRightProduct pair.1.1 pair.1.2 L C :=
    componentRightProduct_pos hcoords.2 C
  have hnormalized :=
    canonical_normalization hP hQ hd hz hdsq hwhole
  refine ⟨hcoords.2, Nat.le_of_lt
    (BoundedRatioGeometry.mem_boundedRatioBlock.mp hblock.2.1).2, ?_⟩
  change
    shapeRightProduct shape pair.1.2 =
      leftNormalizedCoefficient shape base d *
        canonicalSquarePart (shapeRightProduct shape pair.1.2) ^ 2
  have hPshape :
      componentLeftProduct pair.1.1 pair.1.2 L C =
        shapeLeftProduct shape (base + 1) := by
    rw [componentLeftProduct_eq_offsetProduct, hleft, hxEq]
    rfl
  have hQshape :
      componentRightProduct pair.1.1 pair.1.2 L C =
        shapeRightProduct shape pair.1.2 := by
    rw [componentRightProduct_eq_offsetProduct, hright]
    rfl
  rw [← hQshape]
  simpa only [leftNormalizedCoefficient, ← hPshape, ← hQshape] using
    hnormalized.2.2.2.1

theorem rightFixedSquareClassSolution_mem
    {N M A L K base d : ℕ} (hN : 2 ≤ N)
    {shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1))}
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈ rightFixedSquareClassFiber
        N M A L K base shape d) :
    offsetProductNatFiber shape.1
      (rightNormalizedCoefficient shape base d) M
      (rightFixedSquareClassSolution shape pair) := by
  rcases mem_rightFixedSquareClassFiber.mp hpair with
    ⟨hbaseFiber, hd, hdsq, _hdsmooth, _hdBound,
      C, hC, _hcard, hleft, hright, z, hz, hwhole⟩
  have hbase := (mem_rightBaseShapeFiber.mp hbaseFiber).2
  have hyEq : pair.1.2 = base + 1 :=
    second_eq_base_succ hN hbase
  have hcoords := pair_coordinates_two_le hN pair
  have hblock :=
    mem_separatedBoundedRatioPairs.mp pair.2
  have hP :
      0 < componentLeftProduct pair.1.1 pair.1.2 L C :=
    componentLeftProduct_pos hcoords.1 C
  have hQ :
      0 < componentRightProduct pair.1.1 pair.1.2 L C :=
    componentRightProduct_pos hcoords.2 C
  have hnormalized :=
    canonical_normalization hQ hP hd hz hdsq (by
      simpa [mul_comm] using hwhole)
  refine ⟨hcoords.1, Nat.le_of_lt
    (BoundedRatioGeometry.mem_boundedRatioBlock.mp hblock.1).2, ?_⟩
  change
    shapeLeftProduct shape pair.1.1 =
      rightNormalizedCoefficient shape base d *
        canonicalSquarePart (shapeLeftProduct shape pair.1.1) ^ 2
  have hPshape :
      componentLeftProduct pair.1.1 pair.1.2 L C =
        shapeLeftProduct shape pair.1.1 := by
    rw [componentLeftProduct_eq_offsetProduct, hleft]
    rfl
  have hQshape :
      componentRightProduct pair.1.1 pair.1.2 L C =
        shapeRightProduct shape (base + 1) := by
    rw [componentRightProduct_eq_offsetProduct, hright, hyEq]
    rfl
  rw [← hPshape]
  simpa only [rightNormalizedCoefficient, ← hQshape, ← hPshape] using
    hnormalized.2.2.2.1

theorem leftFixedSquareClassSolution_injective_on
    {N M A L K base d : ℕ} (hN : 2 ≤ N)
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    {u v : SeparatedBoundedRatioPair N M L}
    (hu :
      u ∈ leftFixedSquareClassFiber
        N M A L K base shape d)
    (hv :
      v ∈ leftFixedSquareClassFiber
        N M A L K base shape d)
    (huv :
      leftFixedSquareClassSolution shape u =
        leftFixedSquareClassSolution shape v) :
    u = v := by
  have huBase :=
    (mem_leftBaseShapeFiber.mp
      (mem_leftFixedSquareClassFiber.mp hu).1).2
  have hvBase :=
    (mem_leftBaseShapeFiber.mp
      (mem_leftFixedSquareClassFiber.mp hv).1).2
  have hfirst :
      u.1.1 = v.1.1 := by
    rw [first_eq_base_succ hN huBase,
      first_eq_base_succ hN hvBase]
  have hsecond :
      u.1.2 = v.1.2 := by
    have :=
      congrArg Prod.fst huv
    simpa only [leftFixedSquareClassSolution] using this
  exact Subtype.ext (Prod.ext hfirst hsecond)

theorem rightFixedSquareClassSolution_injective_on
    {N M A L K base d : ℕ} (hN : 2 ≤ N)
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    {u v : SeparatedBoundedRatioPair N M L}
    (hu :
      u ∈ rightFixedSquareClassFiber
        N M A L K base shape d)
    (hv :
      v ∈ rightFixedSquareClassFiber
        N M A L K base shape d)
    (huv :
      rightFixedSquareClassSolution shape u =
        rightFixedSquareClassSolution shape v) :
    u = v := by
  have huBase :=
    (mem_rightBaseShapeFiber.mp
      (mem_rightFixedSquareClassFiber.mp hu).1).2
  have hvBase :=
    (mem_rightBaseShapeFiber.mp
      (mem_rightFixedSquareClassFiber.mp hv).1).2
  have hfirst :
      u.1.1 = v.1.1 := by
    have :=
      congrArg Prod.fst huv
    simpa only [rightFixedSquareClassSolution] using this
  have hsecond :
      u.1.2 = v.1.2 := by
    rw [second_eq_base_succ hN huBase,
      second_eq_base_succ hN hvBase]
  exact Subtype.ext (Prod.ext hfirst hsecond)

/-! ## Generic fixed-`d` and summed counts -/

theorem card_leftFixedSquareClassFiber_le
    {N M A L K base d Q : ℕ} (hN : 2 ≤ N)
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (hcount :
      HasAtMostSolutions
        (offsetProductNatFiber shape.2
          (leftNormalizedCoefficient shape base d) M)
        Q) :
    (leftFixedSquareClassFiber
      N M A L K base shape d).card ≤ Q := by
  classical
  let f : SeparatedBoundedRatioPair N M L → ℕ × ℕ :=
    leftFixedSquareClassSolution shape
  let population :=
    leftFixedSquareClassFiber N M A L K base shape d
  have himage :
      ∀ solution ∈ population.image f,
        offsetProductNatFiber shape.2
          (leftNormalizedCoefficient shape base d) M solution := by
    intro solution hsolution
    obtain ⟨pair, hpair, rfl⟩ :=
      Finset.mem_image.mp hsolution
    exact leftFixedSquareClassSolution_mem hN hpair
  have hinjective :
      Set.InjOn f (↑population : Set
        (SeparatedBoundedRatioPair N M L)) := by
    intro u hu v hv huv
    exact leftFixedSquareClassSolution_injective_on
      hN shape hu hv huv
  calc
    population.card = (population.image f).card :=
      (Finset.card_image_of_injOn hinjective).symm
    _ ≤ Q := hcount _ himage

theorem card_rightFixedSquareClassFiber_le
    {N M A L K base d Q : ℕ} (hN : 2 ≤ N)
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (hcount :
      HasAtMostSolutions
        (offsetProductNatFiber shape.1
          (rightNormalizedCoefficient shape base d) M)
        Q) :
    (rightFixedSquareClassFiber
      N M A L K base shape d).card ≤ Q := by
  classical
  let f : SeparatedBoundedRatioPair N M L → ℕ × ℕ :=
    rightFixedSquareClassSolution shape
  let population :=
    rightFixedSquareClassFiber N M A L K base shape d
  have himage :
      ∀ solution ∈ population.image f,
        offsetProductNatFiber shape.1
          (rightNormalizedCoefficient shape base d) M solution := by
    intro solution hsolution
    obtain ⟨pair, hpair, rfl⟩ :=
      Finset.mem_image.mp hsolution
    exact rightFixedSquareClassSolution_mem hN hpair
  have hinjective :
      Set.InjOn f (↑population : Set
        (SeparatedBoundedRatioPair N M L)) := by
    intro u hu v hv huv
    exact rightFixedSquareClassSolution_injective_on
      hN shape hu hv huv
  calc
    population.card = (population.image f).card :=
      (Finset.card_image_of_injOn hinjective).symm
    _ ≤ Q := hcount _ himage

theorem card_leftBaseShapeFiber_le_of_fixedSquareClassCounts
    {N M A L K base Q : ℕ} (hN : 2 ≤ N)
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (hcount :
      ∀ d ∈ squarefreeSmoothUpTo
          (L + 1) (boundedRatioCutoff M L ^ K),
        HasAtMostSolutions
          (offsetProductNatFiber shape.2
            (leftNormalizedCoefficient shape base d) M)
          Q) :
    (leftBaseShapeFiber N M A L K base shape).card ≤
      (squarefreeSmoothUpTo
        (L + 1) (boundedRatioCutoff M L ^ K)).card * Q := by
  classical
  let D :=
    squarefreeSmoothUpTo
      (L + 1) (boundedRatioCutoff M L ^ K)
  calc
    (leftBaseShapeFiber N M A L K base shape).card ≤
        (D.biUnion fun d =>
          leftFixedSquareClassFiber
            N M A L K base shape d).card :=
      Finset.card_le_card
        (leftBaseShapeFiber_subset_squareClassUnion hN shape)
    _ ≤
        ∑ d ∈ D,
          (leftFixedSquareClassFiber
            N M A L K base shape d).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _d ∈ D, Q :=
      Finset.sum_le_sum fun d hd =>
        card_leftFixedSquareClassFiber_le hN shape
          (hcount d (by simpa only [D] using hd))
    _ = D.card * Q := by simp

theorem card_rightBaseShapeFiber_le_of_fixedSquareClassCounts
    {N M A L K base Q : ℕ} (hN : 2 ≤ N)
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (hcount :
      ∀ d ∈ squarefreeSmoothUpTo
          (L + 1) (boundedRatioCutoff M L ^ K),
        HasAtMostSolutions
          (offsetProductNatFiber shape.1
            (rightNormalizedCoefficient shape base d) M)
          Q) :
    (rightBaseShapeFiber N M A L K base shape).card ≤
      (squarefreeSmoothUpTo
        (L + 1) (boundedRatioCutoff M L ^ K)).card * Q := by
  classical
  let D :=
    squarefreeSmoothUpTo
      (L + 1) (boundedRatioCutoff M L ^ K)
  calc
    (rightBaseShapeFiber N M A L K base shape).card ≤
        (D.biUnion fun d =>
          rightFixedSquareClassFiber
            N M A L K base shape d).card :=
      Finset.card_le_card
        (rightBaseShapeFiber_subset_squareClassUnion hN shape)
    _ ≤
        ∑ d ∈ D,
          (rightFixedSquareClassFiber
            N M A L K base shape d).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _d ∈ D, Q :=
      Finset.sum_le_sum fun d hd =>
        card_rightFixedSquareClassFiber_le hN shape
          (hcount d (by simpa only [D] using hd))
    _ = D.card * Q := by simp

/--
Nonuniform version of the preceding summation.  It is the exact form needed
when the ES bound depends on the normalized coefficient attached to `d`.
-/
theorem card_leftBaseShapeFiber_le_sum_fixedSquareClassCounts
    {N M A L K base : ℕ} (hN : 2 ≤ N)
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (Q : ℕ → ℕ)
    (hcount :
      ∀ d ∈ squarefreeSmoothUpTo
          (L + 1) (boundedRatioCutoff M L ^ K),
        HasAtMostSolutions
          (offsetProductNatFiber shape.2
            (leftNormalizedCoefficient shape base d) M)
          (Q d)) :
    (leftBaseShapeFiber N M A L K base shape).card ≤
      ∑ d ∈ squarefreeSmoothUpTo
        (L + 1) (boundedRatioCutoff M L ^ K), Q d := by
  classical
  let D :=
    squarefreeSmoothUpTo
      (L + 1) (boundedRatioCutoff M L ^ K)
  calc
    (leftBaseShapeFiber N M A L K base shape).card ≤
        (D.biUnion fun d =>
          leftFixedSquareClassFiber
            N M A L K base shape d).card :=
      Finset.card_le_card
        (leftBaseShapeFiber_subset_squareClassUnion hN shape)
    _ ≤
        ∑ d ∈ D,
          (leftFixedSquareClassFiber
            N M A L K base shape d).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ d ∈ D, Q d :=
      Finset.sum_le_sum fun d hd =>
        card_leftFixedSquareClassFiber_le hN shape
          (hcount d (by simpa only [D] using hd))

theorem card_rightBaseShapeFiber_le_sum_fixedSquareClassCounts
    {N M A L K base : ℕ} (hN : 2 ≤ N)
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (Q : ℕ → ℕ)
    (hcount :
      ∀ d ∈ squarefreeSmoothUpTo
          (L + 1) (boundedRatioCutoff M L ^ K),
        HasAtMostSolutions
          (offsetProductNatFiber shape.1
            (rightNormalizedCoefficient shape base d) M)
          (Q d)) :
    (rightBaseShapeFiber N M A L K base shape).card ≤
      ∑ d ∈ squarefreeSmoothUpTo
        (L + 1) (boundedRatioCutoff M L ^ K), Q d := by
  classical
  let D :=
    squarefreeSmoothUpTo
      (L + 1) (boundedRatioCutoff M L ^ K)
  calc
    (rightBaseShapeFiber N M A L K base shape).card ≤
        (D.biUnion fun d =>
          rightFixedSquareClassFiber
            N M A L K base shape d).card :=
      Finset.card_le_card
        (rightBaseShapeFiber_subset_squareClassUnion hN shape)
    _ ≤
        ∑ d ∈ D,
          (rightFixedSquareClassFiber
            N M A L K base shape d).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ d ∈ D, Q d :=
      Finset.sum_le_sum fun d hd =>
        card_rightFixedSquareClassFiber_le hN shape
          (hcount d (by simpa only [D] using hd))

/-! ## Degree one is completely discharged -/

private theorem oneOffsetNatShift_le
    {L : ℕ} (i : Fin (L + 1)) :
    oneOffsetNatShift i ≤ L := by
  unfold oneOffsetNatShift
  split_ifs
  · omega
  · omega

theorem card_leftBaseShapeFiber_degree_one
    {N M A L K base : ℕ} (hN : 2 ≤ N)
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (hdegree : shape.2.card = 1) :
    (leftBaseShapeFiber N M A L K base shape).card ≤
      (squarefreeSmoothUpTo
          (L + 1) (boundedRatioCutoff M L ^ K)).card *
        (Nat.sqrt (M + L) + 1) := by
  apply card_leftBaseShapeFiber_le_of_fixedSquareClassCounts
    hN shape
  intro d hd
  obtain ⟨i, hi, hcount⟩ :=
    offsetProductNatFiber_degree_one_atMost
      shape.2 hdegree
      (leftNormalizedCoefficient shape base d) M
      (leftNormalizedCoefficient_pos shape base d)
  intro s hs
  have hsmall := hcount s hs
  calc
    s.card ≤ Nat.sqrt (M + oneOffsetNatShift i) + 1 :=
      hsmall
    _ ≤ Nat.sqrt (M + L) + 1 := by
      exact Nat.add_le_add_right
        (Nat.sqrt_le_sqrt
          (Nat.add_le_add_left (oneOffsetNatShift_le i) M)) 1

theorem card_rightBaseShapeFiber_degree_one
    {N M A L K base : ℕ} (hN : 2 ≤ N)
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (hdegree : shape.1.card = 1) :
    (rightBaseShapeFiber N M A L K base shape).card ≤
      (squarefreeSmoothUpTo
          (L + 1) (boundedRatioCutoff M L ^ K)).card *
        (Nat.sqrt (M + L) + 1) := by
  apply card_rightBaseShapeFiber_le_of_fixedSquareClassCounts
    hN shape
  intro d hd
  obtain ⟨i, hi, hcount⟩ :=
    offsetProductNatFiber_degree_one_atMost
      shape.1 hdegree
      (rightNormalizedCoefficient shape base d) M
      (rightNormalizedCoefficient_pos shape base d)
  intro s hs
  have hsmall := hcount s hs
  calc
    s.card ≤ Nat.sqrt (M + oneOffsetNatShift i) + 1 :=
      hsmall
    _ ≤ Nat.sqrt (M + L) + 1 := by
      exact Nat.add_le_add_right
        (Nat.sqrt_le_sqrt
          (Nat.add_le_add_left (oneOffsetNatShift_le i) M)) 1

/-! ### Uniform half-power envelope for the degree-one branch -/

/--
Endpoint-independent real envelope for every bounded-ratio degree-one
fibre.  The smooth square-class factor is `N^o(1)` and the remaining factor
is a fixed multiple of `sqrt N`.
-/
noncomputable def degreeOneFixedFiberEnvelope
    (κ₀ N L : ℕ) : ℝ :=
  Real.sqrt N *
    ((2 * Real.sqrt (κ₀ + 1)) *
      smoothKernelChebyshevEnvelope (L + 1))

theorem degreeOneFixedFiberEnvelope_uniformHalfPower
    {C : ℝ} (hC : 0 ≤ C) (κ₀ : ℕ) :
    UniformHalfPowerSubpolynomialOn
      (CriticalRunWindow.InRunLengthWindow C)
      (degreeOneFixedFiberEnvelope κ₀) := by
  have hsmooth :=
    smoothKernelChebyshevEnvelope_uniformSubpolynomial hC
  have hresidual :
      UniformSubpolynomialOn
        (CriticalRunWindow.InRunLengthWindow C)
        (fun _N L =>
          (2 * Real.sqrt (κ₀ + 1)) *
            smoothKernelChebyshevEnvelope (L + 1)) := by
    simpa only using
      ExpSqrtLog.uniformSubpolynomialOn_const_mul
        (2 * Real.sqrt (κ₀ + 1)) hsmooth
  apply UniformHalfPower.of_sqrt_mul_subpolynomial hresidual
  refine ⟨0, ?_⟩
  intro N _hN L _hrun
  unfold degreeOneFixedFiberEnvelope
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]

private theorem sqrt_width_add_one_cast_le
    {κ₀ N M L : ℕ}
    (hN : 1 ≤ N) (hMκ : M ≤ κ₀ * N) (hL : L ≤ N) :
    ((Nat.sqrt (M + L) + 1 : ℕ) : ℝ) ≤
      2 * Real.sqrt (κ₀ + 1) * Real.sqrt N := by
  have hwidth :
      M + L ≤ (κ₀ + 1) * N := by
    calc
      M + L ≤ κ₀ * N + N := Nat.add_le_add hMκ hL
      _ = (κ₀ + 1) * N := by
        rw [Nat.add_mul, one_mul]
  have hroot :
      (Nat.sqrt (M + L) : ℝ) ≤
        Real.sqrt (((κ₀ + 1) * N : ℕ) : ℝ) := by
    exact Real.nat_sqrt_le_real_sqrt.trans
      (Real.sqrt_le_sqrt (by exact_mod_cast hwidth))
  have hargumentOne :
      (1 : ℝ) ≤ (((κ₀ + 1) * N : ℕ) : ℝ) := by
    exact_mod_cast
      (show 1 ≤ (κ₀ + 1) * N by
        exact Nat.mul_pos (by omega) (by omega))
  have hone :
      (1 : ℝ) ≤
        Real.sqrt (((κ₀ + 1) * N : ℕ) : ℝ) :=
    Real.one_le_sqrt.mpr hargumentOne
  calc
    ((Nat.sqrt (M + L) + 1 : ℕ) : ℝ) =
        (Nat.sqrt (M + L) : ℝ) + 1 := by norm_num
    _ ≤
        Real.sqrt (((κ₀ + 1) * N : ℕ) : ℝ) +
          Real.sqrt (((κ₀ + 1) * N : ℕ) : ℝ) :=
      add_le_add hroot hone
    _ =
        2 * Real.sqrt (κ₀ + 1) * Real.sqrt N := by
      rw [Nat.cast_mul,
        Real.sqrt_mul (Nat.cast_nonneg (κ₀ + 1))]
      norm_num only [Nat.cast_add, Nat.cast_one]
      ring

theorem card_leftBaseShapeFiber_degree_one_cast_le_envelope
    {κ₀ N M A L K base : ℕ} (hN : 2 ≤ N)
    (hMκ : M ≤ κ₀ * N) (hL : L ≤ N) (hB : 4 ≤ L + 1)
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (hdegree : shape.2.card = 1) :
    ((leftBaseShapeFiber
        N M A L K base shape).card : ℝ) ≤
      degreeOneFixedFiberEnvelope κ₀ N L := by
  have hfinite :=
    card_leftBaseShapeFiber_degree_one
      (M := M) (A := A) (K := K) (base := base)
      hN shape hdegree
  have hfiniteCast :
      ((leftBaseShapeFiber
          N M A L K base shape).card : ℝ) ≤
        ((squarefreeSmoothUpTo
          (L + 1) (boundedRatioCutoff M L ^ K)).card : ℝ) *
          ((Nat.sqrt (M + L) + 1 : ℕ) : ℝ) := by
    exact_mod_cast hfinite
  have hsmooth :=
    card_squarefreeSmoothUpTo_le_smoothKernelChebyshevEnvelope
      (X := boundedRatioCutoff M L ^ K) hB
  have hroot :=
    sqrt_width_add_one_cast_le
      (κ₀ := κ₀) (M := M) (L := L)
      (show 1 ≤ N by omega) hMκ hL
  calc
    ((leftBaseShapeFiber
        N M A L K base shape).card : ℝ) ≤
        ((squarefreeSmoothUpTo
          (L + 1) (boundedRatioCutoff M L ^ K)).card : ℝ) *
          ((Nat.sqrt (M + L) + 1 : ℕ) : ℝ) :=
      hfiniteCast
    _ ≤
        smoothKernelChebyshevEnvelope (L + 1) *
          (2 * Real.sqrt (κ₀ + 1) * Real.sqrt N) :=
      mul_le_mul hsmooth hroot (by positivity) (by
        unfold smoothKernelChebyshevEnvelope
        positivity)
    _ = degreeOneFixedFiberEnvelope κ₀ N L := by
      unfold degreeOneFixedFiberEnvelope
      ring

theorem card_rightBaseShapeFiber_degree_one_cast_le_envelope
    {κ₀ N M A L K base : ℕ} (hN : 2 ≤ N)
    (hMκ : M ≤ κ₀ * N) (hL : L ≤ N) (hB : 4 ≤ L + 1)
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (hdegree : shape.1.card = 1) :
    ((rightBaseShapeFiber
        N M A L K base shape).card : ℝ) ≤
      degreeOneFixedFiberEnvelope κ₀ N L := by
  have hfinite :=
    card_rightBaseShapeFiber_degree_one
      (M := M) (A := A) (K := K) (base := base)
      hN shape hdegree
  have hfiniteCast :
      ((rightBaseShapeFiber
          N M A L K base shape).card : ℝ) ≤
        ((squarefreeSmoothUpTo
          (L + 1) (boundedRatioCutoff M L ^ K)).card : ℝ) *
          ((Nat.sqrt (M + L) + 1 : ℕ) : ℝ) := by
    exact_mod_cast hfinite
  have hsmooth :=
    card_squarefreeSmoothUpTo_le_smoothKernelChebyshevEnvelope
      (X := boundedRatioCutoff M L ^ K) hB
  have hroot :=
    sqrt_width_add_one_cast_le
      (κ₀ := κ₀) (M := M) (L := L)
      (show 1 ≤ N by omega) hMκ hL
  calc
    ((rightBaseShapeFiber
        N M A L K base shape).card : ℝ) ≤
        ((squarefreeSmoothUpTo
          (L + 1) (boundedRatioCutoff M L ^ K)).card : ℝ) *
          ((Nat.sqrt (M + L) + 1 : ℕ) : ℝ) :=
      hfiniteCast
    _ ≤
        smoothKernelChebyshevEnvelope (L + 1) *
          (2 * Real.sqrt (κ₀ + 1) * Real.sqrt N) :=
      mul_le_mul hsmooth hroot (by positivity) (by
        unfold smoothKernelChebyshevEnvelope
        positivity)
    _ = degreeOneFixedFiberEnvelope κ₀ N L := by
      unfold degreeOneFixedFiberEnvelope
      ring

/-! ## Natural-to-integral transfer -/

def natSolutionToInt (solution : ℕ × ℕ) : ℤ × ℤ :=
  ((solution.1 : ℤ), (solution.2 : ℤ))

theorem natSolutionToInt_injective :
    Function.Injective natSolutionToInt := by
  intro u v huv
  have hfirst :=
    congrArg Prod.fst huv
  have hsecond :=
    congrArg Prod.snd huv
  apply Prod.ext
  · change (u.1 : ℤ) = (v.1 : ℤ) at hfirst
    exact_mod_cast hfirst
  · change (u.2 : ℤ) = (v.2 : ℤ) at hsecond
    exact_mod_cast hsecond

/-! ## Degree two: Pell boxes and the exceptional divisor factorization -/

/--
A common integral height for the completed-square coordinates of every
natural solution with mobile start at most `Y`.  The deliberately quadratic
height keeps the transfer elementary and is still polynomial in the ambient
cutoff, as required by `GeneralizedPellPolynomialBoxStatement`.
-/
def degreeTwoPellHeight (Y L : ℕ) : ℕ :=
  2 * (Y + L + 1) ^ 2

private theorem offsetShiftOfCard_natAbs_le
    {L r : ℕ} (offsets : Finset (Fin (L + 1)))
    (hcard : offsets.card = r) (i : Fin r) :
    (offsetShiftOfCard offsets hcard i).natAbs ≤ L + 1 := by
  have hbound :=
    AlignedRungeBridge.abs_channelVertexOffset_le
      ((offsetEnumeration offsets
        (Fin.cast hcard.symm i)).1)
  rw [Int.abs_eq_natAbs] at hbound
  exact_mod_cast hbound

private theorem startCompleteVertexLabel_le_mobileCutoff
    {L x Y : ℕ} (hxY : x ≤ Y)
    (i : Fin (L + 1)) :
    startCompleteVertexLabel x L i ≤ Y + L := by
  simp only [startCompleteVertexLabel]
  split_ifs <;> omega

private theorem offsetProductNatFiber_squarePart_le
    {L e Y : ℕ}
    (offsets : Finset (Fin (L + 1)))
    {solution : ℕ × ℕ}
    (he : 0 < e)
    (hsolution :
      offsetProductNatFiber offsets e Y solution) :
    solution.2 ^ 2 ≤ (Y + L) ^ offsets.card := by
  calc
    solution.2 ^ 2 ≤ e * solution.2 ^ 2 :=
      Nat.le_mul_of_pos_left _ he
    _ =
        ∏ i ∈ offsets,
          startCompleteVertexLabel solution.1 L i :=
      hsolution.2.2.symm
    _ ≤ ∏ _i ∈ offsets, (Y + L) :=
      Finset.prod_le_prod
        (fun _i _hi => Nat.zero_le _)
        (fun i _hi =>
          startCompleteVertexLabel_le_mobileCutoff
            hsolution.2.1 i)
    _ = (Y + L) ^ offsets.card := by simp

private theorem natSolutionToInt_degreeTwoPellHeight
    {L e Y : ℕ}
    (offsets : Finset (Fin (L + 1)))
    (hdegree : offsets.card = 2)
    {solution : ℕ × ℕ}
    (he : 0 < e)
    (hsolution :
      offsetProductNatFiber offsets e Y solution) :
    let pell :=
      toPellPair
        (offsetShiftOfCard offsets hdegree 0)
        (offsetShiftOfCard offsets hdegree 1)
        (natSolutionToInt solution)
    pell.1.natAbs ≤ degreeTwoPellHeight Y L ∧
      pell.2.natAbs ≤ degreeTwoPellHeight Y L := by
  dsimp only [toPellPair, natSolutionToInt, Prod.fst, Prod.snd]
  have hshiftZero :=
    offsetShiftOfCard_natAbs_le offsets hdegree (0 : Fin 2)
  have hshiftOne :=
    offsetShiftOfCard_natAbs_le offsets hdegree (1 : Fin 2)
  have hfirst :
      (2 * (solution.1 : ℤ) +
          offsetShiftOfCard offsets hdegree 0 +
          offsetShiftOfCard offsets hdegree 1).natAbs ≤
        degreeTwoPellHeight Y L := by
    calc
      (2 * (solution.1 : ℤ) +
          offsetShiftOfCard offsets hdegree 0 +
          offsetShiftOfCard offsets hdegree 1).natAbs ≤
          (2 * (solution.1 : ℤ) +
            offsetShiftOfCard offsets hdegree 0).natAbs +
            (offsetShiftOfCard offsets hdegree 1).natAbs :=
        Int.natAbs_add_le _ _
      _ ≤
          (2 * (solution.1 : ℤ)).natAbs +
              (offsetShiftOfCard offsets hdegree 0).natAbs +
            (offsetShiftOfCard offsets hdegree 1).natAbs := by
        exact Nat.add_le_add_right
          (Int.natAbs_add_le _ _) _
      _ ≤ 2 * solution.1 + (L + 1) + (L + 1) := by
        norm_num only [Int.natAbs_mul, Int.natAbs_natCast]
        exact
          Nat.add_le_add
            (Nat.add_le_add_left hshiftZero (2 * solution.1))
            hshiftOne
      _ ≤ 2 * (Y + L + 1) := by
        have hxY : solution.1 ≤ Y := hsolution.2.1
        omega
      _ ≤ degreeTwoPellHeight Y L := by
        unfold degreeTwoPellHeight
        exact Nat.mul_le_mul_left 2
          (Nat.le_self_pow (by norm_num : (2 : ℕ) ≠ 0)
            (Y + L + 1))
  have hsquare :
      solution.2 ^ 2 ≤ (Y + L) ^ 2 := by
    simpa only [hdegree] using
      offsetProductNatFiber_squarePart_le
        offsets he hsolution
  have hv :
      solution.2 ≤ (Y + L) ^ 2 :=
    (Nat.le_self_pow (by norm_num : (2 : ℕ) ≠ 0)
      solution.2).trans hsquare
  have hsecond :
      (2 * (solution.2 : ℤ)).natAbs ≤
        degreeTwoPellHeight Y L := by
    simp only [Int.natAbs_mul, Int.natAbs_natCast]
    unfold degreeTwoPellHeight
    exact (Nat.mul_le_mul_left 2 hv).trans
      (Nat.mul_le_mul_left 2
        (Nat.pow_le_pow_left (Nat.le_add_right _ 1) 2))
  exact ⟨hfirst, hsecond⟩

/--
Exact transfer of the bounded natural degree-two fibre to the already
formalized Pell box.  No asymptotic bridge is hidden here: callers may
supply any finite Pell-box estimate at the explicit height
`degreeTwoPellHeight Y L`.
-/
theorem offsetProductNatFiber_degree_two_atMost_of_pell
    {L P d Y Q : ℕ}
    (offsets : Finset (Fin (L + 1)))
    (hdegree : offsets.card = 2)
    (hPell :
      PellInput.HasAtMostSolutionsReal
        (PellInput.pellBox
          1
          (squarefreeKernel (d * P))
          ((offsetShiftOfCard offsets hdegree 0 -
            offsetShiftOfCard offsets hdegree 1) ^ 2)
          (degreeTwoPellHeight Y L))
        (Q : ℝ)) :
    HasAtMostSolutions
      (offsetProductNatFiber offsets
        (squarefreeKernel (d * P)) Y)
      Q := by
  intro s hs
  let f : ℕ × ℕ → ℤ × ℤ := natSolutionToInt
  have hnormalized :=
    normalizedOffsetDegreeTwo_atMost_of_pell
      offsets hdegree hPell
  have himage :
      ∀ solution ∈ s.image f,
        normalizedShiftedEquation
              P d (offsetShift offsets) solution ∧
          (toPellPair
            (offsetShiftOfCard offsets hdegree 0)
            (offsetShiftOfCard offsets hdegree 1)
            solution).1.natAbs ≤
              degreeTwoPellHeight Y L ∧
          (toPellPair
            (offsetShiftOfCard offsets hdegree 0)
            (offsetShiftOfCard offsets hdegree 1)
            solution).2.natAbs ≤
              degreeTwoPellHeight Y L := by
    intro solution hsolution
    obtain ⟨source, hsource, rfl⟩ :=
      Finset.mem_image.mp hsolution
    dsimp only [f]
    have hdata :
        offsetProductNatFiber offsets
          (squarefreeKernel (d * P)) Y source :=
      hs source hsource
    have hsourceOne : 1 ≤ source.1 :=
      (by norm_num : 1 ≤ 2).trans hdata.1
    have he :
        0 < squarefreeKernel (d * P) :=
      squarefreeKernel_pos _
    refine ⟨?_, ?_⟩
    · unfold normalizedShiftedEquation shiftedSquareEquation
      change
        shiftedProduct (offsetShift offsets) (source.1 : ℤ) =
          (squarefreeKernel (d * P) : ℤ) *
            (source.2 : ℤ) ^ 2
      rw [shiftedProduct_offsetShift
        hsourceOne offsets]
      exact_mod_cast hdata.2.2
    · exact
        natSolutionToInt_degreeTwoPellHeight
          offsets hdegree he hdata
  have hbound := hnormalized (s.image f) himage
  have hcardImage :
      (s.image f).card = s.card := by
    simpa only [f] using
      Finset.card_image_of_injective s natSolutionToInt_injective
  have hbound' : (s.card : ℝ) ≤ (Q : ℝ) := by
    simpa only [hcardImage] using hbound
  exact_mod_cast hbound'

/--
Direct specialization of the registered generalized-Pell bridge to the
natural degree-two offset fibre.  The three displayed polynomial
inequalities are the complete height bookkeeping left to a caller:

* the normalized squarefree coefficient;
* the squared offset discriminant;
* the explicit natural-to-Pell height.

For coefficient at least two, squarefreeness proves the required nonsquare
condition internally.
-/
theorem offsetProductNatFiber_degree_two_polynomialBox_of_generalizedPell
    (hPell :
      PellInput.GeneralizedPellPolynomialBoxStatement) :
    ∀ E : ℕ, 0 < E →
      ∃ c : ℝ, 0 ≤ c ∧
        ∃ X₀ : ℕ, ∀ X ≥ X₀,
          ∀ (L : ℕ)
            (offsets : Finset (Fin (L + 1)))
            (hdegree : offsets.card = 2)
            (P d Y : ℕ),
          2 ≤ squarefreeKernel (d * P) →
          squarefreeKernel (d * P) ≤ X ^ E →
          ((offsetShiftOfCard offsets hdegree 0 -
            offsetShiftOfCard offsets hdegree 1) ^ 2).natAbs ≤
              X ^ E →
          degreeTwoPellHeight Y L ≤ X ^ E →
          HasAtMostSolutions
            (offsetProductNatFiber offsets
              (squarefreeKernel (d * P)) Y)
            ⌈PellInput.expLogLogBound c X⌉₊ := by
  intro E hE
  obtain ⟨c, hc, X₀, hX₀⟩ :=
    normalizedOffsetDegreeTwo_polynomialBox_of_generalizedPell
      hPell E hE
  refine ⟨c, hc, X₀, ?_⟩
  intro X hX L offsets hdegree P d Y heTwo
    heBound hdeltaBound hheightBound
  have hePos : 0 < squarefreeKernel (d * P) :=
    squarefreeKernel_pos _
  have heSquarefree :
      Squarefree (squarefreeKernel (d * P)) :=
    squarefreeKernel_squarefree _
  have heNeOne : squarefreeKernel (d * P) ≠ 1 := by
    omega
  have hratio :
      ¬IsSquare
        ((1 : ℚ) / (squarefreeKernel (d * P) : ℚ)) := by
    exact
      TerminalPartnerPell.not_isSquare_ratio_of_squarefree_of_ne
        (by norm_num : 0 < (1 : ℕ))
        hePos
        (by norm_num : Squarefree (1 : ℕ))
        heSquarefree
        (Ne.symm heNeOne)
  have hnormalized :=
    hX₀ X hX L offsets hdegree P d
      hePos heSquarefree hratio heBound hdeltaBound
  intro s hs
  let f : ℕ × ℕ → ℤ × ℤ := natSolutionToInt
  have himage :
      ∀ solution ∈ s.image f,
        normalizedShiftedEquation
              P d (offsetShift offsets) solution ∧
          (toPellPair
            (offsetShiftOfCard offsets hdegree 0)
            (offsetShiftOfCard offsets hdegree 1)
            solution).1.natAbs ≤ X ^ E ∧
          (toPellPair
            (offsetShiftOfCard offsets hdegree 0)
            (offsetShiftOfCard offsets hdegree 1)
            solution).2.natAbs ≤ X ^ E := by
    intro solution hsolution
    obtain ⟨source, hsource, rfl⟩ :=
      Finset.mem_image.mp hsolution
    dsimp only [f]
    have hdata :
        offsetProductNatFiber offsets
          (squarefreeKernel (d * P)) Y source :=
      hs source hsource
    have hsourceOne : 1 ≤ source.1 :=
      (by norm_num : 1 ≤ 2).trans hdata.1
    refine ⟨?_, ?_⟩
    · unfold normalizedShiftedEquation shiftedSquareEquation
      change
        shiftedProduct (offsetShift offsets) (source.1 : ℤ) =
          (squarefreeKernel (d * P) : ℤ) *
            (source.2 : ℤ) ^ 2
      rw [shiftedProduct_offsetShift hsourceOne offsets]
      exact_mod_cast hdata.2.2
    · have hheight :=
        natSolutionToInt_degreeTwoPellHeight
          offsets hdegree hePos hdata
      exact
        ⟨hheight.1.trans hheightBound,
          hheight.2.trans hheightBound⟩
  have hbound := hnormalized (s.image f) himage
  have hcardImage :
      (s.image f).card = s.card := by
    simpa only [f] using
      Finset.card_image_of_injective s natSolutionToInt_injective
  have hceil :
      PellInput.expLogLogBound c X ≤
        (⌈PellInput.expLogLogBound c X⌉₊ : ℝ) :=
    Nat.le_ceil _
  have hbound' :
      (s.card : ℝ) ≤
        (⌈PellInput.expLogLogBound c X⌉₊ : ℝ) := by
    have hboundCard :
        (s.card : ℝ) ≤ PellInput.expLogLogBound c X := by
      simpa only [hcardImage] using hbound
    exact hboundCard.trans hceil
  exact_mod_cast hbound'

/-- The two linear factors obtained from the completed-square coordinates. -/
def degreeTwoFactorPair
    (j₁ j₂ : ℤ) (solution : ℕ × ℕ) : ℤ × ℤ :=
  let pell := toPellPair j₁ j₂ (natSolutionToInt solution)
  (pell.1 - pell.2, pell.1 + pell.2)

/-- A positive integer has two signed copies of each natural factor pair. -/
theorem card_int_divisorsAntidiag_natCast
    (n : ℕ) :
    (Int.divisorsAntidiag (n : ℤ)).card =
      2 * n.divisorsAntidiagonal.card := by
  rw [Int.divisorsAntidiag_natCast, Finset.card_disjUnion]
  simp only [Finset.card_map]
  omega

/-- Natural factor pairs are in bijection with positive divisors. -/
theorem card_divisorsAntidiagonal_eq_card_divisors
    (n : ℕ) :
    n.divisorsAntidiagonal.card = n.divisors.card := by
  have hinjective :
      Set.InjOn Prod.fst
        (↑n.divisorsAntidiagonal : Set (ℕ × ℕ)) := by
    intro a ha b hb hab
    have haProduct :=
      (Nat.mem_divisorsAntidiagonal.mp ha).1
    have hbProduct :=
      (Nat.mem_divisorsAntidiagonal.mp hb).1
    have haFirst :
        0 < a.1 :=
      Nat.pos_of_ne_zero
        (Nat.left_ne_zero_of_mem_divisorsAntidiagonal ha)
    apply Prod.ext hab
    apply Nat.eq_of_mul_eq_mul_left haFirst
    calc
      a.1 * a.2 = n := haProduct
      _ = b.1 * b.2 := hbProduct.symm
      _ = a.1 * b.2 := by rw [hab]
  have hcard :=
    Finset.card_image_of_injOn hinjective
  rw [Nat.image_fst_divisorsAntidiagonal] at hcard
  exact hcard.symm

/-- Hence the signed factor-pair count is exactly twice `τ(n)`. -/
theorem card_int_divisorsAntidiag_natCast_eq_two_mul_divisors
    (n : ℕ) :
    (Int.divisorsAntidiag (n : ℤ)).card =
      2 * n.divisors.card := by
  rw [card_int_divisorsAntidiag_natCast,
    card_divisorsAntidiagonal_eq_card_divisors]

theorem degreeTwoFactorPair_injective
    (j₁ j₂ : ℤ) :
    Function.Injective (degreeTwoFactorPair j₁ j₂) := by
  intro u v huv
  have hfirst :
      (toPellPair j₁ j₂ (natSolutionToInt u)).1 -
          (toPellPair j₁ j₂ (natSolutionToInt u)).2 =
        (toPellPair j₁ j₂ (natSolutionToInt v)).1 -
          (toPellPair j₁ j₂ (natSolutionToInt v)).2 :=
    congrArg Prod.fst huv
  have hsecond :
      (toPellPair j₁ j₂ (natSolutionToInt u)).1 +
          (toPellPair j₁ j₂ (natSolutionToInt u)).2 =
        (toPellPair j₁ j₂ (natSolutionToInt v)).1 +
          (toPellPair j₁ j₂ (natSolutionToInt v)).2 :=
    congrArg Prod.snd huv
  have hpell :
      toPellPair j₁ j₂ (natSolutionToInt u) =
        toPellPair j₁ j₂ (natSolutionToInt v) := by
    apply Prod.ext <;> omega
  exact natSolutionToInt_injective
    (toPellPair_injective j₁ j₂ hpell)

private theorem offsetProductNatFiber_degree_two_maps_to_factorPair
    {L Y : ℕ}
    (offsets : Finset (Fin (L + 1)))
    (hdegree : offsets.card = 2)
    {solution : ℕ × ℕ}
    (hsolution :
      offsetProductNatFiber offsets 1 Y solution) :
    degreeTwoFactorPair
        (offsetShiftOfCard offsets hdegree 0)
        (offsetShiftOfCard offsets hdegree 1)
        solution ∈
      Int.divisorsAntidiag
        ((offsetShiftOfCard offsets hdegree 0 -
          offsetShiftOfCard offsets hdegree 1) ^ 2) := by
  let j₁ := offsetShiftOfCard offsets hdegree 0
  let j₂ := offsetShiftOfCard offsets hdegree 1
  have hshiftNe : j₁ ≠ j₂ := by
    intro hij
    have h01 : (0 : Fin 2) = 1 :=
      offsetShiftOfCard_injective offsets hdegree hij
    exact (by decide : (0 : Fin 2) ≠ 1) h01
  have hnormalized :
      normalizedShiftedEquation
        1 1 (offsetShift offsets)
        (natSolutionToInt solution) := by
    have hsourceOne : 1 ≤ solution.1 :=
      (by norm_num : 1 ≤ 2).trans hsolution.1
    have hkernel : squarefreeKernel (1 * 1) = 1 := by
      apply Nat.eq_one_of_dvd_one
      exact squarefreeKernel_dvd (by norm_num)
    unfold normalizedShiftedEquation shiftedSquareEquation
    change
      shiftedProduct (offsetShift offsets) (solution.1 : ℤ) =
        (squarefreeKernel (1 * 1) : ℤ) *
          (solution.2 : ℤ) ^ 2
    rw [shiftedProduct_offsetShift hsourceOne offsets]
    rw [hkernel]
    exact_mod_cast hsolution.2.2
  have htwo :
      twoShiftEquation j₁ j₂ 1
        (natSolutionToInt solution) := by
    have htwoRaw :=
      (reindexedOffsetNormalizedEquation_degree_two_iff
        offsets hdegree (natSolutionToInt solution)).mp
        ((reindexedOffsetNormalizedEquation_iff
          offsets hdegree (natSolutionToInt solution)).mpr
          hnormalized)
    have hkernel : squarefreeKernel (1 * 1) = 1 := by
      apply Nat.eq_one_of_dvd_one
      exact squarefreeKernel_dvd (by norm_num)
    simpa only [j₁, j₂, hkernel] using htwoRaw
  have hfactor :=
    twoShiftEquation_one_factorization htwo
  rw [Int.mem_divisorsAntidiag]
  refine ⟨?_, pow_ne_zero 2 (sub_ne_zero.mpr hshiftNe)⟩
  simpa only [degreeTwoFactorPair, j₁, j₂] using hfactor

/--
The exceptional normalized coefficient `e=1` is bounded exactly by the
finite set of signed divisor pairs of the nonzero offset discriminant.
This is the divisor-factorization branch of Lemma 17.21, with no external
Diophantine hypothesis.
-/
theorem offsetProductNatFiber_degree_two_one_atMost_divisors
    {L Y : ℕ}
    (offsets : Finset (Fin (L + 1)))
    (hdegree : offsets.card = 2) :
    HasAtMostSolutions
      (offsetProductNatFiber offsets 1 Y)
      (Int.divisorsAntidiag
        ((offsetShiftOfCard offsets hdegree 0 -
          offsetShiftOfCard offsets hdegree 1) ^ 2)).card := by
  intro s hs
  let j₁ := offsetShiftOfCard offsets hdegree 0
  let j₂ := offsetShiftOfCard offsets hdegree 1
  let f : ℕ × ℕ → ℤ × ℤ :=
    degreeTwoFactorPair j₁ j₂
  have hsubset :
      s.image f ⊆
        Int.divisorsAntidiag ((j₁ - j₂) ^ 2) := by
    intro pair hpair
    obtain ⟨solution, hsolution, rfl⟩ :=
      Finset.mem_image.mp hpair
    exact
      offsetProductNatFiber_degree_two_maps_to_factorPair
        offsets hdegree (hs solution hsolution)
  calc
    s.card = (s.image f).card := by
      symm
      exact Finset.card_image_of_injective _
        (degreeTwoFactorPair_injective j₁ j₂)
    _ ≤ (Int.divisorsAntidiag ((j₁ - j₂) ^ 2)).card :=
      Finset.card_le_card hsubset

/--
Ordinary divisor-function form of the preceding estimate:
`#solutions ≤ 2 τ(|Δ²|)`.
-/
theorem offsetProductNatFiber_degree_two_one_atMost_two_mul_divisors
    {L Y : ℕ}
    (offsets : Finset (Fin (L + 1)))
    (hdegree : offsets.card = 2) :
    HasAtMostSolutions
      (offsetProductNatFiber offsets 1 Y)
      (2 *
        (((offsetShiftOfCard offsets hdegree 0 -
          offsetShiftOfCard offsets hdegree 1) ^ 2).natAbs).divisors.card) := by
  have hcount :=
    offsetProductNatFiber_degree_two_one_atMost_divisors
      (Y := Y) offsets hdegree
  intro s hs
  have hsmall := hcount s hs
  let Δ :=
    offsetShiftOfCard offsets hdegree 0 -
      offsetShiftOfCard offsets hdegree 1
  have hcast : (((Δ ^ 2).natAbs : ℕ) : ℤ) = Δ ^ 2 := by
    rw [Int.natCast_natAbs, abs_of_nonneg (sq_nonneg Δ)]
  calc
    s.card ≤ (Int.divisorsAntidiag (Δ ^ 2)).card := by
      simpa only [Δ] using hsmall
    _ = (Int.divisorsAntidiag (((Δ ^ 2).natAbs : ℕ) : ℤ)).card := by
      rw [hcast]
    _ = 2 * ((Δ ^ 2).natAbs.divisors.card) :=
      card_int_divisorsAntidiag_natCast_eq_two_mul_divisors _

/-! ### Transfer back to the fixed square-class and fixed-shape fibres -/

theorem card_leftFixedSquareClassFiber_degree_two_of_pell
    {N M A L K base d Q : ℕ} (hN : 2 ≤ N)
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (hdegree : shape.2.card = 2)
    (hPell :
      PellInput.HasAtMostSolutionsReal
        (PellInput.pellBox
          1
          (leftNormalizedCoefficient shape base d)
          ((offsetShiftOfCard shape.2 hdegree 0 -
            offsetShiftOfCard shape.2 hdegree 1) ^ 2)
          (degreeTwoPellHeight M L))
        (Q : ℝ)) :
    (leftFixedSquareClassFiber
        N M A L K base shape d).card ≤ Q := by
  apply card_leftFixedSquareClassFiber_le hN shape
  simpa only [leftNormalizedCoefficient] using
    offsetProductNatFiber_degree_two_atMost_of_pell
      shape.2 hdegree hPell

theorem card_rightFixedSquareClassFiber_degree_two_of_pell
    {N M A L K base d Q : ℕ} (hN : 2 ≤ N)
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (hdegree : shape.1.card = 2)
    (hPell :
      PellInput.HasAtMostSolutionsReal
        (PellInput.pellBox
          1
          (rightNormalizedCoefficient shape base d)
          ((offsetShiftOfCard shape.1 hdegree 0 -
            offsetShiftOfCard shape.1 hdegree 1) ^ 2)
          (degreeTwoPellHeight M L))
        (Q : ℝ)) :
    (rightFixedSquareClassFiber
        N M A L K base shape d).card ≤ Q := by
  apply card_rightFixedSquareClassFiber_le hN shape
  simpa only [rightNormalizedCoefficient] using
    offsetProductNatFiber_degree_two_atMost_of_pell
      shape.1 hdegree hPell

theorem card_leftFixedSquareClassFiber_degree_two_one
    {N M A L K base d : ℕ} (hN : 2 ≤ N)
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (hdegree : shape.2.card = 2)
    (heq : leftNormalizedCoefficient shape base d = 1) :
    (leftFixedSquareClassFiber
        N M A L K base shape d).card ≤
      (Int.divisorsAntidiag
        ((offsetShiftOfCard shape.2 hdegree 0 -
          offsetShiftOfCard shape.2 hdegree 1) ^ 2)).card := by
  apply card_leftFixedSquareClassFiber_le hN shape
  simpa only [heq] using
    offsetProductNatFiber_degree_two_one_atMost_divisors
      (Y := M) shape.2 hdegree

theorem card_rightFixedSquareClassFiber_degree_two_one
    {N M A L K base d : ℕ} (hN : 2 ≤ N)
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (hdegree : shape.1.card = 2)
    (heq : rightNormalizedCoefficient shape base d = 1) :
    (rightFixedSquareClassFiber
        N M A L K base shape d).card ≤
      (Int.divisorsAntidiag
        ((offsetShiftOfCard shape.1 hdegree 0 -
          offsetShiftOfCard shape.1 hdegree 1) ^ 2)).card := by
  apply card_rightFixedSquareClassFiber_le hN shape
  simpa only [heq] using
    offsetProductNatFiber_degree_two_one_atMost_divisors
      (Y := M) shape.1 hdegree

/--
Complete finite degree-two bound for a left-oriented fixed-base/fixed-shape
fibre.  The exceptional coefficient `1` is discharged by divisors; all
other squarefree coefficients use exactly the supplied Pell-box counts.
-/
theorem card_leftBaseShapeFiber_degree_two_of_pell_boxes
    {N M A L K base : ℕ} (hN : 2 ≤ N)
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (hdegree : shape.2.card = 2)
    (Q : ℕ → ℕ)
    (hPell :
      ∀ d ∈ squarefreeSmoothUpTo
          (L + 1) (boundedRatioCutoff M L ^ K),
        leftNormalizedCoefficient shape base d ≠ 1 →
        PellInput.HasAtMostSolutionsReal
          (PellInput.pellBox
            1
            (leftNormalizedCoefficient shape base d)
            ((offsetShiftOfCard shape.2 hdegree 0 -
              offsetShiftOfCard shape.2 hdegree 1) ^ 2)
            (degreeTwoPellHeight M L))
          (Q d : ℝ)) :
    (leftBaseShapeFiber N M A L K base shape).card ≤
      ∑ d ∈ squarefreeSmoothUpTo
          (L + 1) (boundedRatioCutoff M L ^ K),
        if leftNormalizedCoefficient shape base d = 1 then
          (Int.divisorsAntidiag
            ((offsetShiftOfCard shape.2 hdegree 0 -
              offsetShiftOfCard shape.2 hdegree 1) ^ 2)).card
        else Q d := by
  apply card_leftBaseShapeFiber_le_sum_fixedSquareClassCounts
    hN shape
  intro d hd
  by_cases heq :
      leftNormalizedCoefficient shape base d = 1
  · simp only [heq, if_pos]
    simpa only [heq] using
      offsetProductNatFiber_degree_two_one_atMost_divisors
        (Y := M) shape.2 hdegree
  · rw [if_neg heq]
    change HasAtMostSolutions
      (offsetProductNatFiber shape.2
        (squarefreeKernel (d * shapeLeftProduct shape (base + 1))) M)
      (Q d)
    exact offsetProductNatFiber_degree_two_atMost_of_pell
      shape.2 hdegree (hPell d hd heq)

/-- Symmetric complete finite degree-two bound. -/
theorem card_rightBaseShapeFiber_degree_two_of_pell_boxes
    {N M A L K base : ℕ} (hN : 2 ≤ N)
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (hdegree : shape.1.card = 2)
    (Q : ℕ → ℕ)
    (hPell :
      ∀ d ∈ squarefreeSmoothUpTo
          (L + 1) (boundedRatioCutoff M L ^ K),
        rightNormalizedCoefficient shape base d ≠ 1 →
        PellInput.HasAtMostSolutionsReal
          (PellInput.pellBox
            1
            (rightNormalizedCoefficient shape base d)
            ((offsetShiftOfCard shape.1 hdegree 0 -
              offsetShiftOfCard shape.1 hdegree 1) ^ 2)
            (degreeTwoPellHeight M L))
          (Q d : ℝ)) :
    (rightBaseShapeFiber N M A L K base shape).card ≤
      ∑ d ∈ squarefreeSmoothUpTo
          (L + 1) (boundedRatioCutoff M L ^ K),
        if rightNormalizedCoefficient shape base d = 1 then
          (Int.divisorsAntidiag
            ((offsetShiftOfCard shape.1 hdegree 0 -
              offsetShiftOfCard shape.1 hdegree 1) ^ 2)).card
        else Q d := by
  apply card_rightBaseShapeFiber_le_sum_fixedSquareClassCounts
    hN shape
  intro d hd
  by_cases heq :
      rightNormalizedCoefficient shape base d = 1
  · simp only [heq, if_pos]
    simpa only [heq] using
      offsetProductNatFiber_degree_two_one_atMost_divisors
        (Y := M) shape.1 hdegree
  · rw [if_neg heq]
    change HasAtMostSolutions
      (offsetProductNatFiber shape.1
        (squarefreeKernel (d * shapeRightProduct shape (base + 1))) M)
      (Q d)
    exact offsetProductNatFiber_degree_two_atMost_of_pell
      shape.1 hdegree (hPell d hd heq)

/--
Direct generalized-Pell closure of the left degree-two branch.  Its three
uniform premises are precisely the finite polynomial-height invariant still
to be discharged when the fixed fibres are assembled in Lemma 17.26.
-/
theorem card_leftBaseShapeFiber_degree_two_of_generalizedPell
    (hPell :
      PellInput.GeneralizedPellPolynomialBoxStatement) :
    ∀ E : ℕ, 0 < E →
      ∃ c : ℝ, 0 ≤ c ∧
        ∃ X₀ : ℕ, ∀ X ≥ X₀,
          ∀ (N M A L K base : ℕ)
            (shape :
              Finset (Fin (L + 1)) × Finset (Fin (L + 1))),
          2 ≤ N →
          (hdegree : shape.2.card = 2) →
          (∀ d ∈ squarefreeSmoothUpTo
              (L + 1) (boundedRatioCutoff M L ^ K),
            leftNormalizedCoefficient shape base d ≤ X ^ E) →
          ((offsetShiftOfCard shape.2 hdegree 0 -
            offsetShiftOfCard shape.2 hdegree 1) ^ 2).natAbs ≤
              X ^ E →
          degreeTwoPellHeight M L ≤ X ^ E →
          (leftBaseShapeFiber
              N M A L K base shape).card ≤
            ∑ d ∈ squarefreeSmoothUpTo
                (L + 1) (boundedRatioCutoff M L ^ K),
              if leftNormalizedCoefficient shape base d = 1 then
                (Int.divisorsAntidiag
                  ((offsetShiftOfCard shape.2 hdegree 0 -
                    offsetShiftOfCard shape.2 hdegree 1) ^ 2)).card
              else
                ⌈PellInput.expLogLogBound c X⌉₊ := by
  intro E hE
  obtain ⟨c, hc, X₀, hX₀⟩ :=
    offsetProductNatFiber_degree_two_polynomialBox_of_generalizedPell
      hPell E hE
  refine ⟨c, hc, X₀, ?_⟩
  intro X hX N M A L K base shape hN hdegree
    hcoefficient hdelta hheight
  apply card_leftBaseShapeFiber_le_sum_fixedSquareClassCounts
    hN shape
  intro d hd
  by_cases heq :
      leftNormalizedCoefficient shape base d = 1
  · simp only [heq, if_pos]
    simpa only [heq] using
      offsetProductNatFiber_degree_two_one_atMost_divisors
        (Y := M) shape.2 hdegree
  · rw [if_neg heq]
    have hePos :
        0 < leftNormalizedCoefficient shape base d :=
      leftNormalizedCoefficient_pos shape base d
    have heTwo :
        2 ≤ leftNormalizedCoefficient shape base d := by
      omega
    change HasAtMostSolutions
      (offsetProductNatFiber shape.2
        (squarefreeKernel (d * shapeLeftProduct shape (base + 1))) M)
      ⌈PellInput.expLogLogBound c X⌉₊
    exact hX₀ X hX L shape.2 hdegree
      (shapeLeftProduct shape (base + 1)) d M
      heTwo (hcoefficient d hd) hdelta hheight

/-- Symmetric direct generalized-Pell closure. -/
theorem card_rightBaseShapeFiber_degree_two_of_generalizedPell
    (hPell :
      PellInput.GeneralizedPellPolynomialBoxStatement) :
    ∀ E : ℕ, 0 < E →
      ∃ c : ℝ, 0 ≤ c ∧
        ∃ X₀ : ℕ, ∀ X ≥ X₀,
          ∀ (N M A L K base : ℕ)
            (shape :
              Finset (Fin (L + 1)) × Finset (Fin (L + 1))),
          2 ≤ N →
          (hdegree : shape.1.card = 2) →
          (∀ d ∈ squarefreeSmoothUpTo
              (L + 1) (boundedRatioCutoff M L ^ K),
            rightNormalizedCoefficient shape base d ≤ X ^ E) →
          ((offsetShiftOfCard shape.1 hdegree 0 -
            offsetShiftOfCard shape.1 hdegree 1) ^ 2).natAbs ≤
              X ^ E →
          degreeTwoPellHeight M L ≤ X ^ E →
          (rightBaseShapeFiber
              N M A L K base shape).card ≤
            ∑ d ∈ squarefreeSmoothUpTo
                (L + 1) (boundedRatioCutoff M L ^ K),
              if rightNormalizedCoefficient shape base d = 1 then
                (Int.divisorsAntidiag
                  ((offsetShiftOfCard shape.1 hdegree 0 -
                    offsetShiftOfCard shape.1 hdegree 1) ^ 2)).card
              else
                ⌈PellInput.expLogLogBound c X⌉₊ := by
  intro E hE
  obtain ⟨c, hc, X₀, hX₀⟩ :=
    offsetProductNatFiber_degree_two_polynomialBox_of_generalizedPell
      hPell E hE
  refine ⟨c, hc, X₀, ?_⟩
  intro X hX N M A L K base shape hN hdegree
    hcoefficient hdelta hheight
  apply card_rightBaseShapeFiber_le_sum_fixedSquareClassCounts
    hN shape
  intro d hd
  by_cases heq :
      rightNormalizedCoefficient shape base d = 1
  · simp only [heq, if_pos]
    simpa only [heq] using
      offsetProductNatFiber_degree_two_one_atMost_divisors
        (Y := M) shape.1 hdegree
  · rw [if_neg heq]
    have hePos :
        0 < rightNormalizedCoefficient shape base d :=
      rightNormalizedCoefficient_pos shape base d
    have heTwo :
        2 ≤ rightNormalizedCoefficient shape base d := by
      omega
    change HasAtMostSolutions
      (offsetProductNatFiber shape.1
        (squarefreeKernel (d * shapeRightProduct shape (base + 1))) M)
      ⌈PellInput.expLogLogBound c X⌉₊
    exact hX₀ X hX L shape.1 hdegree
      (shapeRightProduct shape (base + 1)) d M
      heTwo (hcoefficient d hd) hdelta hheight

/-! ### Automatic polynomial-height bookkeeping on actual fibres -/

private theorem leftNormalizedCoefficient_le_cutoff_pow_two_mul_of_mem
    {N M A L K base d : ℕ} (hN : 2 ≤ N)
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈ leftBaseShapeFiber
        N M A L K base shape)
    (hdPos : 0 < d)
    (hdBound : d ≤ boundedRatioCutoff M L ^ K) :
    leftNormalizedCoefficient shape base d ≤
      boundedRatioCutoff M L ^ (2 * K) := by
  have hbaseData := mem_leftBaseShapeFiber.mp hpair
  rcases
      (mem_boundedComponentHostsOfShape.mp hbaseData.1).2 with
    ⟨C, hC, hcard, hleft, _hright⟩
  have hxEq :
      pair.1.1 = base + 1 :=
    first_eq_base_succ hN hbaseData.2
  have hvertexCard :
      (LargePrimeComponents.componentVertices
        pair.1.1 pair.1.2 L C).card ≤ K := by
    rw [ComponentProductParity.card_componentVertices]
    exact hcard
  have hproductShape :
      componentLeftProduct
          pair.1.1 pair.1.2 L C =
        shapeLeftProduct shape (base + 1) := by
    rw [componentLeftProduct_eq_offsetProduct, hleft, hxEq]
    rfl
  have hproductBound :
      shapeLeftProduct shape (base + 1) ≤
        boundedRatioCutoff M L ^ K := by
    rw [← hproductShape]
    exact componentLeftProduct_le_cutoff_pow
      hN pair C hvertexCard
  have hproductPos :
      0 < shapeLeftProduct shape (base + 1) := by
    rw [← hproductShape]
    exact componentLeftProduct_pos
      (pair_coordinates_two_le hN pair).1 C
  unfold leftNormalizedCoefficient
  calc
    squarefreeKernel
        (d * shapeLeftProduct shape (base + 1)) ≤
        d * shapeLeftProduct shape (base + 1) :=
      squarefreeKernel_le (Nat.mul_pos hdPos hproductPos)
    _ ≤
        boundedRatioCutoff M L ^ K *
          boundedRatioCutoff M L ^ K :=
      Nat.mul_le_mul hdBound hproductBound
    _ = boundedRatioCutoff M L ^ (2 * K) := by
      rw [← pow_add]
      congr 1
      omega

private theorem rightNormalizedCoefficient_le_cutoff_pow_two_mul_of_mem
    {N M A L K base d : ℕ} (hN : 2 ≤ N)
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    {pair : SeparatedBoundedRatioPair N M L}
    (hpair :
      pair ∈ rightBaseShapeFiber
        N M A L K base shape)
    (hdPos : 0 < d)
    (hdBound : d ≤ boundedRatioCutoff M L ^ K) :
    rightNormalizedCoefficient shape base d ≤
      boundedRatioCutoff M L ^ (2 * K) := by
  have hbaseData := mem_rightBaseShapeFiber.mp hpair
  rcases
      (mem_boundedComponentHostsOfShape.mp hbaseData.1).2 with
    ⟨C, hC, hcard, _hleft, hright⟩
  have hyEq :
      pair.1.2 = base + 1 :=
    second_eq_base_succ hN hbaseData.2
  have hvertexCard :
      (LargePrimeComponents.componentVertices
        pair.1.1 pair.1.2 L C).card ≤ K := by
    rw [ComponentProductParity.card_componentVertices]
    exact hcard
  have hproductShape :
      componentRightProduct
          pair.1.1 pair.1.2 L C =
        shapeRightProduct shape (base + 1) := by
    rw [componentRightProduct_eq_offsetProduct, hright, hyEq]
    rfl
  have hproductBound :
      shapeRightProduct shape (base + 1) ≤
        boundedRatioCutoff M L ^ K := by
    rw [← hproductShape]
    exact componentRightProduct_le_cutoff_pow
      hN pair C hvertexCard
  have hproductPos :
      0 < shapeRightProduct shape (base + 1) := by
    rw [← hproductShape]
    exact componentRightProduct_pos
      (pair_coordinates_two_le hN pair).2 C
  unfold rightNormalizedCoefficient
  calc
    squarefreeKernel
        (d * shapeRightProduct shape (base + 1)) ≤
        d * shapeRightProduct shape (base + 1) :=
      squarefreeKernel_le (Nat.mul_pos hdPos hproductPos)
    _ ≤
        boundedRatioCutoff M L ^ K *
          boundedRatioCutoff M L ^ K :=
      Nat.mul_le_mul hdBound hproductBound
    _ = boundedRatioCutoff M L ^ (2 * K) := by
      rw [← pow_add]
      congr 1
      omega

private theorem three_le_boundedRatioCutoff_of_pair
    {N M L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) :
    3 ≤ boundedRatioCutoff M L := by
  have hpair :=
    mem_separatedBoundedRatioPairs.mp pair.2
  have hxData :=
    BoundedRatioGeometry.mem_boundedRatioBlock.mp hpair.1
  have hxTwo : 2 ≤ pair.1.1 :=
    hN.trans hxData.1
  have hxM : pair.1.1 < M := hxData.2
  have hMthree : 3 ≤ M := by omega
  unfold boundedRatioCutoff
  omega

private theorem degreeTwoPellHeight_le_cutoff_pow_of_pair
    {N M L E : ℕ} (hN : 2 ≤ N)
    (hE : 4 ≤ E)
    (pair : SeparatedBoundedRatioPair N M L) :
    degreeTwoPellHeight M L ≤
      boundedRatioCutoff M L ^ E := by
  let X := boundedRatioCutoff M L
  have hXthree : 3 ≤ X :=
    three_le_boundedRatioCutoff_of_pair hN pair
  have hMLe : M + L + 1 = X + 1 := by
    rfl
  have hplus : X + 1 ≤ 2 * X := by omega
  have hpowTwo : 8 ≤ X ^ 2 := by
    calc
      8 ≤ 3 ^ 2 := by norm_num
      _ ≤ X ^ 2 := Nat.pow_le_pow_left hXthree 2
  calc
    degreeTwoPellHeight M L =
        2 * (X + 1) ^ 2 := by
      unfold degreeTwoPellHeight
      rw [hMLe]
    _ ≤ 2 * (2 * X) ^ 2 :=
      Nat.mul_le_mul_left 2
        (Nat.pow_le_pow_left hplus 2)
    _ = 8 * X ^ 2 := by ring
    _ ≤ X ^ 2 * X ^ 2 :=
      Nat.mul_le_mul_right (X ^ 2) hpowTwo
    _ = X ^ 4 := by ring
    _ ≤ X ^ E :=
      Nat.pow_le_pow_right (by omega) hE

private theorem offsetDiscriminant_le_cutoff_pow_of_pair
    {N M L E : ℕ} (hN : 2 ≤ N)
    (hE : 4 ≤ E)
    (pair : SeparatedBoundedRatioPair N M L)
    (offsets : Finset (Fin (L + 1)))
    (hdegree : offsets.card = 2) :
    ((offsetShiftOfCard offsets hdegree 0 -
      offsetShiftOfCard offsets hdegree 1) ^ 2).natAbs ≤
        boundedRatioCutoff M L ^ E := by
  let X := boundedRatioCutoff M L
  let Δ :=
    offsetShiftOfCard offsets hdegree 0 -
      offsetShiftOfCard offsets hdegree 1
  have hXthree : 3 ≤ X :=
    three_le_boundedRatioCutoff_of_pair hN pair
  have hshiftZero :=
    offsetShiftOfCard_natAbs_le offsets hdegree (0 : Fin 2)
  have hshiftOne :=
    offsetShiftOfCard_natAbs_le offsets hdegree (1 : Fin 2)
  have hdelta :
      Δ.natAbs ≤ 2 * (L + 1) := by
    calc
      Δ.natAbs ≤
          (offsetShiftOfCard offsets hdegree 0).natAbs +
            (offsetShiftOfCard offsets hdegree 1).natAbs :=
        Int.natAbs_sub_le _ _
      _ ≤ 2 * (L + 1) := by omega
  have hLX : L + 1 ≤ X := by
    have hpair :=
      mem_separatedBoundedRatioPairs.mp pair.2
    have hxData :=
      BoundedRatioGeometry.mem_boundedRatioBlock.mp hpair.1
    have hxTwo : 2 ≤ pair.1.1 :=
      hN.trans hxData.1
    have hxM : pair.1.1 < M := hxData.2
    dsimp only [X]
    unfold boundedRatioCutoff
    omega
  have hdeltaX : Δ.natAbs ≤ 2 * X :=
    hdelta.trans (Nat.mul_le_mul_left 2 hLX)
  have hpowTwo : 4 ≤ X ^ 2 := by
    calc
      4 ≤ 3 ^ 2 := by norm_num
      _ ≤ X ^ 2 := Nat.pow_le_pow_left hXthree 2
  calc
    (Δ ^ 2).natAbs = Δ.natAbs ^ 2 := by
      rw [Int.natAbs_pow]
    _ ≤ (2 * X) ^ 2 :=
      Nat.pow_le_pow_left hdeltaX 2
    _ = 4 * X ^ 2 := by ring
    _ ≤ X ^ 2 * X ^ 2 :=
      Nat.mul_le_mul_right (X ^ 2) hpowTwo
    _ = X ^ 4 := by ring
    _ ≤ X ^ E :=
      Nat.pow_le_pow_right (by omega) hE

/--
On an actual nonempty left fixed fibre all three polynomial-height
premises above are automatic.  Thus, for any fixed exponent
`E ≥ max 4 (2K)`, the degree-two branch is completely reduced to the
registered generalized-Pell input and the explicit divisor term.
-/
theorem card_leftBaseShapeFiber_degree_two_polynomial_of_generalizedPell
    (hPell :
      PellInput.GeneralizedPellPolynomialBoxStatement)
    {K E : ℕ} (hEPos : 0 < E)
    (hEFour : 4 ≤ E) (hEK : 2 * K ≤ E) :
    ∃ c : ℝ, 0 ≤ c ∧
      ∃ X₀ : ℕ,
        ∀ (N M A L base : ℕ)
          (shape :
            Finset (Fin (L + 1)) × Finset (Fin (L + 1))),
        2 ≤ N →
        (hdegree : shape.2.card = 2) →
        X₀ ≤ boundedRatioCutoff M L →
        (leftBaseShapeFiber
            N M A L K base shape).card ≤
          ∑ d ∈ squarefreeSmoothUpTo
              (L + 1) (boundedRatioCutoff M L ^ K),
            if leftNormalizedCoefficient shape base d = 1 then
              (Int.divisorsAntidiag
                ((offsetShiftOfCard shape.2 hdegree 0 -
                  offsetShiftOfCard shape.2 hdegree 1) ^ 2)).card
            else
              ⌈PellInput.expLogLogBound c
                (boundedRatioCutoff M L)⌉₊ := by
  obtain ⟨c, hc, X₀, hX₀⟩ :=
    card_leftBaseShapeFiber_degree_two_of_generalizedPell
      hPell E hEPos
  refine ⟨c, hc, X₀, ?_⟩
  intro N M A L base shape hN hdegree hcutoff
  by_cases hempty :
      leftBaseShapeFiber N M A L K base shape = ∅
  · rw [hempty]
    simp
  · obtain ⟨pair, hpair⟩ :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    have hcutoffOne :
        1 ≤ boundedRatioCutoff M L :=
      (three_le_boundedRatioCutoff_of_pair hN pair).trans'
        (by norm_num)
    have hcoefficient :
        ∀ d ∈ squarefreeSmoothUpTo
            (L + 1) (boundedRatioCutoff M L ^ K),
          leftNormalizedCoefficient shape base d ≤
            boundedRatioCutoff M L ^ E := by
      intro d hd
      have hdData := mem_squarefreeSmoothUpTo.mp hd
      exact
        (leftNormalizedCoefficient_le_cutoff_pow_two_mul_of_mem
          hN shape hpair hdData.1 hdData.2.1).trans
          (Nat.pow_le_pow_right hcutoffOne hEK)
    exact hX₀
      (boundedRatioCutoff M L) hcutoff
      N M A L K base shape hN hdegree
      hcoefficient
      (offsetDiscriminant_le_cutoff_pow_of_pair
        hN hEFour pair shape.2 hdegree)
      (degreeTwoPellHeight_le_cutoff_pow_of_pair
        hN hEFour pair)

/-- Symmetric automatic polynomial-height closure. -/
theorem card_rightBaseShapeFiber_degree_two_polynomial_of_generalizedPell
    (hPell :
      PellInput.GeneralizedPellPolynomialBoxStatement)
    {K E : ℕ} (hEPos : 0 < E)
    (hEFour : 4 ≤ E) (hEK : 2 * K ≤ E) :
    ∃ c : ℝ, 0 ≤ c ∧
      ∃ X₀ : ℕ,
        ∀ (N M A L base : ℕ)
          (shape :
            Finset (Fin (L + 1)) × Finset (Fin (L + 1))),
        2 ≤ N →
        (hdegree : shape.1.card = 2) →
        X₀ ≤ boundedRatioCutoff M L →
        (rightBaseShapeFiber
            N M A L K base shape).card ≤
          ∑ d ∈ squarefreeSmoothUpTo
              (L + 1) (boundedRatioCutoff M L ^ K),
            if rightNormalizedCoefficient shape base d = 1 then
              (Int.divisorsAntidiag
                ((offsetShiftOfCard shape.1 hdegree 0 -
                  offsetShiftOfCard shape.1 hdegree 1) ^ 2)).card
            else
              ⌈PellInput.expLogLogBound c
                (boundedRatioCutoff M L)⌉₊ := by
  obtain ⟨c, hc, X₀, hX₀⟩ :=
    card_rightBaseShapeFiber_degree_two_of_generalizedPell
      hPell E hEPos
  refine ⟨c, hc, X₀, ?_⟩
  intro N M A L base shape hN hdegree hcutoff
  by_cases hempty :
      rightBaseShapeFiber N M A L K base shape = ∅
  · rw [hempty]
    simp
  · obtain ⟨pair, hpair⟩ :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    have hcutoffOne :
        1 ≤ boundedRatioCutoff M L :=
      (three_le_boundedRatioCutoff_of_pair hN pair).trans'
        (by norm_num)
    have hcoefficient :
        ∀ d ∈ squarefreeSmoothUpTo
            (L + 1) (boundedRatioCutoff M L ^ K),
          rightNormalizedCoefficient shape base d ≤
            boundedRatioCutoff M L ^ E := by
      intro d hd
      have hdData := mem_squarefreeSmoothUpTo.mp hd
      exact
        (rightNormalizedCoefficient_le_cutoff_pow_two_mul_of_mem
          hN shape hpair hdData.1 hdData.2.1).trans
          (Nat.pow_le_pow_right hcutoffOne hEK)
    exact hX₀
      (boundedRatioCutoff M L) hcutoff
      N M A L K base shape hN hdegree
      hcoefficient
      (offsetDiscriminant_le_cutoff_pow_of_pair
        hN hEFour pair shape.1 hdegree)
      (degreeTwoPellHeight_le_cutoff_pow_of_pair
        hN hEFour pair)

/-! ## Degree at least three maps to the existing ES count -/

theorem offsetProductNatFiber_atMost_of_evertseSilverman
    (hES : EvertseSilvermanAbscissaStatement)
    {L P d Y : ℕ}
    (offsets : Finset (Fin (L + 1)))
    (hdegree : 3 ≤ offsets.card)
    (hP : 0 < P) (hd : 0 < d) :
    HasAtMostSolutions
      (offsetProductNatFiber offsets
        (squarefreeKernel (d * P)) Y)
      (offsets.card +
        explicitBound (offsetShift offsets)
          (squarefreeKernel (d * P) : ℤ)) := by
  have hcount :=
    normalizedShiftedEquation_atMost_of_evertseSilverman
      hES (offsetShift offsets) hdegree
      (offsetShift_injective offsets) hP hd
  intro s hs
  let f : ℕ × ℕ → ℤ × ℤ := natSolutionToInt
  have himage :
      ∀ solution ∈ s.image f,
        normalizedShiftedEquation
          P d (offsetShift offsets) solution := by
    intro solution hsolution
    obtain ⟨source, hsource, rfl⟩ :=
      Finset.mem_image.mp hsolution
    have hdata := hs source hsource
    have hsourceOne : 1 ≤ source.1 := by
      have hsourceTwo : 2 ≤ source.1 := hdata.1
      omega
    unfold normalizedShiftedEquation shiftedSquareEquation
    change
      shiftedProduct (offsetShift offsets) (source.1 : ℤ) =
        (squarefreeKernel (d * P) : ℤ) * (source.2 : ℤ) ^ 2
    rw [shiftedProduct_offsetShift
      hsourceOne offsets]
    exact_mod_cast hdata.2.2
  have hbound := hcount (s.image f) himage
  simpa only [f, Finset.card_image_of_injective _
    natSolutionToInt_injective] using hbound

theorem card_leftFixedSquareClassFiber_degree_at_least_three
    (hES : EvertseSilvermanAbscissaStatement)
    {N M A L K base d : ℕ} (hN : 2 ≤ N)
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (hdegree : 3 ≤ shape.2.card)
    (hbase : 2 ≤ base + 1) (hd : 0 < d) :
    (leftFixedSquareClassFiber
        N M A L K base shape d).card ≤
      shape.2.card +
        explicitBound (offsetShift shape.2)
          (leftNormalizedCoefficient shape base d : ℤ) := by
  apply card_leftFixedSquareClassFiber_le hN shape
  have hP :
      0 < shapeLeftProduct shape (base + 1) := by
    unfold shapeLeftProduct
    exact Finset.prod_pos fun i hi =>
      RationalChannelCode.startCompleteVertexLabel_pos
        hbase i
  simpa only [leftNormalizedCoefficient] using
    offsetProductNatFiber_atMost_of_evertseSilverman
      hES shape.2 hdegree hP hd

theorem card_rightFixedSquareClassFiber_degree_at_least_three
    (hES : EvertseSilvermanAbscissaStatement)
    {N M A L K base d : ℕ} (hN : 2 ≤ N)
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (hdegree : 3 ≤ shape.1.card)
    (hbase : 2 ≤ base + 1) (hd : 0 < d) :
    (rightFixedSquareClassFiber
        N M A L K base shape d).card ≤
      shape.1.card +
        explicitBound (offsetShift shape.1)
          (rightNormalizedCoefficient shape base d : ℤ) := by
  apply card_rightFixedSquareClassFiber_le hN shape
  have hP :
      0 < shapeRightProduct shape (base + 1) := by
    unfold shapeRightProduct
    exact Finset.prod_pos fun i hi =>
      RationalChannelCode.startCompleteVertexLabel_pos
        hbase i
  simpa only [rightNormalizedCoefficient] using
    offsetProductNatFiber_atMost_of_evertseSilverman
      hES shape.1 hdegree hP hd

/--
Complete finite ES bound for a left-oriented fixed-base/fixed-shape fibre.
The only remaining work in this branch is to bound this explicit finite sum
uniformly by `N^o(1)`.
-/
theorem card_leftBaseShapeFiber_degree_at_least_three
    (hES : EvertseSilvermanAbscissaStatement)
    {N M A L K base : ℕ} (hN : 2 ≤ N)
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (hdegree : 3 ≤ shape.2.card)
    (hbase : 2 ≤ base + 1) :
    (leftBaseShapeFiber N M A L K base shape).card ≤
      ∑ d ∈ squarefreeSmoothUpTo
          (L + 1) (boundedRatioCutoff M L ^ K),
        (shape.2.card +
          explicitBound (offsetShift shape.2)
            (leftNormalizedCoefficient shape base d : ℤ)) := by
  apply card_leftBaseShapeFiber_le_sum_fixedSquareClassCounts
    hN shape
    (fun d =>
      shape.2.card +
        explicitBound (offsetShift shape.2)
          (leftNormalizedCoefficient shape base d : ℤ))
  intro d hd
  have hdPos :=
    (mem_squarefreeSmoothUpTo.mp hd).1
  have hP :
      0 < shapeLeftProduct shape (base + 1) := by
    unfold shapeLeftProduct
    exact Finset.prod_pos fun i hi =>
      RationalChannelCode.startCompleteVertexLabel_pos hbase i
  simpa only [leftNormalizedCoefficient] using
    offsetProductNatFiber_atMost_of_evertseSilverman
      hES shape.2 hdegree hP hdPos

/-- Symmetric complete finite ES bound. -/
theorem card_rightBaseShapeFiber_degree_at_least_three
    (hES : EvertseSilvermanAbscissaStatement)
    {N M A L K base : ℕ} (hN : 2 ≤ N)
    (shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1)))
    (hdegree : 3 ≤ shape.1.card)
    (hbase : 2 ≤ base + 1) :
    (rightBaseShapeFiber N M A L K base shape).card ≤
      ∑ d ∈ squarefreeSmoothUpTo
          (L + 1) (boundedRatioCutoff M L ^ K),
        (shape.1.card +
          explicitBound (offsetShift shape.1)
            (rightNormalizedCoefficient shape base d : ℤ)) := by
  apply card_rightBaseShapeFiber_le_sum_fixedSquareClassCounts
    hN shape
    (fun d =>
      shape.1.card +
        explicitBound (offsetShift shape.1)
          (rightNormalizedCoefficient shape base d : ℤ))
  intro d hd
  have hdPos :=
    (mem_squarefreeSmoothUpTo.mp hd).1
  have hP :
      0 < shapeRightProduct shape (base + 1) := by
    unfold shapeRightProduct
    exact Finset.prod_pos fun i hi =>
      RationalChannelCode.startCompleteVertexLabel_pos hbase i
  simpa only [rightNormalizedCoefficient] using
    offsetProductNatFiber_atMost_of_evertseSilverman
      hES shape.1 hdegree hP hdPos

end

end BoundedRatioManyDefectsFixedFibers
end PaperC
