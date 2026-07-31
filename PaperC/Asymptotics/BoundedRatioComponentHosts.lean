import PaperC.Asymptotics.BoundedRatioComponentNormalization
import PaperC.Coding.HammingBound
import PaperC.Combinatorics.DeepCoreSmallComponent

set_option maxHeartbeats 3600000

/-!
# Hosts of a bounded canonical component on a bounded-ratio interval

This file develops the finite part of Lemmas 17.23--17.24.  A host is a
separated bounded-ratio pair carrying a canonical residual component on at
most `K` occurrences.  For such a component Lean records:

* nonzero left and right degrees;
* its two finite sets of signed offsets;
* a polynomial-size container for all possible offset shapes when `K` is
  fixed;
* the normalized shifted-product equation furnished by
  `BoundedRatioComponentNormalization`.

The final counting step is kept as an explicit theorem parameter rather
than packaged as a new arithmetic statement.  In particular this module
introduces no bridge or opaque host-count predicate.
-/

namespace PaperC
namespace BoundedRatioComponentHosts

open scoped BigOperators
open Affine
open AlignedComponentCode
open BoundedRatioComponentNormalization
open CanonicalResidualComponents
open ComponentProductParity
open EvertseSilvermanInput
open LargePrimeComponents
open LargePrimeGraph
open LargePrimeGraphResolution
open LargePrimeOccurrences
open PropositionSixteenOne
open ResidualComponentCounts

noncomputable section

noncomputable local instance instDecidableLargePrimeAdj
    (x y L : ℕ) :
    DecidableRel (largePrimeGraph x y L).Adj :=
  Classical.decRel _

/-! ## The two finite offset sets of a component -/

/-- Left offsets occurring in a connected component. -/
noncomputable def componentLeftOffsets
    (x y L : ℕ)
    (C : (largePrimeGraph x y L).ConnectedComponent) :
    Finset (Fin (L + 1)) :=
  Finset.univ.filter fun i =>
    (Sum.inl i : Occurrence L) ∈ componentVertices x y L C

/-- Right offsets occurring in a connected component. -/
noncomputable def componentRightOffsets
    (x y L : ℕ)
    (C : (largePrimeGraph x y L).ConnectedComponent) :
    Finset (Fin (L + 1)) :=
  Finset.univ.filter fun j =>
    (Sum.inr j : Occurrence L) ∈ componentVertices x y L C

@[simp]
theorem mem_componentLeftOffsets
    {x y L : ℕ}
    {C : (largePrimeGraph x y L).ConnectedComponent}
    {i : Fin (L + 1)} :
    i ∈ componentLeftOffsets x y L C ↔
      (Sum.inl i : Occurrence L) ∈ componentVertices x y L C := by
  simp [componentLeftOffsets]

@[simp]
theorem mem_componentRightOffsets
    {x y L : ℕ}
    {C : (largePrimeGraph x y L).ConnectedComponent}
    {j : Fin (L + 1)} :
    j ∈ componentRightOffsets x y L C ↔
      (Sum.inr j : Occurrence L) ∈ componentVertices x y L C := by
  simp [componentRightOffsets]

/-- The left offset set has the graph-theoretic left degree. -/
theorem card_componentLeftOffsets
    (x y L : ℕ)
    (C : (largePrimeGraph x y L).ConnectedComponent) :
    (componentLeftOffsets x y L C).card =
      componentLeftCount x y L C := by
  classical
  unfold componentLeftCount
  refine Finset.card_bij
    (fun i _hi => (Sum.inl i : Occurrence L)) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, IsLeftOccurrence, and_true]
    exact mem_componentLeftOffsets.mp hi
  · intro i _hi j _hj hij
    exact Sum.inl.inj hij
  · intro v hv
    have hv' := Finset.mem_filter.mp hv
    cases v with
    | inl i =>
        refine ⟨i, mem_componentLeftOffsets.mpr hv'.1, rfl⟩
    | inr j =>
        simp [IsLeftOccurrence] at hv'

/-- The right offset set has the graph-theoretic right degree. -/
theorem card_componentRightOffsets
    (x y L : ℕ)
    (C : (largePrimeGraph x y L).ConnectedComponent) :
    (componentRightOffsets x y L C).card =
      componentRightCount x y L C := by
  classical
  unfold componentRightCount
  refine Finset.card_bij
    (fun j _hj => (Sum.inr j : Occurrence L)) ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, IsRightOccurrence, and_true]
    exact mem_componentRightOffsets.mp hj
  · intro i _hi j _hj hij
    exact Sum.inr.inj hij
  · intro v hv
    have hv' := Finset.mem_filter.mp hv
    cases v with
    | inl i =>
        simp [IsRightOccurrence] at hv'
    | inr j =>
        refine ⟨j, mem_componentRightOffsets.mpr hv'.1, rfl⟩

/-- Both offset sets of a canonical residual component are nonempty. -/
theorem componentOffsets_nonempty
    {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L)
    {C : (largePrimeGraph pair.1.1 pair.1.2 L).ConnectedComponent}
    (hC : C ∈ canonicalResidualComponents
      A pair.1.1 pair.1.2 L) :
    (componentLeftOffsets pair.1.1 pair.1.2 L C).Nonempty ∧
      (componentRightOffsets pair.1.1 pair.1.2 L C).Nonempty := by
  have hcoords := pair_coordinates_two_le hN pair
  have hnontrivial :=
    isNontrivialUnpinnedComponent_of_mem_canonicalResidualComponents hC
  have hleft :=
    one_le_componentLeftCount
      (show 1 ≤ pair.1.1 by omega)
      (show 1 ≤ pair.1.2 by omega) C hnontrivial
  have hright :=
    one_le_componentRightCount
      (show 1 ≤ pair.1.1 by omega)
      (show 1 ≤ pair.1.2 by omega) C hnontrivial
  rw [← card_componentLeftOffsets] at hleft
  rw [← card_componentRightOffsets] at hright
  exact
    ⟨Finset.card_pos.mp (by omega),
      Finset.card_pos.mp (by omega)⟩

/-- The total number of offsets is exactly the support size. -/
theorem card_componentOffsets
    (x y L : ℕ)
    (C : (largePrimeGraph x y L).ConnectedComponent) :
    (componentLeftOffsets x y L C).card +
        (componentRightOffsets x y L C).card =
      Fintype.card C.supp := by
  rw [card_componentLeftOffsets, card_componentRightOffsets,
    componentLeftCount_add_rightCount,
    card_componentVertices]

/-! ## A finite polynomial-size container of offset shapes -/

/--
All ordered pairs of nonempty offset subsets whose total size is at most
`K`.  Every component host of size at most `K` has a shape in this finite
container.
-/
noncomputable def boundedOffsetShapes
    (L K : ℕ) :
    Finset (Finset (Fin (L + 1)) × Finset (Fin (L + 1))) :=
  ((HammingBound.smallSupports (L + 1) K).product
      (HammingBound.smallSupports (L + 1) K)).filter fun shape =>
    shape.1.Nonempty ∧ shape.2.Nonempty ∧
      shape.1.card + shape.2.card ≤ K

@[simp]
theorem mem_boundedOffsetShapes
    {L K : ℕ}
    {shape : Finset (Fin (L + 1)) × Finset (Fin (L + 1))} :
    shape ∈ boundedOffsetShapes L K ↔
      shape.1.Nonempty ∧ shape.2.Nonempty ∧
        shape.1.card + shape.2.card ≤ K := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨?_, h⟩
    change shape ∈
      (HammingBound.smallSupports (L + 1) K) ×ˢ
        (HammingBound.smallSupports (L + 1) K)
    rw [Finset.mem_product]
    constructor <;>
      simp only [HammingBound.smallSupports, Finset.mem_filter,
        Finset.mem_powerset, Finset.subset_univ, true_and] <;>
      omega

/-- The Hamming-ball container of subsets of size at most `K` is polynomial
in the ambient cardinality when `K` is fixed. -/
theorem card_smallSupports_le
    (n K : ℕ) (hn : 1 ≤ n) :
    (HammingBound.smallSupports n K).card ≤
      (K + 1) * n ^ K := by
  rw [HammingBound.card_smallSupports, HammingBound.volume]
  calc
    (∑ j ∈ Finset.range (K + 1), n.choose j) ≤
        ∑ _j ∈ Finset.range (K + 1), n ^ K := by
      apply Finset.sum_le_sum
      intro j hj
      have hjK : j ≤ K := by
        simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
      exact
        (Nat.choose_le_pow n j).trans
          (Nat.pow_le_pow_right hn hjK)
    _ = (K + 1) * n ^ K := by simp

/-- Explicit polynomial overcount for all bounded offset shapes. -/
theorem card_boundedOffsetShapes_le
    (L K : ℕ) :
    (boundedOffsetShapes L K).card ≤
      ((K + 1) * (L + 1) ^ K) ^ 2 := by
  have hsmall :=
    card_smallSupports_le (L + 1) K (by omega)
  calc
    (boundedOffsetShapes L K).card ≤
        ((HammingBound.smallSupports (L + 1) K).product
          (HammingBound.smallSupports (L + 1) K)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ =
        (HammingBound.smallSupports (L + 1) K).card *
          (HammingBound.smallSupports (L + 1) K).card := by
      simp
    _ ≤
        ((K + 1) * (L + 1) ^ K) *
          ((K + 1) * (L + 1) ^ K) :=
      Nat.mul_le_mul hsmall hsmall
    _ = ((K + 1) * (L + 1) ^ K) ^ 2 := by ring

/-- The actual offset shape of every bounded canonical component belongs to
the finite shape container. -/
theorem componentOffsetShape_mem
    {N M A L K : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L)
    {C : (largePrimeGraph pair.1.1 pair.1.2 L).ConnectedComponent}
    (hC : C ∈ canonicalResidualComponents
      A pair.1.1 pair.1.2 L)
    (hcard : Fintype.card C.supp ≤ K) :
    (componentLeftOffsets pair.1.1 pair.1.2 L C,
        componentRightOffsets pair.1.1 pair.1.2 L C) ∈
      boundedOffsetShapes L K := by
  apply mem_boundedOffsetShapes.mpr
  refine ⟨(componentOffsets_nonempty hN pair hC).1,
    (componentOffsets_nonempty hN pair hC).2, ?_⟩
  rw [card_componentOffsets]
  exact hcard

/-! ## The literal finite host population -/

/--
Separated bounded-ratio pairs carrying a canonical residual component with
at most `K` occurrences.
-/
noncomputable def boundedComponentHosts
    (N M A L K : ℕ) :
    Finset (SeparatedBoundedRatioPair N M L) :=
  Finset.univ.filter fun pair =>
    ∃ C ∈ canonicalResidualComponents
        A pair.1.1 pair.1.2 L,
      Fintype.card C.supp ≤ K

@[simp]
theorem mem_boundedComponentHosts
    {N M A L K : ℕ}
    {pair : SeparatedBoundedRatioPair N M L} :
    pair ∈ boundedComponentHosts N M A L K ↔
      ∃ C ∈ canonicalResidualComponents
          A pair.1.1 pair.1.2 L,
        Fintype.card C.supp ≤ K := by
  simp [boundedComponentHosts]

/--
Exact rational-density extraction behind Lemma 17.24: a dense canonical
core places the pair in a bounded-component host population.
-/
theorem mem_boundedComponentHosts_of_rational_density
    {N M A L alphaNum alphaDen K : ℕ}
    (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L)
    (hden : 0 < alphaDen)
    (hdensity :
      alphaNum * (L + 1) ≤
        alphaDen *
          canonicalResidualComponentCount
            A pair.1.1 pair.1.2 L)
    (hcutoff :
      2 * alphaDen < alphaNum * (K + 1)) :
    pair ∈ boundedComponentHosts N M A L K := by
  classical
  have hcoords := pair_coordinates_two_le hN pair
  have hcard :
      (canonicalResidualComponents
          A pair.1.1 pair.1.2 L).card =
        canonicalResidualComponentCount
          A pair.1.1 pair.1.2 L :=
    card_canonicalResidualComponents hcoords.1 hcoords.2
  have hdensity' :
      alphaNum * (L + 1) ≤
        alphaDen *
          (canonicalResidualComponents
            A pair.1.1 pair.1.2 L).card := by
    rwa [hcard]
  have hambient :
      Fintype.card (Occurrence L) ≤ 2 * (L + 1) := by
    rw [card_occurrence]
  obtain ⟨C, hC, _htwo, hsmall⟩ :=
    PaperC.DeepCoreSmallComponent.exists_bounded_connectedComponent_of_rational_density
      (largePrimeGraph pair.1.1 pair.1.2 L)
      (canonicalResidualComponents
        A pair.1.1 pair.1.2 L)
      (Nat.succ_pos L) hden hambient
      (fun C hC =>
        (isNontrivialUnpinnedComponent_of_mem_canonicalResidualComponents
          hC).2)
      hdensity' hcutoff
  exact mem_boundedComponentHosts.mpr ⟨C, hC, hsmall⟩

/-! ## Canonical enumeration and shifted products -/

/-- Canonical finite enumeration of a set of offsets. -/
noncomputable def offsetEnumeration
    {L : ℕ} (offsets : Finset (Fin (L + 1))) :
    Fin offsets.card ≃ {i // i ∈ offsets} :=
  offsets.equivFin.symm

/-- The signed shifts attached to the canonical enumeration of an offset
set. -/
noncomputable def offsetShift
    {L : ℕ} (offsets : Finset (Fin (L + 1))) :
    Fin offsets.card → ℤ :=
  fun r =>
    RationalChannelCode.channelVertexOffset
      ((offsetEnumeration offsets r).1)

/-- Distinct vertices give distinct signed shifts. -/
theorem offsetShift_injective
    {L : ℕ} (offsets : Finset (Fin (L + 1))) :
    Function.Injective (offsetShift offsets) := by
  intro r s hrs
  apply (offsetEnumeration offsets).injective
  apply Subtype.ext
  exact
    ResidualCertificates.channelVertexOffset_injective
      (by simpa only [offsetShift] using hrs)

/-- Reindexing a finite shifted product by its actual offset set. -/
theorem shiftedProduct_offsetShift
    {x L : ℕ} (hx : 1 ≤ x)
    (offsets : Finset (Fin (L + 1))) :
    shiftedProduct (offsetShift offsets) (x : ℤ) =
      ∏ i ∈ offsets,
        (startCompleteVertexLabel x L i : ℤ) := by
  let e :
      Fin offsets.card ≃ {i // i ∈ offsets} :=
    offsetEnumeration offsets
  calc
    shiftedProduct (offsetShift offsets) (x : ℤ) =
        ∏ r : Fin offsets.card,
          ((x : ℤ) +
            RationalChannelCode.channelVertexOffset ((e r).1)) := by
      rfl
    _ =
        ∏ i : {i // i ∈ offsets},
          ((x : ℤ) +
            RationalChannelCode.channelVertexOffset i.1) :=
      e.prod_comp
        (fun i : {i // i ∈ offsets} =>
          (x : ℤ) +
            RationalChannelCode.channelVertexOffset i.1)
    _ =
        ∏ i ∈ offsets,
          ((x : ℤ) +
            RationalChannelCode.channelVertexOffset i) := by
      exact
        Finset.prod_coe_sort offsets
          (fun i : Fin (L + 1) =>
            (x : ℤ) +
              RationalChannelCode.channelVertexOffset i)
    _ =
        ∏ i ∈ offsets,
          (startCompleteVertexLabel x L i : ℤ) := by
      apply Finset.prod_congr rfl
      intro i _hi
      exact (RationalChannelCode.startCompleteVertexLabel_cast hx i).symm

private theorem prod_leftOccurrenceFactor_eq_offsets
    (x L : ℕ) (s : Finset (Occurrence L)) :
    (∏ v ∈ s, leftOccurrenceFactor x L v) =
      ∏ i ∈
          (Finset.univ.filter fun i : Fin (L + 1) =>
            (Sum.inl i : Occurrence L) ∈ s),
        startCompleteVertexLabel x L i := by
  classical
  let leftVertices := s.filter IsLeftOccurrence
  let offsets :=
    Finset.univ.filter fun i : Fin (L + 1) =>
      (Sum.inl i : Occurrence L) ∈ s
  have hrestrict :
      (∏ v ∈ leftVertices, leftOccurrenceFactor x L v) =
        ∏ v ∈ s, leftOccurrenceFactor x L v := by
    apply Finset.prod_subset (Finset.filter_subset _ _)
    intro v hv hvleft
    cases v with
    | inl i =>
        exfalso
        apply hvleft
        simp [leftVertices, IsLeftOccurrence, hv]
    | inr j =>
        simp [leftOccurrenceFactor]
  have hreindex :
      (∏ i ∈ offsets, startCompleteVertexLabel x L i) =
        ∏ v ∈ leftVertices, leftOccurrenceFactor x L v := by
    apply Finset.prod_bij
      (fun i _hi => (Sum.inl i : Occurrence L))
    · intro i hi
      have his := (Finset.mem_filter.mp hi).2
      exact
        Finset.mem_filter.mpr
          ⟨his, by simp [IsLeftOccurrence]⟩
    · intro i _hi j _hj hij
      exact Sum.inl.inj hij
    · intro v hv
      have hv' := Finset.mem_filter.mp hv
      cases v with
      | inl i =>
          refine ⟨i, ?_, rfl⟩
          exact
            Finset.mem_filter.mpr
              ⟨Finset.mem_univ i, hv'.1⟩
      | inr j =>
          simp [IsLeftOccurrence] at hv'
    · intro i _hi
      rfl
  exact hrestrict.symm.trans hreindex.symm

private theorem prod_rightOccurrenceFactor_eq_offsets
    (y L : ℕ) (s : Finset (Occurrence L)) :
    (∏ v ∈ s, rightOccurrenceFactor y L v) =
      ∏ j ∈
          (Finset.univ.filter fun j : Fin (L + 1) =>
            (Sum.inr j : Occurrence L) ∈ s),
        startCompleteVertexLabel y L j := by
  classical
  let rightVertices := s.filter IsRightOccurrence
  let offsets :=
    Finset.univ.filter fun j : Fin (L + 1) =>
      (Sum.inr j : Occurrence L) ∈ s
  have hrestrict :
      (∏ v ∈ rightVertices, rightOccurrenceFactor y L v) =
        ∏ v ∈ s, rightOccurrenceFactor y L v := by
    apply Finset.prod_subset (Finset.filter_subset _ _)
    intro v hv hvright
    cases v with
    | inl i =>
        simp [rightOccurrenceFactor]
    | inr j =>
        exfalso
        apply hvright
        simp [rightVertices, IsRightOccurrence, hv]
  have hreindex :
      (∏ j ∈ offsets, startCompleteVertexLabel y L j) =
        ∏ v ∈ rightVertices, rightOccurrenceFactor y L v := by
    apply Finset.prod_bij
      (fun j _hj => (Sum.inr j : Occurrence L))
    · intro j hj
      have hjs := (Finset.mem_filter.mp hj).2
      exact
        Finset.mem_filter.mpr
          ⟨hjs, by simp [IsRightOccurrence]⟩
    · intro i _hi j _hj hij
      exact Sum.inr.inj hij
    · intro v hv
      have hv' := Finset.mem_filter.mp hv
      cases v with
      | inl i =>
          simp [IsRightOccurrence] at hv'
      | inr j =>
          refine ⟨j, ?_, rfl⟩
          exact
            Finset.mem_filter.mpr
              ⟨Finset.mem_univ j, hv'.1⟩
    · intro j _hj
      rfl
  exact hrestrict.symm.trans hreindex.symm

/-- Product presentation using exactly the left offset set. -/
theorem componentLeftProduct_eq_offsetProduct
    (x y L : ℕ)
    (C : (largePrimeGraph x y L).ConnectedComponent) :
    componentLeftProduct x y L C =
      ∏ i ∈ componentLeftOffsets x y L C,
        startCompleteVertexLabel x L i := by
  unfold componentLeftProduct componentLeftOffsets
  exact
    prod_leftOccurrenceFactor_eq_offsets
      x L (componentVertices x y L C)

/-- Product presentation using exactly the right offset set. -/
theorem componentRightProduct_eq_offsetProduct
    (x y L : ℕ)
    (C : (largePrimeGraph x y L).ConnectedComponent) :
    componentRightProduct x y L C =
      ∏ j ∈ componentRightOffsets x y L C,
        startCompleteVertexLabel y L j := by
  unfold componentRightProduct componentRightOffsets
  exact
    prod_rightOccurrenceFactor_eq_offsets
      y L (componentVertices x y L C)

/-- Canonical left shift family of a component. -/
noncomputable def componentLeftShift
    (x y L : ℕ)
    (C : (largePrimeGraph x y L).ConnectedComponent) :
    Fin (componentLeftOffsets x y L C).card → ℤ :=
  offsetShift (componentLeftOffsets x y L C)

/-- Canonical right shift family of a component. -/
noncomputable def componentRightShift
    (x y L : ℕ)
    (C : (largePrimeGraph x y L).ConnectedComponent) :
    Fin (componentRightOffsets x y L C).card → ℤ :=
  offsetShift (componentRightOffsets x y L C)

theorem componentLeftShift_injective
    (x y L : ℕ)
    (C : (largePrimeGraph x y L).ConnectedComponent) :
    Function.Injective (componentLeftShift x y L C) :=
  offsetShift_injective _

theorem componentRightShift_injective
    (x y L : ℕ)
    (C : (largePrimeGraph x y L).ConnectedComponent) :
    Function.Injective (componentRightShift x y L C) :=
  offsetShift_injective _

/-- The canonical left shifted product is exactly the integer cast of the
left component factor. -/
theorem shiftedProduct_componentLeftShift
    {x y L : ℕ} (hx : 1 ≤ x)
    (C : (largePrimeGraph x y L).ConnectedComponent) :
    shiftedProduct (componentLeftShift x y L C) (x : ℤ) =
      (componentLeftProduct x y L C : ℤ) := by
  rw [componentLeftProduct_eq_offsetProduct]
  push_cast
  exact
    shiftedProduct_offsetShift hx
      (componentLeftOffsets x y L C)

/-- The canonical right shifted product is exactly the integer cast of the
right component factor. -/
theorem shiftedProduct_componentRightShift
    {x y L : ℕ} (hy : 1 ≤ y)
    (C : (largePrimeGraph x y L).ConnectedComponent) :
    shiftedProduct (componentRightShift x y L C) (y : ℤ) =
      (componentRightProduct x y L C : ℤ) := by
  rw [componentRightProduct_eq_offsetProduct]
  push_cast
  exact
    shiftedProduct_offsetShift hy
      (componentRightOffsets x y L C)

/-! ## The normalized component equation -/

/-- The normalized right-hand equation attached to a fixed component and
its left square-class data. -/
def componentNormalizedEquation
    (x y L : ℕ)
    (C : (largePrimeGraph x y L).ConnectedComponent)
    (d : ℕ) (solution : ℤ × ℤ) : Prop :=
  ComponentNormalization.normalizedShiftedEquation
    (componentLeftProduct x y L C) d
    (componentRightShift x y L C) solution

/--
Every bounded canonical component yields an actual solution of its
canonically enumerated normalized shifted-product equation.  The two
coefficients retain the polynomial cutoff bounds proved in the
normalization module.
-/
theorem exists_componentNormalizedSolution_with_height
    {N M A L K : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L)
    {C : (largePrimeGraph pair.1.1 pair.1.2 L).ConnectedComponent}
    (hC : C ∈ canonicalResidualComponents
      A pair.1.1 pair.1.2 L)
    (hcard : Fintype.card C.supp ≤ K) :
    ∃ d v : ℕ,
      0 < d ∧ Squarefree d ∧
      (∀ p : ℕ, p.Prime → p ∣ d → p ≤ L + 1) ∧
      0 < v ∧
      componentNormalizedEquation
        pair.1.1 pair.1.2 L C d
        ((pair.1.2 : ℤ), (v : ℤ)) ∧
      d ≤ boundedRatioCutoff M L ^ K ∧
      ComponentNormalization.squarefreeKernel
          (d *
            componentLeftProduct
              pair.1.1 pair.1.2 L C) ≤
        boundedRatioCutoff M L ^ (2 * K) := by
  obtain ⟨d, _z, e, v, hd, hdsq, hdsmooth, _hz,
      _he, _hesq, hv, _hwhole, hright, heCanonical,
      hdBound, _hleftBound, _hrightBound, heBound⟩ :=
    exists_normalized_component_equation_with_height
      hN pair hC hcard
  refine ⟨d, v, hd, hdsq, hdsmooth, hv, ?_,
    hdBound, ?_⟩
  · unfold componentNormalizedEquation
      ComponentNormalization.normalizedShiftedEquation
      EvertseSilvermanInput.shiftedSquareEquation
    rw [shiftedProduct_componentRightShift
      (show 1 ≤ pair.1.2 by
        have := pair_coordinates_two_le hN pair
        omega) C]
    rw [← heCanonical]
    change
      (componentRightProduct
        pair.1.1 pair.1.2 L C : ℤ) =
        (e : ℤ) * (v : ℤ) ^ 2
    exact_mod_cast hright
  · rwa [← heCanonical]

/--
The degree-at-least-three fiber is exactly the existing
Evertse--Silverman normalized-equation count, now instantiated with the
actual component offsets.
-/
theorem componentNormalizedEquation_atMost_of_evertseSilverman
    (hES :
      EvertseSilvermanInput.EvertseSilvermanAbscissaStatement)
    {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L)
    {C : (largePrimeGraph pair.1.1 pair.1.2 L).ConnectedComponent}
    (_hC : C ∈ canonicalResidualComponents
      A pair.1.1 pair.1.2 L)
    {d : ℕ} (hd : 0 < d)
    (hdegree :
      3 ≤
        (componentRightOffsets
          pair.1.1 pair.1.2 L C).card) :
    HasAtMostSolutions
      (componentNormalizedEquation
        pair.1.1 pair.1.2 L C d)
      ((componentRightOffsets
          pair.1.1 pair.1.2 L C).card +
        explicitBound
          (componentRightShift
            pair.1.1 pair.1.2 L C)
          (ComponentNormalization.squarefreeKernel
            (d *
              componentLeftProduct
                pair.1.1 pair.1.2 L C) : ℤ)) := by
  have hcoords := pair_coordinates_two_le hN pair
  change HasAtMostSolutions
    (ComponentNormalization.normalizedShiftedEquation
      (componentLeftProduct pair.1.1 pair.1.2 L C) d
      (componentRightShift pair.1.1 pair.1.2 L C)) _
  exact
    ComponentNormalization.normalizedShiftedEquation_atMost_of_evertseSilverman
      hES
      (componentRightShift pair.1.1 pair.1.2 L C)
      hdegree
      (componentRightShift_injective
        pair.1.1 pair.1.2 L C)
      (componentLeftProduct_pos hcoords.1 C)
      hd

/-! ## Reindexing a fixed degree -/

/-- Reindex an offset family by a specified cardinality. -/
noncomputable def offsetShiftOfCard
    {L r : ℕ} (offsets : Finset (Fin (L + 1)))
    (hcard : offsets.card = r) :
    Fin r → ℤ :=
  fun i =>
    offsetShift offsets (Fin.cast hcard.symm i)

theorem offsetShiftOfCard_injective
    {L r : ℕ} (offsets : Finset (Fin (L + 1)))
    (hcard : offsets.card = r) :
    Function.Injective (offsetShiftOfCard offsets hcard) := by
  intro i j hij
  have hcast :
      Fin.cast hcard.symm i =
        Fin.cast hcard.symm j :=
    offsetShift_injective offsets
      (by simpa only [offsetShiftOfCard] using hij)
  exact Fin.cast_injective hcard.symm hcast

/-- Reindexing does not change the shifted product. -/
theorem shiftedProduct_offsetShiftOfCard
    {L r : ℕ} (offsets : Finset (Fin (L + 1)))
    (hcard : offsets.card = r) (X : ℤ) :
    shiftedProduct (offsetShiftOfCard offsets hcard) X =
      shiftedProduct (offsetShift offsets) X := by
  let e : Fin r ≃ Fin offsets.card :=
    (Fin.castOrderIso hcard.symm).toEquiv
  unfold EvertseSilvermanInput.shiftedProduct
  exact
    e.prod_comp
      (fun i : Fin offsets.card =>
        X + offsetShift offsets i)

/-- Reindexed normalized equation, convenient for the degree-one and
degree-two branches. -/
def reindexedOffsetNormalizedEquation
    {L r : ℕ} (offsets : Finset (Fin (L + 1)))
    (hcard : offsets.card = r)
    (P d : ℕ) (solution : ℤ × ℤ) : Prop :=
  ComponentNormalization.normalizedShiftedEquation
    P d (offsetShiftOfCard offsets hcard) solution

theorem reindexedOffsetNormalizedEquation_iff
    {L r P d : ℕ}
    (offsets : Finset (Fin (L + 1)))
    (hcard : offsets.card = r)
    (solution : ℤ × ℤ) :
    reindexedOffsetNormalizedEquation
        offsets hcard P d solution ↔
      ComponentNormalization.normalizedShiftedEquation
        P d (offsetShift offsets) solution := by
  unfold reindexedOffsetNormalizedEquation
    ComponentNormalization.normalizedShiftedEquation
    EvertseSilvermanInput.shiftedSquareEquation
  rw [shiftedProduct_offsetShiftOfCard]

/-! ## Degree one: transfer to the existing square-root count -/

/-- Natural base used to remove the sole possible negative signed shift
`-1`. -/
def oneOffsetBase
    {L : ℕ} (i : Fin (L + 1)) (x : ℕ) : ℕ :=
  if i.1 = 0 then x - 1 else x

/-- Nonnegative shift after the preceding base change. -/
def oneOffsetNatShift
    {L : ℕ} (i : Fin (L + 1)) : ℕ :=
  if i.1 = 0 then 0 else i.1 - 1

/-- Map a solution for one complete-start vertex to the degree-one equation
already counted in `ComponentNormalization`. -/
def oneOffsetToOneShift
    {L : ℕ} (i : Fin (L + 1))
    (solution : ℕ × ℕ) : ℕ × ℕ :=
  (oneOffsetBase i solution.1, solution.2)

/-- The bounded degree-one fiber attached to one actual vertex offset. -/
def oneOffsetFiber
    {L : ℕ} (i : Fin (L + 1))
    (e Y : ℕ) (solution : ℕ × ℕ) : Prop :=
  2 ≤ solution.1 ∧
    solution.1 ≤ Y ∧
    startCompleteVertexLabel solution.1 L i =
      e * solution.2 ^ 2

theorem oneOffsetFiber_maps_to_oneShift
    {L e Y : ℕ} {i : Fin (L + 1)}
    {solution : ℕ × ℕ}
    (hsolution : oneOffsetFiber i e Y solution) :
    ComponentNormalization.oneShiftEquation
        e (oneOffsetNatShift i)
        (oneOffsetToOneShift i solution) ∧
      (oneOffsetToOneShift i solution).1 ≤ Y := by
  rcases hsolution with ⟨hx, hxY, heq⟩
  by_cases hi : i.1 = 0
  · simp only [oneOffsetToOneShift, oneOffsetBase,
      oneOffsetNatShift, hi, if_pos,
      ComponentNormalization.oneShiftEquation,
      Prod.fst, Prod.snd, add_zero]
    constructor
    · simpa [startCompleteVertexLabel, hi] using heq
    · omega
  · simp only [oneOffsetToOneShift, oneOffsetBase,
      oneOffsetNatShift, hi, if_neg,
      ComponentNormalization.oneShiftEquation,
      Prod.fst, Prod.snd]
    constructor
    · simpa [startCompleteVertexLabel, hi] using heq
    · exact hxY

theorem oneOffsetToOneShift_injective_on
    {L e Y : ℕ} {i : Fin (L + 1)}
    {u v : ℕ × ℕ}
    (hu : oneOffsetFiber i e Y u)
    (hv : oneOffsetFiber i e Y v)
    (huv :
      oneOffsetToOneShift i u =
        oneOffsetToOneShift i v) :
    u = v := by
  have hfst :=
    congrArg Prod.fst huv
  have hsnd :=
    congrArg Prod.snd huv
  have huLower := hu.1
  have hvLower := hv.1
  apply Prod.ext
  · by_cases hi : i.1 = 0
    · simp only [oneOffsetToOneShift, oneOffsetBase,
        hi, if_pos, Prod.fst] at hfst
      omega
    · simpa [oneOffsetToOneShift, oneOffsetBase, hi] using hfst
  · simpa [oneOffsetToOneShift] using hsnd

/--
The actual signed-offset degree-one fiber inherits the repository's exact
`sqrt(Y+j)+1` count.
-/
theorem oneOffsetFiber_atMost_sqrt
    {L : ℕ} (i : Fin (L + 1))
    (e Y : ℕ) (he : 0 < e) :
    HasAtMostSolutions
      (oneOffsetFiber i e Y)
      (Nat.sqrt (Y + oneOffsetNatShift i) + 1) := by
  intro s hs
  let f : ℕ × ℕ → ℕ × ℕ :=
    oneOffsetToOneShift i
  have hinjective :
      Set.InjOn f (↑s : Set (ℕ × ℕ)) := by
    intro u hu v hv huv
    exact
      oneOffsetToOneShift_injective_on
        (hs u hu) (hs v hv)
        (by simpa only [f] using huv)
  have himage :
      ∀ solution ∈ s.image f,
        ComponentNormalization.oneShiftEquation
            e (oneOffsetNatShift i) solution ∧
          solution.1 ≤ Y := by
    intro solution hsolution
    obtain ⟨original, horiginal, rfl⟩ :=
      Finset.mem_image.mp hsolution
    simpa only [f] using
      oneOffsetFiber_maps_to_oneShift
        (hs original horiginal)
  have hcount :=
    ComponentNormalization.oneShiftEquation_atMost_sqrt
      e (oneOffsetNatShift i) Y he
      (s.image f) himage
  calc
    s.card = (s.image f).card :=
      (Finset.card_image_of_injOn hinjective).symm
    _ ≤ Nat.sqrt (Y + oneOffsetNatShift i) + 1 :=
      hcount

/-- Fixed-shape natural fiber used for the one-sided host count. -/
def offsetProductNatFiber
    {L : ℕ} (offsets : Finset (Fin (L + 1)))
    (e Y : ℕ) (solution : ℕ × ℕ) : Prop :=
  2 ≤ solution.1 ∧
    solution.1 ≤ Y ∧
    (∏ i ∈ offsets,
      startCompleteVertexLabel solution.1 L i) =
        e * solution.2 ^ 2

/--
When the mobile degree is one, the concrete fixed-shape fiber reduces
without loss to `oneOffsetFiber_atMost_sqrt`.
-/
theorem offsetProductNatFiber_degree_one_atMost
    {L : ℕ} (offsets : Finset (Fin (L + 1)))
    (hdegree : offsets.card = 1)
    (e Y : ℕ) (he : 0 < e) :
    ∃ i : Fin (L + 1),
      offsets = {i} ∧
      HasAtMostSolutions
        (offsetProductNatFiber offsets e Y)
        (Nat.sqrt (Y + oneOffsetNatShift i) + 1) := by
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hdegree
  refine ⟨i, hi, ?_⟩
  have hcount :=
    oneOffsetFiber_atMost_sqrt i e Y he
  intro s hs
  apply hcount s
  intro solution hsolution
  have hsource := hs solution hsolution
  simpa [offsetProductNatFiber, hi, oneOffsetFiber] using
    hsource

/--
The normalized solution supplied by an actual bounded component belongs to
the fixed-shape natural fiber used above.
-/
theorem exists_componentRightFiber_with_height
    {N M A L K : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L)
    {C : (largePrimeGraph pair.1.1 pair.1.2 L).ConnectedComponent}
    (hC : C ∈ canonicalResidualComponents
      A pair.1.1 pair.1.2 L)
    (hcard : Fintype.card C.supp ≤ K) :
    ∃ d e v : ℕ,
      0 < d ∧ Squarefree d ∧
      (∀ p : ℕ, p.Prime → p ∣ d → p ≤ L + 1) ∧
      0 < e ∧ Squarefree e ∧
      0 < v ∧
      e =
        ComponentNormalization.squarefreeKernel
          (d *
            componentLeftProduct
              pair.1.1 pair.1.2 L C) ∧
      d ≤ boundedRatioCutoff M L ^ K ∧
      e ≤ boundedRatioCutoff M L ^ (2 * K) ∧
      offsetProductNatFiber
        (componentRightOffsets
          pair.1.1 pair.1.2 L C)
        e M (pair.1.2, v) := by
  obtain ⟨d, _z, e, v, hd, hdsq, hdsmooth, _hz,
      he, hesq, hv, _hwhole, hright, heCanonical,
      hdBound, _hleftBound, _hrightBound, heBound⟩ :=
    exists_normalized_component_equation_with_height
      hN pair hC hcard
  refine ⟨d, e, v, hd, hdsq, hdsmooth, he, hesq, hv,
    heCanonical, hdBound, heBound, ?_⟩
  have hcoords := pair_coordinates_two_le hN pair
  have hpair := mem_separatedBoundedRatioPairs.mp pair.2
  refine ⟨hcoords.2, (Nat.le_of_lt
    (mem_boundedRatioBlock.mp hpair.2.1).2), ?_⟩
  rw [← componentRightProduct_eq_offsetProduct]
  exact hright

/-! ## Degree two: exact transfer to the existing Pell box -/

/-- A reindexed degree-two normalized equation is literally the completed
square input used by `twoShiftPellBox_atMost`. -/
theorem reindexedOffsetNormalizedEquation_degree_two_iff
    {L P d : ℕ}
    (offsets : Finset (Fin (L + 1)))
    (hdegree : offsets.card = 2)
    (solution : ℤ × ℤ) :
    reindexedOffsetNormalizedEquation
        offsets hdegree P d solution ↔
      ComponentNormalization.twoShiftEquation
        (offsetShiftOfCard offsets hdegree 0)
        (offsetShiftOfCard offsets hdegree 1)
        (ComponentNormalization.squarefreeKernel (d * P))
        solution := by
  unfold reindexedOffsetNormalizedEquation
    ComponentNormalization.normalizedShiftedEquation
    EvertseSilvermanInput.shiftedSquareEquation
    EvertseSilvermanInput.shiftedProduct
    ComponentNormalization.twoShiftEquation
  rw [Fin.prod_univ_two]

/--
Any finite Pell-box estimate transfers unchanged to the actual normalized
degree-two offset fiber.  This is the exact fixed-parameter reduction; the
remaining global work is only to sum these bounds uniformly over shapes
and square classes.
-/
theorem normalizedOffsetDegreeTwo_atMost_of_pell
    {L P d H : ℕ} {R : ℝ}
    (offsets : Finset (Fin (L + 1)))
    (hdegree : offsets.card = 2)
    (hPell :
      PellInput.HasAtMostSolutionsReal
        (PellInput.pellBox
          1
          (ComponentNormalization.squarefreeKernel (d * P))
          ((offsetShiftOfCard offsets hdegree 0 -
            offsetShiftOfCard offsets hdegree 1) ^ 2)
          H)
        R) :
    PellInput.HasAtMostSolutionsReal
      (fun solution : ℤ × ℤ =>
        ComponentNormalization.normalizedShiftedEquation
            P d (offsetShift offsets) solution ∧
          (ComponentNormalization.toPellPair
            (offsetShiftOfCard offsets hdegree 0)
            (offsetShiftOfCard offsets hdegree 1)
            solution).1.natAbs ≤ H ∧
          (ComponentNormalization.toPellPair
            (offsetShiftOfCard offsets hdegree 0)
            (offsetShiftOfCard offsets hdegree 1)
            solution).2.natAbs ≤ H)
      R := by
  have htransfer :=
    ComponentNormalization.twoShiftPellBox_atMost hPell
  intro s hs
  apply htransfer s
  intro solution hsolution
  have hsource := hs solution hsolution
  refine ⟨?_, hsource.2.1, hsource.2.2⟩
  apply
    (reindexedOffsetNormalizedEquation_degree_two_iff
      offsets hdegree solution).mp
  exact
    (reindexedOffsetNormalizedEquation_iff
      offsets hdegree solution).mpr hsource.1

/--
Polynomial-box wrapper exposing only the already registered generalized
Pell hypothesis.  All specialization to the actual two component offsets
and transfer back to the normalized component fiber are proved here.
-/
theorem normalizedOffsetDegreeTwo_polynomialBox_of_generalizedPell
    (hPell :
      PellInput.GeneralizedPellPolynomialBoxStatement) :
    ∀ K : ℕ, 0 < K →
      ∃ c : ℝ, 0 ≤ c ∧
        ∃ N₀ : ℕ, ∀ N ≥ N₀,
          ∀ (L : ℕ)
            (offsets : Finset (Fin (L + 1)))
            (hdegree : offsets.card = 2)
            (P d : ℕ),
          0 <
              ComponentNormalization.squarefreeKernel
                (d * P) →
          Squarefree
              (ComponentNormalization.squarefreeKernel
                (d * P)) →
          ¬IsSquare
              ((1 : ℚ) /
                (ComponentNormalization.squarefreeKernel
                  (d * P) : ℚ)) →
          ComponentNormalization.squarefreeKernel
                (d * P) ≤
              N ^ K →
          ((offsetShiftOfCard offsets hdegree 0 -
              offsetShiftOfCard offsets hdegree 1) ^ 2).natAbs ≤
              N ^ K →
          PellInput.HasAtMostSolutionsReal
            (fun solution : ℤ × ℤ =>
              ComponentNormalization.normalizedShiftedEquation
                  P d (offsetShift offsets) solution ∧
                (ComponentNormalization.toPellPair
                  (offsetShiftOfCard offsets hdegree 0)
                  (offsetShiftOfCard offsets hdegree 1)
                  solution).1.natAbs ≤ N ^ K ∧
                (ComponentNormalization.toPellPair
                  (offsetShiftOfCard offsets hdegree 0)
                  (offsetShiftOfCard offsets hdegree 1)
                  solution).2.natAbs ≤ N ^ K)
            (PellInput.expLogLogBound c N) := by
  intro K hK
  obtain ⟨c, hc, N₀, hN₀⟩ :=
    ComponentNormalization.twoShiftPolynomialBox_of_generalizedPell
      hPell K hK
  refine ⟨c, hc, N₀, ?_⟩
  intro N hN L offsets hdegree P d he hesq
    hnonsquare heBound hdeltaBound
  have hshifts :
      offsetShiftOfCard offsets hdegree 0 ≠
        offsetShiftOfCard offsets hdegree 1 := by
    intro h
    have h01 :
        (0 : Fin 2) = 1 :=
      offsetShiftOfCard_injective offsets hdegree h
    exact (by decide : (0 : Fin 2) ≠ 1) h01
  have hcount :=
    hN₀ N hN
      (ComponentNormalization.squarefreeKernel (d * P))
      (offsetShiftOfCard offsets hdegree 0)
      (offsetShiftOfCard offsets hdegree 1)
      he hesq hshifts hnonsquare heBound hdeltaBound
  intro s hs
  apply hcount s
  intro solution hsolution
  have hsource := hs solution hsolution
  refine ⟨?_, hsource.2.1, hsource.2.2⟩
  apply
    (reindexedOffsetNormalizedEquation_degree_two_iff
      offsets hdegree solution).mp
  exact
    (reindexedOffsetNormalizedEquation_iff
      offsets hdegree solution).mpr hsource.1

/-! ## Exact finite summation invariant for Lemmas 17.23--17.24 -/

/--
Hosts carrying a bounded component with one specified ordered offset
shape.  The component itself is existential because a pair may carry more
than one bounded component.
-/
noncomputable def boundedComponentHostsOfShape
    (N M A L K : ℕ)
    (shape :
      Finset (Fin (L + 1)) × Finset (Fin (L + 1))) :
    Finset (SeparatedBoundedRatioPair N M L) :=
  (boundedComponentHosts N M A L K).filter fun pair =>
    ∃ C ∈ canonicalResidualComponents
        A pair.1.1 pair.1.2 L,
      Fintype.card C.supp ≤ K ∧
      componentLeftOffsets pair.1.1 pair.1.2 L C =
          shape.1 ∧
        componentRightOffsets pair.1.1 pair.1.2 L C =
          shape.2

@[simp]
theorem mem_boundedComponentHostsOfShape
    {N M A L K : ℕ}
    {shape :
      Finset (Fin (L + 1)) × Finset (Fin (L + 1))}
    {pair : SeparatedBoundedRatioPair N M L} :
    pair ∈ boundedComponentHostsOfShape
        N M A L K shape ↔
      pair ∈ boundedComponentHosts N M A L K ∧
      ∃ C ∈ canonicalResidualComponents
          A pair.1.1 pair.1.2 L,
        Fintype.card C.supp ≤ K ∧
        componentLeftOffsets pair.1.1 pair.1.2 L C =
            shape.1 ∧
          componentRightOffsets pair.1.1 pair.1.2 L C =
            shape.2 := by
  simp [boundedComponentHostsOfShape]

/-- The finite shape fibers cover the entire host population. -/
theorem boundedComponentHosts_subset_shapeUnion
    {N M A L K : ℕ} (hN : 2 ≤ N) :
    boundedComponentHosts N M A L K ⊆
      (boundedOffsetShapes L K).biUnion fun shape =>
        boundedComponentHostsOfShape
          N M A L K shape := by
  classical
  intro pair hpair
  obtain ⟨C, hC, hsmall⟩ :=
    mem_boundedComponentHosts.mp hpair
  let shape :
      Finset (Fin (L + 1)) × Finset (Fin (L + 1)) :=
    (componentLeftOffsets pair.1.1 pair.1.2 L C,
      componentRightOffsets pair.1.1 pair.1.2 L C)
  apply Finset.mem_biUnion.mpr
  refine ⟨shape, ?_, ?_⟩
  · exact componentOffsetShape_mem hN pair hC hsmall
  · apply mem_boundedComponentHostsOfShape.mpr
    exact
      ⟨hpair, C, hC, hsmall, rfl, rfl⟩

/--
Exact remaining summation invariant.  A uniform bound `Q` for every fixed
offset-shape fiber gives the global bound

`#hosts ≤ ((K+1)(L+1)^K)^2 * Q`.

The premise is deliberately a theorem parameter, not a named proposition
or bridge.  Its future proof is where the degree-one, Pell and
Evertse--Silverman fiber estimates above must be summed over the remaining
square-class and fixed-start data.
-/
theorem card_boundedComponentHosts_le_of_shapeFibers
    {N M A L K Q : ℕ} (hN : 2 ≤ N)
    (hshape :
      ∀ shape ∈ boundedOffsetShapes L K,
        (boundedComponentHostsOfShape
          N M A L K shape).card ≤ Q) :
    (boundedComponentHosts N M A L K).card ≤
      ((K + 1) * (L + 1) ^ K) ^ 2 * Q := by
  classical
  calc
    (boundedComponentHosts N M A L K).card ≤
        ((boundedOffsetShapes L K).biUnion fun shape =>
          boundedComponentHostsOfShape
            N M A L K shape).card :=
      Finset.card_le_card
        (boundedComponentHosts_subset_shapeUnion hN)
    _ ≤
        ∑ shape ∈ boundedOffsetShapes L K,
          (boundedComponentHostsOfShape
            N M A L K shape).card :=
      Finset.card_biUnion_le
    _ ≤
        ∑ _shape ∈ boundedOffsetShapes L K, Q :=
      Finset.sum_le_sum fun shape hshapeMem =>
        hshape shape hshapeMem
    _ = (boundedOffsetShapes L K).card * Q := by
      simp
    _ ≤
        ((K + 1) * (L + 1) ^ K) ^ 2 * Q :=
      Nat.mul_le_mul_right Q
        (card_boundedOffsetShapes_le L K)

/-! ## The deep-core population of Lemma 17.24 -/

/-- Literal rational-density population, before selecting a small
component. -/
noncomputable def denseCanonicalCorePairs
    (N M A L alphaNum alphaDen : ℕ) :
    Finset (SeparatedBoundedRatioPair N M L) :=
  Finset.univ.filter fun pair =>
    alphaNum * (L + 1) ≤
      alphaDen *
        canonicalResidualComponentCount
          A pair.1.1 pair.1.2 L

@[simp]
theorem mem_denseCanonicalCorePairs
    {N M A L alphaNum alphaDen : ℕ}
    {pair : SeparatedBoundedRatioPair N M L} :
    pair ∈ denseCanonicalCorePairs
        N M A L alphaNum alphaDen ↔
      alphaNum * (L + 1) ≤
        alphaDen *
          canonicalResidualComponentCount
            A pair.1.1 pair.1.2 L := by
  simp [denseCanonicalCorePairs]

/-- Rational density selects a bounded component uniformly in the pair. -/
theorem denseCanonicalCorePairs_subset_boundedComponentHosts
    {N M A L alphaNum alphaDen K : ℕ}
    (hN : 2 ≤ N) (hden : 0 < alphaDen)
    (hcutoff :
      2 * alphaDen < alphaNum * (K + 1)) :
    denseCanonicalCorePairs
        N M A L alphaNum alphaDen ⊆
      boundedComponentHosts N M A L K := by
  intro pair hpair
  exact
    mem_boundedComponentHosts_of_rational_density
      hN pair hden
      (mem_denseCanonicalCorePairs.mp hpair)
      hcutoff

/--
Finite Lemma 17.24 closure from the same fixed-shape invariant as
Lemma 17.23.
-/
theorem card_denseCanonicalCorePairs_le_of_shapeFibers
    {N M A L alphaNum alphaDen K Q : ℕ}
    (hN : 2 ≤ N) (hden : 0 < alphaDen)
    (hcutoff :
      2 * alphaDen < alphaNum * (K + 1))
    (hshape :
      ∀ shape ∈ boundedOffsetShapes L K,
        (boundedComponentHostsOfShape
          N M A L K shape).card ≤ Q) :
    (denseCanonicalCorePairs
        N M A L alphaNum alphaDen).card ≤
      ((K + 1) * (L + 1) ^ K) ^ 2 * Q := by
  exact
    (Finset.card_le_card
      (denseCanonicalCorePairs_subset_boundedComponentHosts
        hN hden hcutoff)).trans
      (card_boundedComponentHosts_le_of_shapeFibers
        hN hshape)

end

end BoundedRatioComponentHosts
end PaperC
