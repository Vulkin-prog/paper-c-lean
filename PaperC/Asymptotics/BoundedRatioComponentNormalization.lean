import PaperC.Asymptotics.PropositionSixteenOneCore
import PaperC.Coding.AlignedComponentCode
import PaperC.Combinatorics.ComponentProductParity
import PaperC.Diophantine.ComponentNormalization

set_option maxHeartbeats 1800000

/-!
# Component normalization on a bounded-ratio interval

This file supplies the exact finite bridge between the graph-theoretic
component extracted in Lemmas 17.23--17.26 and the Diophantine equations of
Lemmas 17.20--17.21.

For one residual component we split its product into a left factor depending
only on the first start and a right factor depending only on the second
start.  The component square-class theorem then gives

`P_I(x) * Q_J(y) = d * z^2`,

with `d` positive, squarefree and supported on primes at most `L+1`.
The canonical normalization of Lemma 9.3 consequently rewrites the right
factor as `e * v^2`.  All factors are bounded directly by powers of the
literal cutoff `M+L`; no dyadic-shell replacement is used.
-/

namespace PaperC
namespace BoundedRatioComponentNormalization

open scoped BigOperators
open Affine
open AlignedComponentCode
open CanonicalResidualComponents
open ComponentProductParity
open LargePrimeComponents
open LargePrimeGraph
open LargePrimeGraphResolution
open LargePrimeOccurrences
open PropositionSixteenOne

noncomputable section

noncomputable local instance instDecidableLargePrimeAdj
    (x y L : ℕ) :
    DecidableRel (largePrimeGraph x y L).Adj :=
  Classical.decRel _

/-! ## Splitting a component product by blocks -/

/-- The factor contributed by an occurrence to the left component product. -/
def leftOccurrenceFactor
    (x L : ℕ) : Occurrence L → ℕ
  | Sum.inl i => startCompleteVertexLabel x L i
  | Sum.inr _ => 1

/-- The factor contributed by an occurrence to the right component product. -/
def rightOccurrenceFactor
    (y L : ℕ) : Occurrence L → ℕ
  | Sum.inl _ => 1
  | Sum.inr j => startCompleteVertexLabel y L j

/-- Product of the labels of the left vertices of a component. -/
noncomputable def componentLeftProduct
    (x y L : ℕ)
    (C : (largePrimeGraph x y L).ConnectedComponent) : ℕ :=
  ∏ v ∈ componentVertices x y L C,
    leftOccurrenceFactor x L v

/-- Product of the labels of the right vertices of a component. -/
noncomputable def componentRightProduct
    (x y L : ℕ)
    (C : (largePrimeGraph x y L).ConnectedComponent) : ℕ :=
  ∏ v ∈ componentVertices x y L C,
    rightOccurrenceFactor y L v

/-- Each complete label is the product of its left and right factors. -/
theorem left_mul_rightOccurrenceFactor
    (x y L : ℕ) (v : Occurrence L) :
    leftOccurrenceFactor x L v *
        rightOccurrenceFactor y L v =
      twoStartCompleteVertexLabel x y L v := by
  cases v <;> simp [leftOccurrenceFactor, rightOccurrenceFactor,
    twoStartCompleteVertexLabel]

/-- Exact factorization of the component product into its two blocks. -/
theorem componentVertexProduct_eq_left_mul_right
    (x y L : ℕ)
    (C : (largePrimeGraph x y L).ConnectedComponent) :
    componentVertexProduct x y L C =
      componentLeftProduct x y L C *
        componentRightProduct x y L C := by
  classical
  unfold componentVertexProduct componentLeftProduct componentRightProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v _hv
  exact (left_mul_rightOccurrenceFactor x y L v).symm

/-- The image-product presentation agrees with the occurrence product. -/
theorem componentProduct_labels_eq_componentVertexProduct
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hsep : L < Nat.dist x y)
    (C : (largePrimeGraph x y L).ConnectedComponent) :
    ComponentSquareClass.componentProduct
        (componentLabels x y L C) =
      componentVertexProduct x y L C := by
  classical
  unfold ComponentSquareClass.componentProduct componentLabels
    componentVertexProduct
  rw [Finset.prod_image]
  intro v _hv w _hw hvw
  exact
    twoStartCompleteVertexLabel_injective_of_separated
      hx hy hsep hvw

/-!
Every nontrivial large-prime component meets both blocks.  This elementary
bipartite fact is what makes both offset sets `I` and `J` nonempty in
Lemma 17.20.
-/
theorem exists_left_and_right_vertices
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (C : (largePrimeGraph x y L).ConnectedComponent)
    (hC :
      PinnedGraphResolution.IsNontrivialUnpinnedComponent
        (largePrimeGraph x y L)
        (pinnedVertices x y L) C) :
    ∃ i j,
      (Sum.inl i : Occurrence L) ∈
          componentVertices x y L C ∧
        (Sum.inr j : Occurrence L) ∈
          componentVertices x y L C := by
  classical
  have hsize : 2 ≤ Fintype.card C.supp :=
    hC.2
  have hcard :
      1 < (componentVertices x y L C).card := by
    rw [ComponentProductParity.card_componentVertices]
    omega
  obtain ⟨u, w, hu, hw, huw⟩ :=
    Finset.one_lt_card_iff.mp hcard
  have hcomponent :
      (largePrimeGraph x y L).connectedComponentMk u =
        (largePrimeGraph x y L).connectedComponentMk w := by
    rw [mem_componentVertices] at hu hw
    exact hu.trans hw.symm
  let walk : (largePrimeGraph x y L).Walk u w :=
    Classical.choice
      (SimpleGraph.ConnectedComponent.exact hcomponent)
  have hlength : 0 < walk.length := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact huw (walk.eq_of_length_eq_zero hzero)
  have hnotnil : ¬walk.Nil :=
    SimpleGraph.Walk.not_nil_iff_lt_length.mpr hlength
  have hadj :
      (largePrimeGraph x y L).Adj u walk.snd :=
    walk.adj_snd hnotnil
  have hsnd :
      walk.snd ∈ componentVertices x y L C := by
    rw [mem_componentVertices]
    have husnd :
        (largePrimeGraph x y L).connectedComponentMk u =
          (largePrimeGraph x y L).connectedComponentMk walk.snd :=
      SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj
    rw [← husnd]
    exact mem_componentVertices.mp hu
  obtain ⟨hne, p, hp, hup, hsndp⟩ := hadj
  rcases
      inOppositeBlocks_of_mem_of_ne
        hx hy hp.1 hp.2 hup hsndp hne with
    ⟨i, j, hui, hsndj⟩ | ⟨j, i, huj, hsndi⟩
  · refine ⟨i, j, ?_, ?_⟩
    · simpa only [hui] using hu
    · simpa only [hsndj] using hsnd
  · refine ⟨i, j, ?_, ?_⟩
    · simpa only [hsndi] using hsnd
    · simpa only [huj] using hu

/-- The left degree of a nontrivial component is positive. -/
theorem one_le_componentLeftCount
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (C : (largePrimeGraph x y L).ConnectedComponent)
    (hC :
      PinnedGraphResolution.IsNontrivialUnpinnedComponent
        (largePrimeGraph x y L)
        (pinnedVertices x y L) C) :
    1 ≤ componentLeftCount x y L C := by
  classical
  obtain ⟨i, _j, hi, _hj⟩ :=
    exists_left_and_right_vertices hx hy C hC
  unfold componentLeftCount
  apply Finset.one_le_card.mpr
  exact
    ⟨Sum.inl i, by
      simp only [Finset.mem_filter, hi, IsLeftOccurrence, and_self]⟩

/-- The right degree of a nontrivial component is positive. -/
theorem one_le_componentRightCount
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (C : (largePrimeGraph x y L).ConnectedComponent)
    (hC :
      PinnedGraphResolution.IsNontrivialUnpinnedComponent
        (largePrimeGraph x y L)
        (pinnedVertices x y L) C) :
    1 ≤ componentRightCount x y L C := by
  classical
  obtain ⟨_i, j, _hi, hj⟩ :=
    exists_left_and_right_vertices hx hy C hC
  unfold componentRightCount
  apply Finset.one_le_card.mpr
  exact
    ⟨Sum.inr j, by
      simp only [Finset.mem_filter, hj, IsRightOccurrence, and_self]⟩

/-! ## Positivity and literal cutoff bounds -/

/-- Every left occurrence factor is positive for a positive start. -/
theorem leftOccurrenceFactor_pos
    {x L : ℕ} (hx : 2 ≤ x) (v : Occurrence L) :
    0 < leftOccurrenceFactor x L v := by
  cases v with
  | inl i =>
      unfold leftOccurrenceFactor
      exact
        Affine.RationalChannelCode.startCompleteVertexLabel_pos
          hx i
  | inr _ =>
      simp [leftOccurrenceFactor]

/-- Every right occurrence factor is positive for a positive start. -/
theorem rightOccurrenceFactor_pos
    {y L : ℕ} (hy : 2 ≤ y) (v : Occurrence L) :
    0 < rightOccurrenceFactor y L v := by
  cases v with
  | inl _ =>
      simp [rightOccurrenceFactor]
  | inr j =>
      unfold rightOccurrenceFactor
      exact
        Affine.RationalChannelCode.startCompleteVertexLabel_pos
          hy j

/-- The left component factor is positive. -/
theorem componentLeftProduct_pos
    {x y L : ℕ} (hx : 2 ≤ x)
    (C : (largePrimeGraph x y L).ConnectedComponent) :
    0 < componentLeftProduct x y L C := by
  unfold componentLeftProduct
  exact Finset.prod_pos fun v _hv => leftOccurrenceFactor_pos hx v

/-- The right component factor is positive. -/
theorem componentRightProduct_pos
    {x y L : ℕ} (hy : 2 ≤ y)
    (C : (largePrimeGraph x y L).ConnectedComponent) :
    0 < componentRightProduct x y L C := by
  unfold componentRightProduct
  exact Finset.prod_pos fun v _hv => rightOccurrenceFactor_pos hy v

/-- Every left factor is bounded by the literal cylinder cutoff `M+L`. -/
theorem leftOccurrenceFactor_le_cutoff
    {N M L : ℕ}
    (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L)
    (v : Occurrence L) :
    leftOccurrenceFactor pair.1.1 L v ≤
      boundedRatioCutoff M L := by
  have hpair :=
    mem_separatedBoundedRatioPairs.mp pair.2
  have hcoords := pair_coordinates_two_le hN pair
  have hxM := (mem_boundedRatioBlock.mp hpair.1).2
  cases v with
  | inl i =>
      simp only [leftOccurrenceFactor]
      have hupper :=
        startCompleteVertexLabel_upper
          (show 1 ≤ pair.1.1 by omega) i
      unfold boundedRatioCutoff
      calc
        startCompleteVertexLabel pair.1.1 L i ≤
            pair.1.1 + L :=
          Nat.le_of_lt hupper
        _ ≤ M + L :=
          Nat.add_le_add_right (Nat.le_of_lt hxM) L
  | inr _ =>
      simp only [leftOccurrenceFactor]
      unfold boundedRatioCutoff
      omega

/-- Every right factor is bounded by the literal cylinder cutoff `M+L`. -/
theorem rightOccurrenceFactor_le_cutoff
    {N M L : ℕ}
    (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L)
    (v : Occurrence L) :
    rightOccurrenceFactor pair.1.2 L v ≤
      boundedRatioCutoff M L := by
  have hpair :=
    mem_separatedBoundedRatioPairs.mp pair.2
  have hcoords := pair_coordinates_two_le hN pair
  have hyM := (mem_boundedRatioBlock.mp hpair.2.1).2
  cases v with
  | inl _ =>
      simp only [rightOccurrenceFactor]
      unfold boundedRatioCutoff
      omega
  | inr j =>
      simp only [rightOccurrenceFactor]
      have hupper :=
        startCompleteVertexLabel_upper
          (show 1 ≤ pair.1.2 by omega) j
      unfold boundedRatioCutoff
      calc
        startCompleteVertexLabel pair.1.2 L j ≤
            pair.1.2 + L :=
          Nat.le_of_lt hupper
        _ ≤ M + L :=
          Nat.add_le_add_right (Nat.le_of_lt hyM) L

/-- Every complete component label is below the literal cylinder cutoff. -/
theorem twoStartCompleteVertexLabel_le_cutoff
    {N M L : ℕ}
    (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L)
    (v : Occurrence L) :
    twoStartCompleteVertexLabel pair.1.1 pair.1.2 L v ≤
      boundedRatioCutoff M L := by
  cases v with
  | inl i =>
      change startCompleteVertexLabel pair.1.1 L i ≤
        boundedRatioCutoff M L
      simpa only [leftOccurrenceFactor] using
        leftOccurrenceFactor_le_cutoff hN pair (Sum.inl i)
  | inr j =>
      change startCompleteVertexLabel pair.1.2 L j ≤
        boundedRatioCutoff M L
      simpa only [rightOccurrenceFactor] using
        rightOccurrenceFactor_le_cutoff hN pair (Sum.inr j)

/-- Product bound with the exact number of component vertices. -/
theorem componentLeftProduct_le_cutoff_pow_card
    {N M L : ℕ}
    (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L)
    (C : (largePrimeGraph pair.1.1 pair.1.2 L).ConnectedComponent) :
    componentLeftProduct pair.1.1 pair.1.2 L C ≤
      boundedRatioCutoff M L ^
        (componentVertices pair.1.1 pair.1.2 L C).card := by
  unfold componentLeftProduct
  calc
    (∏ v ∈ componentVertices pair.1.1 pair.1.2 L C,
        leftOccurrenceFactor pair.1.1 L v) ≤
        ∏ _v ∈ componentVertices pair.1.1 pair.1.2 L C,
          boundedRatioCutoff M L :=
      Finset.prod_le_prod
        (fun _v _hv => Nat.zero_le _)
        (fun v _hv => leftOccurrenceFactor_le_cutoff hN pair v)
    _ = boundedRatioCutoff M L ^
        (componentVertices pair.1.1 pair.1.2 L C).card := by
      simp

/-- Symmetric product bound for the right block. -/
theorem componentRightProduct_le_cutoff_pow_card
    {N M L : ℕ}
    (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L)
    (C : (largePrimeGraph pair.1.1 pair.1.2 L).ConnectedComponent) :
    componentRightProduct pair.1.1 pair.1.2 L C ≤
      boundedRatioCutoff M L ^
        (componentVertices pair.1.1 pair.1.2 L C).card := by
  unfold componentRightProduct
  calc
    (∏ v ∈ componentVertices pair.1.1 pair.1.2 L C,
        rightOccurrenceFactor pair.1.2 L v) ≤
        ∏ _v ∈ componentVertices pair.1.1 pair.1.2 L C,
          boundedRatioCutoff M L :=
      Finset.prod_le_prod
        (fun _v _hv => Nat.zero_le _)
        (fun v _hv => rightOccurrenceFactor_le_cutoff hN pair v)
    _ = boundedRatioCutoff M L ^
        (componentVertices pair.1.1 pair.1.2 L C).card := by
      simp

/-- The unsplit component product has the same sharp cardinal exponent. -/
theorem componentVertexProduct_le_cutoff_pow_card
    {N M L : ℕ}
    (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L)
    (C : (largePrimeGraph pair.1.1 pair.1.2 L).ConnectedComponent) :
    componentVertexProduct pair.1.1 pair.1.2 L C ≤
      boundedRatioCutoff M L ^
        (componentVertices pair.1.1 pair.1.2 L C).card := by
  unfold componentVertexProduct
  calc
    (∏ v ∈ componentVertices pair.1.1 pair.1.2 L C,
        twoStartCompleteVertexLabel pair.1.1 pair.1.2 L v) ≤
        ∏ _v ∈ componentVertices pair.1.1 pair.1.2 L C,
          boundedRatioCutoff M L :=
      Finset.prod_le_prod
        (fun _v _hv => Nat.zero_le _)
        (fun v _hv => twoStartCompleteVertexLabel_le_cutoff hN pair v)
    _ = boundedRatioCutoff M L ^
        (componentVertices pair.1.1 pair.1.2 L C).card := by
      simp

/-- The literal cutoff is nonzero whenever the bounded-ratio pair exists. -/
theorem one_le_boundedRatioCutoff_of_pair
    {N M L : ℕ}
    (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L) :
    1 ≤ boundedRatioCutoff M L := by
  have hcoords := pair_coordinates_two_le hN pair
  have hpair := mem_separatedBoundedRatioPairs.mp pair.2
  have hxM := (mem_boundedRatioBlock.mp hpair.1).2
  unfold boundedRatioCutoff
  omega

/-- A component with at most `K` vertices has left product at most `(M+L)^K`. -/
theorem componentLeftProduct_le_cutoff_pow
    {N M L K : ℕ}
    (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L)
    (C : (largePrimeGraph pair.1.1 pair.1.2 L).ConnectedComponent)
    (hcard : (componentVertices pair.1.1 pair.1.2 L C).card ≤ K) :
    componentLeftProduct pair.1.1 pair.1.2 L C ≤
      boundedRatioCutoff M L ^ K := by
  exact
    (componentLeftProduct_le_cutoff_pow_card hN pair C).trans
      (Nat.pow_le_pow_right
        (one_le_boundedRatioCutoff_of_pair hN pair) hcard)

/-- Symmetric bounded-size estimate for the right product. -/
theorem componentRightProduct_le_cutoff_pow
    {N M L K : ℕ}
    (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L)
    (C : (largePrimeGraph pair.1.1 pair.1.2 L).ConnectedComponent)
    (hcard : (componentVertices pair.1.1 pair.1.2 L C).card ≤ K) :
    componentRightProduct pair.1.1 pair.1.2 L C ≤
      boundedRatioCutoff M L ^ K := by
  exact
    (componentRightProduct_le_cutoff_pow_card hN pair C).trans
      (Nat.pow_le_pow_right
        (one_le_boundedRatioCutoff_of_pair hN pair) hcard)

/-- Bounded-size estimate for the complete component product. -/
theorem componentVertexProduct_le_cutoff_pow
    {N M L K : ℕ}
    (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L)
    (C : (largePrimeGraph pair.1.1 pair.1.2 L).ConnectedComponent)
    (hcard : (componentVertices pair.1.1 pair.1.2 L C).card ≤ K) :
    componentVertexProduct pair.1.1 pair.1.2 L C ≤
      boundedRatioCutoff M L ^ K := by
  exact
    (componentVertexProduct_le_cutoff_pow_card hN pair C).trans
      (Nat.pow_le_pow_right
        (one_le_boundedRatioCutoff_of_pair hN pair) hcard)

/-! ## Lemmas 17.20--17.21: exact normalized equation -/

/--
Every canonical residual component of a separated bounded-ratio pair gives
the precise square-class equation used in Lemma 17.20.
-/
theorem exists_component_square_class_equation
    {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L)
    {C : (largePrimeGraph pair.1.1 pair.1.2 L).ConnectedComponent}
    (hC : C ∈ canonicalResidualComponents
      A pair.1.1 pair.1.2 L) :
    ∃ d z : ℕ,
      0 < d ∧ Squarefree d ∧
      (∀ p : ℕ, p.Prime → p ∣ d → p ≤ L + 1) ∧
      0 < z ∧
      componentLeftProduct pair.1.1 pair.1.2 L C *
          componentRightProduct pair.1.1 pair.1.2 L C =
        d * z ^ 2 := by
  have hcoords := pair_coordinates_two_le hN pair
  have hpair :=
    mem_separatedBoundedRatioPairs.mp pair.2
  have hfree :
      ¬LargePrimeComponents.IsPinnedComponent
        pair.1.1 pair.1.2 L C :=
    not_isPinnedComponent_of_isNontrivialUnpinned
      (isNontrivialUnpinnedComponent_of_mem_canonicalResidualComponents hC)
  obtain ⟨d, z, hd, hdsq, hdsmooth, hz, heq⟩ :=
    LargePrimeComponents.exists_component_square_class
      hcoords.1 hcoords.2 hpair.2.2 C hfree
  refine ⟨d, z, hd, hdsq, hdsmooth, hz, ?_⟩
  rw [← componentVertexProduct_eq_left_mul_right]
  rw [← componentProduct_labels_eq_componentVertexProduct
    (show 1 ≤ pair.1.1 by omega)
    (show 1 ≤ pair.1.2 by omega) hpair.2.2 C]
  exact heq

/--
Canonical normalization of the right-hand polynomial factor.  This is the
literal finite conclusion of Lemma 17.20, before applying the degree-one,
Pell or Evertse--Silverman count according to its number of offsets.
-/
theorem exists_normalized_component_equation
    {N M A L : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L)
    {C : (largePrimeGraph pair.1.1 pair.1.2 L).ConnectedComponent}
    (hC : C ∈ canonicalResidualComponents
      A pair.1.1 pair.1.2 L) :
    ∃ d z e v : ℕ,
      0 < d ∧ Squarefree d ∧
      (∀ p : ℕ, p.Prime → p ∣ d → p ≤ L + 1) ∧
      0 < z ∧
      0 < e ∧ Squarefree e ∧
      0 < v ∧
      componentLeftProduct pair.1.1 pair.1.2 L C *
          componentRightProduct pair.1.1 pair.1.2 L C =
        d * z ^ 2 ∧
      componentRightProduct pair.1.1 pair.1.2 L C =
        e * v ^ 2 ∧
      e =
        ComponentNormalization.squarefreeKernel
          (d * componentLeftProduct pair.1.1 pair.1.2 L C) ∧
      e ∣ d * componentLeftProduct pair.1.1 pair.1.2 L C ∧
      e ≤ d * componentLeftProduct pair.1.1 pair.1.2 L C := by
  obtain ⟨d, z, hd, hdsq, hdsmooth, hz, heq⟩ :=
    exists_component_square_class_equation hN pair hC
  have hcoords := pair_coordinates_two_le hN pair
  have hleft :=
    componentLeftProduct_pos hcoords.1 C
  have hright :=
    componentRightProduct_pos hcoords.2 C
  obtain ⟨e, v, he, hesq, hv, hrightEq, heCanonical,
      heDvd, heLe⟩ :=
    ComponentNormalization.exists_normalized_right_factor
      hleft hright hd hz hdsq heq
  exact
    ⟨d, z, e, v, hd, hdsq, hdsmooth, hz, he, hesq, hv,
      heq, hrightEq, heCanonical, heDvd, heLe⟩

/--
Polynomial-height package for a bounded component.  Besides the normalized
equations it records the sharp elementary bounds

`d, P_I(x), Q_J(y) ≤ (M+L)^K` and `e ≤ (M+L)^(2K)`.
-/
theorem exists_normalized_component_equation_with_height
    {N M A L K : ℕ} (hN : 2 ≤ N)
    (pair : SeparatedBoundedRatioPair N M L)
    {C : (largePrimeGraph pair.1.1 pair.1.2 L).ConnectedComponent}
    (hC : C ∈ canonicalResidualComponents
      A pair.1.1 pair.1.2 L)
    (hcard : Fintype.card C.supp ≤ K) :
    ∃ d z e v : ℕ,
      0 < d ∧ Squarefree d ∧
      (∀ p : ℕ, p.Prime → p ∣ d → p ≤ L + 1) ∧
      0 < z ∧
      0 < e ∧ Squarefree e ∧
      0 < v ∧
      componentLeftProduct pair.1.1 pair.1.2 L C *
          componentRightProduct pair.1.1 pair.1.2 L C =
        d * z ^ 2 ∧
      componentRightProduct pair.1.1 pair.1.2 L C =
        e * v ^ 2 ∧
      e =
        ComponentNormalization.squarefreeKernel
          (d * componentLeftProduct pair.1.1 pair.1.2 L C) ∧
      d ≤ boundedRatioCutoff M L ^ K ∧
      componentLeftProduct pair.1.1 pair.1.2 L C ≤
        boundedRatioCutoff M L ^ K ∧
      componentRightProduct pair.1.1 pair.1.2 L C ≤
        boundedRatioCutoff M L ^ K ∧
      e ≤ boundedRatioCutoff M L ^ (2 * K) := by
  obtain ⟨d, z, e, v, hd, hdsq, hdsmooth, hz, he, hesq, hv,
      heq, hrightEq, heCanonical, _heDvd, heLe⟩ :=
    exists_normalized_component_equation hN pair hC
  have hcard' :
      (componentVertices pair.1.1 pair.1.2 L C).card ≤ K := by
    rw [ComponentProductParity.card_componentVertices]
    exact hcard
  have hleft :
      componentLeftProduct pair.1.1 pair.1.2 L C ≤
        boundedRatioCutoff M L ^ K :=
    componentLeftProduct_le_cutoff_pow hN pair C hcard'
  have hright :
      componentRightProduct pair.1.1 pair.1.2 L C ≤
        boundedRatioCutoff M L ^ K :=
    componentRightProduct_le_cutoff_pow hN pair C hcard'
  have hwhole :
      componentVertexProduct pair.1.1 pair.1.2 L C ≤
        boundedRatioCutoff M L ^ K :=
    componentVertexProduct_le_cutoff_pow hN pair C hcard'
  have hdWhole :
      d ≤ componentVertexProduct pair.1.1 pair.1.2 L C := by
    calc
      d ≤ d * z ^ 2 :=
        Nat.le_mul_of_pos_right d (by positivity)
      _ =
          componentLeftProduct pair.1.1 pair.1.2 L C *
            componentRightProduct pair.1.1 pair.1.2 L C :=
        heq.symm
      _ = componentVertexProduct pair.1.1 pair.1.2 L C :=
        (componentVertexProduct_eq_left_mul_right
          pair.1.1 pair.1.2 L C).symm
  have hdBound :
      d ≤ boundedRatioCutoff M L ^ K :=
    hdWhole.trans hwhole
  have heBound :
      e ≤ boundedRatioCutoff M L ^ (2 * K) := by
    calc
      e ≤ d *
          componentLeftProduct pair.1.1 pair.1.2 L C :=
        heLe
      _ ≤
          boundedRatioCutoff M L ^ K *
            boundedRatioCutoff M L ^ K :=
        Nat.mul_le_mul hdBound hleft
      _ = boundedRatioCutoff M L ^ (2 * K) := by
        rw [← pow_add]
        congr 1
        omega
  exact
    ⟨d, z, e, v, hd, hdsq, hdsmooth, hz, he, hesq, hv,
      heq, hrightEq, heCanonical, hdBound, hleft, hright, heBound⟩

end

end BoundedRatioComponentNormalization
end PaperC
