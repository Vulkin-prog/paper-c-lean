import PaperC.Coding.TwoParityColumnCode
import PaperC.Combinatorics.ComponentProductParity

/-!
# Instantiating the Section 8 component code

This file turns a finite list of unpinned large-prime components into the
binary matrix `Φ` from Theorem 8.1.  Its rows are:

* the parity of the component product at every prime `p ≤ L + 1`;
* the parity of the number of left vertices;
* the parity of the number of right vertices.

A kernel word therefore selects an even number of vertices on each side and
a square product of all selected component labels.  Large-prime coordinates
need not be put in the matrix: they vanish component by component.
-/

namespace PaperC
namespace AlignedComponentCode

open scoped BigOperators
open ComponentProductParity
open LargePrimeComponents
open LargePrimeGraph
open LargePrimeOccurrences

noncomputable section

/-- Whether an occurrence belongs to the left complete boundary. -/
def IsLeftOccurrence {L : ℕ} : Occurrence L → Prop
  | Sum.inl _ => True
  | Sum.inr _ => False

/-- Whether an occurrence belongs to the right complete boundary. -/
def IsRightOccurrence {L : ℕ} : Occurrence L → Prop
  | Sum.inl _ => False
  | Sum.inr _ => True

instance instDecidableIsLeftOccurrence {L : ℕ} :
    DecidablePred (IsLeftOccurrence : Occurrence L → Prop) :=
  fun v ↦
    match v with
    | Sum.inl _ => isTrue trivial
    | Sum.inr _ => isFalse id

instance instDecidableIsRightOccurrence {L : ℕ} :
    DecidablePred (IsRightOccurrence : Occurrence L → Prop) :=
  fun v ↦
    match v with
    | Sum.inl _ => isFalse id
    | Sum.inr _ => isTrue trivial

/-- Number of left vertices in a connected component. -/
noncomputable def componentLeftCount
    (x y L : ℕ)
    (C : (largePrimeGraph x y L).ConnectedComponent) : ℕ := by
  classical
  exact
    ((componentVertices x y L C).filter IsLeftOccurrence).card

/-- Number of right vertices in a connected component. -/
noncomputable def componentRightCount
    (x y L : ℕ)
    (C : (largePrimeGraph x y L).ConnectedComponent) : ℕ := by
  classical
  exact
    ((componentVertices x y L C).filter IsRightOccurrence).card

/-- The left and right counts partition the vertices of a component. -/
theorem componentLeftCount_add_rightCount
    (x y L : ℕ)
    (C : (largePrimeGraph x y L).ConnectedComponent) :
    componentLeftCount x y L C +
        componentRightCount x y L C =
      (componentVertices x y L C).card := by
  classical
  have hfilter :
      (componentVertices x y L C).filter IsRightOccurrence =
        (componentVertices x y L C).filter
          (fun v ↦ ¬IsLeftOccurrence v) := by
    ext v
    cases v <;>
      simp [IsLeftOccurrence, IsRightOccurrence]
  unfold componentLeftCount componentRightCount
  rw [hfilter]
  exact
    Finset.card_filter_add_card_filter_not
      (s := componentVertices x y L C) IsLeftOccurrence

/-- The small-prime block of the column attached to one component. -/
noncomputable def componentSmallParityColumn
    (x y L : ℕ)
    (C : (largePrimeGraph x y L).ConnectedComponent) :
    Fin (PrimesUpTo.count (L + 1)) → F₂ :=
  fun j ↦
    parityVec (componentVertexProduct x y L C)
      (PrimesUpTo.smallPrime (L + 1) j)

/-- The linear map whose columns are the paper's component vectors `Φ(C)`. -/
noncomputable def componentCodeMap
    {m x y L : ℕ}
    (component :
      Fin m → (largePrimeGraph x y L).ConnectedComponent) :
    (Fin m → F₂) →ₗ[F₂]
      (Fin (PrimesUpTo.count (L + 1) + 2) → F₂) :=
  TwoParityColumnCode.twoAugmentedColumnMap
    (fun i ↦ componentSmallParityColumn x y L (component i))
    (fun i ↦ (componentLeftCount x y L (component i) : F₂))
    (fun i ↦ (componentRightCount x y L (component i) : F₂))

/-- The component code has codimension at most `π(L+1)+2`. -/
theorem componentCode_finrank_ge
    {m x y L : ℕ}
    (component :
      Fin m → (largePrimeGraph x y L).ConnectedComponent) :
    m - (PrimesUpTo.count (L + 1) + 2) ≤
      Module.finrank F₂ (LinearMap.ker (componentCodeMap component)) := by
  exact
    TwoParityColumnCode.columns_sub_twoAugmentedRows_le_finrank_ker
      (fun i ↦ componentSmallParityColumn x y L (component i))
      (fun i ↦ (componentLeftCount x y L (component i) : F₂))
      (fun i ↦ (componentRightCount x y L (component i) : F₂))

/-- A kernel word selects an even total number of left vertices. -/
theorem kernelWord_leftCount_even
    {m x y L : ℕ}
    (component :
      Fin m → (largePrimeGraph x y L).ConnectedComponent)
    (word : Fin m → F₂)
    (hword : word ∈ LinearMap.ker (componentCodeMap component)) :
    Even
      (∑ i ∈ HammingBound.wordSupport word,
        componentLeftCount x y L (component i)) := by
  have hzero :
      ∑ i ∈ HammingBound.wordSupport word,
          (componentLeftCount x y L (component i) : F₂) =
        0 := by
    exact
      TwoParityColumnCode.kernel_left_selected_sum_eq_zero
        (fun i ↦ componentSmallParityColumn x y L (component i))
        (fun i ↦ (componentLeftCount x y L (component i) : F₂))
        (fun i ↦ (componentRightCount x y L (component i) : F₂))
        word hword
  have hcast :
      (((∑ i ∈ HammingBound.wordSupport word,
          componentLeftCount x y L (component i)) : ℕ) : F₂) =
        0 := by
    simpa using hzero
  exact even_iff_two_dvd.mpr
    ((ZMod.natCast_eq_zero_iff
      (∑ i ∈ HammingBound.wordSupport word,
        componentLeftCount x y L (component i)) 2).mp hcast)

/-- A kernel word selects an even total number of right vertices. -/
theorem kernelWord_rightCount_even
    {m x y L : ℕ}
    (component :
      Fin m → (largePrimeGraph x y L).ConnectedComponent)
    (word : Fin m → F₂)
    (hword : word ∈ LinearMap.ker (componentCodeMap component)) :
    Even
      (∑ i ∈ HammingBound.wordSupport word,
        componentRightCount x y L (component i)) := by
  have hzero :
      ∑ i ∈ HammingBound.wordSupport word,
          (componentRightCount x y L (component i) : F₂) =
        0 := by
    exact
      TwoParityColumnCode.kernel_right_selected_sum_eq_zero
        (fun i ↦ componentSmallParityColumn x y L (component i))
        (fun i ↦ (componentLeftCount x y L (component i) : F₂))
        (fun i ↦ (componentRightCount x y L (component i) : F₂))
        word hword
  have hcast :
      (((∑ i ∈ HammingBound.wordSupport word,
          componentRightCount x y L (component i)) : ℕ) : F₂) =
        0 := by
    simpa using hzero
  exact even_iff_two_dvd.mpr
    ((ZMod.natCast_eq_zero_iff
      (∑ i ∈ HammingBound.wordSupport word,
        componentRightCount x y L (component i)) 2).mp hcast)

/--
A kernel word selects component products whose total product is a square.
The matrix handles `p ≤ L+1`; unpinnedness handles all larger primes.
-/
theorem kernelWord_componentProducts_square
    {m x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (component :
      Fin m → (largePrimeGraph x y L).ConnectedComponent)
    (hfree : ∀ i, ¬IsPinnedComponent x y L (component i))
    (word : Fin m → F₂)
    (hword : word ∈ LinearMap.ker (componentCodeMap component)) :
    ∃ q : ℕ,
      ∏ i ∈ HammingBound.wordSupport word,
          componentVertexProduct x y L (component i) =
        q ^ 2 := by
  apply
    (sum_parityVec_eq_zero_iff_prod_eq_sq
      (HammingBound.wordSupport word)
      (fun i ↦ componentVertexProduct x y L (component i))
      ?_).mp
  · ext p
    by_cases hp :
        ∃ j : Fin (PrimesUpTo.count (L + 1)),
          PrimesUpTo.smallPrime (L + 1) j = p
    · obtain ⟨j, rfl⟩ := hp
      rw [Finsupp.finsetSum_apply]
      simp only [Finsupp.zero_apply]
      rw [DefectCodeRank.sum_wordSupport_eq_weighted_sum]
      have hzero :=
        congrFun (LinearMap.mem_ker.mp hword)
          j.castSucc.castSucc
      simpa [componentCodeMap, componentSmallParityColumn,
        TwoParityColumnCode.twoAugmentedColumnMap_apply_small]
        using hzero
    · have hzero :
          ∀ i : Fin m,
            parityVec
                (componentVertexProduct x y L (component i)) p =
              0 := by
        intro i
        apply Classical.byContradiction
        intro hne
        exact hp
          (componentVertexProduct_smallPrime_coverage
            hx hy (component i) (hfree i) p hne)
      simp [hzero]
  · intro i hi
    exact (componentVertexProduct_pos hx hy (component i)).ne'

/-- All three arithmetic consequences of a component-code kernel word. -/
theorem kernelWord_parity_package
    {m x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (component :
      Fin m → (largePrimeGraph x y L).ConnectedComponent)
    (hfree : ∀ i, ¬IsPinnedComponent x y L (component i))
    (word : Fin m → F₂)
    (hword : word ∈ LinearMap.ker (componentCodeMap component)) :
    Even
        (∑ i ∈ HammingBound.wordSupport word,
          componentLeftCount x y L (component i)) ∧
      Even
        (∑ i ∈ HammingBound.wordSupport word,
          componentRightCount x y L (component i)) ∧
      ∃ q : ℕ,
        ∏ i ∈ HammingBound.wordSupport word,
            componentVertexProduct x y L (component i) =
          q ^ 2 :=
  ⟨kernelWord_leftCount_even component word hword,
    kernelWord_rightCount_even component word hword,
    kernelWord_componentProducts_square
      hx hy component hfree word hword⟩

end

end AlignedComponentCode
end PaperC
