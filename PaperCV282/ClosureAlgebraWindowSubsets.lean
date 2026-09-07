import PaperCV282.ClosureAlgebraSquareTuple
import PaperC.Affine.RelationalPrimeAssignment

/-! # Literal integer-window form of the tuple square-product bijection -/
namespace PaperC.V282.ClosureAlgebraWindowSubsets

open Affine RelationalPrimeAssignment ClosureAlgebraStartTuple ClosureAlgebraSquareTuple
open scoped BigOperators

noncomputable section

/-- The integer vertices of the complete start window. -/
def windowVertices (x L : ℕ) : Finset ℕ :=
  Finset.univ.image (startCompleteVertexLabel x L)

theorem windowVertices_eq_interval {x L : ℕ} (hx : 1 ≤ x) :
    windowVertices x L = Finset.Icc (x-1) (x+L-1) := by
  have hl (j : Fin (L+1)) : startCompleteVertexLabel x L j = x-1+j.val := by
    unfold startCompleteVertexLabel
    split_ifs <;> omega
  ext n
  simp only [windowVertices, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_Icc]
  constructor
  · rintro ⟨j,rfl⟩
    rw [hl]
    have hh := j.isLt
    omega
  · intro h
    refine ⟨⟨n-(x-1), by omega⟩, ?_⟩
    rw [hl]
    simp only
    omega

/-- A literal subset of the integer window. -/
def WindowSubset (x L : ℕ) := {S : Finset ℕ // S ⊆ windowVertices x L}

/-- Relabel an offset subset by its actual integer values. -/
def windowSubsetMap (x L : ℕ) (S : Finset (Fin (L+1))) : WindowSubset x L :=
  ⟨S.image (startCompleteVertexLabel x L),
    Finset.image_subset_image (Finset.subset_univ S)⟩

theorem windowSubsetMap_bijective {x L : ℕ} (hx : 1 ≤ x) :
    Function.Bijective (windowSubsetMap x L) := by
  constructor
  · intro S T h
    apply Finset.image_injective (startCompleteVertexLabel_injective hx)
    exact congrArg Subtype.val h
  · intro S
    refine ⟨Finset.univ.filter (fun j => startCompleteVertexLabel x L j ∈ S.val), ?_⟩
    apply Subtype.ext
    ext n
    change n ∈ Finset.image _ _ ↔ n ∈ S.val
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j,hj,rfl⟩
      exact hj
    · intro hn
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp (S.property hn)
      exact ⟨j,hn,rfl⟩

/-- No vertices are lost or identified within a complete window. -/
def windowSubsetEquiv {x L : ℕ} (hx : 1 ≤ x) : Finset (Fin (L+1)) ≃ WindowSubset x L :=
  Equiv.ofBijective (windowSubsetMap x L) (windowSubsetMap_bijective hx)

theorem windowSubset_card {x L : ℕ} (hx : 1 ≤ x) (S : Finset (Fin (L+1))) :
    (windowSubsetEquiv hx S).val.card = S.card :=
  Finset.card_image_of_injective S (startCompleteVertexLabel_injective hx)

theorem windowSubset_product {x L : ℕ} (hx : 1 ≤ x) (S : Finset (Fin (L+1))) :
    (∏ n ∈ (windowSubsetEquiv hx S).val, n) = ∏ j ∈ S, startCompleteVertexLabel x L j := by
  exact Finset.prod_image (fun _ _ _ _ h => startCompleteVertexLabel_injective hx h)

theorem windowSubset_root {x L : ℕ} (hx : 1 ≤ x) (S : Finset (Fin (L+1))) :
    x-1 ∈ (windowSubsetEquiv hx S).val ↔ startRootVertex L ∈ S := by
  change x-1 ∈ S.image (startCompleteVertexLabel x L) ↔ _
  rw [← startCompleteVertexLabel_root x L]
  constructor
  · intro h
    obtain ⟨j,hj,hjroot⟩ := Finset.mem_image.mp h
    exact startCompleteVertexLabel_injective hx hjroot ▸ hj
  · intro h
    exact Finset.mem_image_of_mem _ h

variable {ι : Type*} [Fintype ι]

/-- Tuples of actual integer subsets, each even, with square combined product. -/
def IntegerSquareTuple (L : ℕ) (x : ι → ℕ) :=
  {S : (i : ι) → WindowSubset (x i) L //
    (∀ i, Even (S i).val.card) ∧ ∃ r : ℕ, (∏ i, ∏ n ∈ (S i).val, n) = r^2}

/-- Offset and integer formulations preserve both evenness and the product. -/
def integerSquareTupleEquiv (L : ℕ) (x : ι → ℕ) (hx : ∀ i, 1 ≤ x i) :
    EvenSquareTuple L x ≃ IntegerSquareTuple L x :=
  (Equiv.piCongrRight (fun i => windowSubsetEquiv (L := L) (hx i))).subtypeEquiv (by
    intro S
    change ((∀ i, Even (S i).card) ∧ _) ↔
      ((∀ i, Even (windowSubsetEquiv (hx i) (S i)).val.card) ∧ _)
    simp only [Equiv.piCongrRight_apply, Pi.map_apply, windowSubset_card, windowSubset_product])

/-- The exact printed Lemma 2.2, now with subsets of the integer windows themselves. -/
def lemma_two_two_integer_windows {M L : ℕ} (x : ι → ℕ) (hx : ∀ i, 2 ≤ x i)
    (hcut : ∀ i, x i+L ≤ M) :
    RelationSpace (tupleSystem M L x) ≃ IntegerSquareTuple L x :=
  (lemma_two_two x hx hcut).trans (integerSquareTupleEquiv L x (fun i => by have := hx i; omega))

/-- The affine character reads precisely the selected integer left endpoints. -/
theorem integer_window_character {M L : ℕ} (x : ι → ℕ) (hx : ∀ i, 2 ≤ x i)
    (hcut : ∀ i, x i+L ≤ M) (u : RelationSpace (tupleSystem M L x)) :
    relationCharacter (tupleSystem M L x) (tupleRhs L) u =
      ∑ i, if x i-1 ∈ ((lemma_two_two_integer_windows x hx hcut u).val i).val then
        (1 : F₂) else 0 := by
  rw [lemma_two_two_character x hx hcut u]
  apply Finset.sum_congr rfl
  intro i _
  change (if startRootVertex L ∈ (lemma_two_two x hx hcut u).val i then (1 : F₂) else 0) =
    if x i-1 ∈ (windowSubsetEquiv (show 1 ≤ x i by have := hx i; omega)
      ((lemma_two_two x hx hcut u).val i)).val then 1 else 0
  simp only [windowSubset_root]

end
end PaperC.V282.ClosureAlgebraWindowSubsets
