import PaperCV282.ClosureAlgebraTupleBoundary

/-! # Tuples of even square-product subsets

The target of the equivalence is a literal tuple of finite vertex subsets,
not a postulated linear subspace. Each subset is even, their joint product
is a square, and the affine character counts the selected left endpoints.
Occurrence labels also make the result valid for overlapping windows.
-/
namespace PaperC.V282.ClosureAlgebraSquareTuple

open Affine ClosureAlgebraStartTuple ClosureAlgebraTupleBoundary ValueSquareRelations
open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- A tuple of subsets as binary vertex coefficients. -/
def selectionVector {L : ℕ} (S : ι → Finset (Fin (L+1))) : ι × Fin (L+1) → F₂ :=
  fun v => if v.2 ∈ S v.1 then 1 else 0

/-- The selected vertices in each tuple block. -/
def vertexSubsets {L : ℕ} (w : ι × Fin (L+1) → F₂) : ι → Finset (Fin (L+1)) :=
  fun i => Finset.univ.filter (fun j => w (i,j) ≠ 0)

omit [Fintype ι] in
theorem selectionVector_vertexSubsets {L : ℕ} (w : ι × Fin (L+1) → F₂) :
    selectionVector (vertexSubsets w) = w := by
  funext v
  have hb : w v = 0 ∨ w v = 1 := (by decide : ∀ a : F₂, a=0 ∨ a=1) (w v)
  rcases hb with h | h <;> simp [selectionVector, vertexSubsets, h]

omit [Fintype ι] in
theorem vertexSubsets_selectionVector {L : ℕ} (S : ι → Finset (Fin (L+1))) :
    vertexSubsets (selectionVector S) = S := by
  funext i
  ext j
  simp [vertexSubsets, selectionVector]

omit [Fintype ι] in
theorem selection_even_iff {L : ℕ} (S : ι → Finset (Fin (L+1))) (i : ι) :
    (∑ j, selectionVector S (i,j)) = 0 ↔ Even (S i).card := by
  have hs : (∑ j, selectionVector S (i,j)) = ((S i).card : F₂) := by
    simp [selectionVector]
  rw [hs, ZMod.natCast_eq_zero_iff, even_iff_two_dvd]

theorem selection_product {L : ℕ} (x : ι → ℕ) (S : ι → Finset (Fin (L+1))) :
    (∏ v ∈ relationSupport (selectionVector S), tupleVertex L x v) =
      ∏ i, ∏ j ∈ S i, startCompleteVertexLabel (x i) L j := by
  simp [relationSupport, selectionVector, Finset.prod_filter, Fintype.prod_prod_type,
    tupleVertex]

/-- The manuscript's tuple of even subsets with square total product. -/
def EvenSquareTuple (L : ℕ) (x : ι → ℕ) :=
  {S : ι → Finset (Fin (L+1)) // (∀ i, Even (S i).card) ∧
    ∃ r : ℕ, (∏ i, ∏ j ∈ S i, startCompleteVertexLabel (x i) L j) = r^2}

/-- Boundary subsets of an actual tuple relation. -/
def relationToSquareTuple {M L : ℕ} (x : ι → ℕ) (hx : ∀ i, 2 ≤ x i)
    (hcut : ∀ i, x i+L ≤ M) :
    RelationSpace (tupleSystem M L x) → EvenSquareTuple L x := fun u =>
  ⟨vertexSubsets (tupleBoundary L u), by
    constructor
    · intro i
      rw [← selection_even_iff, selectionVector_vertexSubsets]
      exact tupleBoundary_even L u i
    · have hp := (tuple_relation_iff_square_product x hx hcut u).mp u.property
      rw [← selectionVector_vertexSubsets (tupleBoundary L u.val), selection_product] at hp
      exact hp⟩

theorem relationToSquareTuple_injective {M L : ℕ} (x : ι → ℕ) (hx : ∀ i, 2 ≤ x i)
    (hcut : ∀ i, x i+L ≤ M) : Function.Injective (relationToSquareTuple x hx hcut) := by
  intro u v h
  apply Subtype.ext
  apply tupleBoundary_injective L
  have hs := congrArg (fun S : EvenSquareTuple L x => selectionVector S.val) h
  simpa only [relationToSquareTuple, selectionVector_vertexSubsets] using hs

theorem relationToSquareTuple_surjective {M L : ℕ} (x : ι → ℕ) (hx : ∀ i, 2 ≤ x i)
    (hcut : ∀ i, x i+L ≤ M) : Function.Surjective (relationToSquareTuple x hx hcut) := by
  intro S
  have he : ∀ i, ∑ j, selectionVector S.val (i,j) = 0 :=
    fun i => (selection_even_iff S.val i).mpr (S.property.1 i)
  obtain ⟨u,hu,_⟩ := existsUnique_tupleBoundary L (selectionVector S.val) he
  have hr : u ∈ RelationSpace (tupleSystem M L x) := by
    rw [tuple_relation_iff_square_product x hx hcut, hu, selection_product]
    exact S.property.2
  refine ⟨⟨u,hr⟩, ?_⟩
  apply Subtype.ext
  change vertexSubsets (tupleBoundary L u) = S.val
  rw [hu, vertexSubsets_selectionVector]

/-- Lemma 2.2: the exact bijection for every finite tuple of complete windows. -/
def lemma_two_two {M L : ℕ} (x : ι → ℕ) (hx : ∀ i, 2 ≤ x i)
    (hcut : ∀ i, x i+L ≤ M) :
    RelationSpace (tupleSystem M L x) ≃ EvenSquareTuple L x :=
  Equiv.ofBijective (relationToSquareTuple x hx hcut)
    ⟨relationToSquareTuple_injective x hx hcut, relationToSquareTuple_surjective x hx hcut⟩

/-- Its character is exactly the parity of the selected left endpoints. -/
theorem lemma_two_two_character {M L : ℕ} (x : ι → ℕ) (hx : ∀ i, 2 ≤ x i)
    (hcut : ∀ i, x i+L ≤ M) (u : RelationSpace (tupleSystem M L x)) :
    relationCharacter (tupleSystem M L x) (tupleRhs L) u =
      ∑ i, if startRootVertex L ∈ (lemma_two_two x hx hcut u).val i then (1 : F₂) else 0 := by
  rw [relationCharacter_apply, tuple_affine_character]
  apply Finset.sum_congr rfl
  intro i _
  have h := congrFun (selectionVector_vertexSubsets (tupleBoundary L u)) (i,startRootVertex L)
  exact h.symm

end
end PaperC.V282.ClosureAlgebraSquareTuple
