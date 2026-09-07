import PaperCV282.ClosureAlgebraStartTuple
import PaperCV282.ValueSquareRelations
import PaperC.Affine.RationalChannelCode

/-! # The boundary and affine character for every tuple of start trees -/
namespace PaperC.V282.ClosureAlgebraTupleBoundary

open Affine ClosureAlgebraStartTuple PrescribedValues ValueSquareRelations RationalChannelCode
open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- The boundary map retains the occurrence label of every vertex. -/
def tupleBoundary (L : ℕ) : (ι × Fin L → F₂) →ₗ[F₂] (ι × Fin (L+1) → F₂) where
  toFun u v := startCompleteBoundary L (fun j => u (v.1,j)) v.2
  map_add' u v := by funext i; exact congrFun (map_add (startCompleteBoundary L) _ _) i.2
  map_smul' c u := by funext i; exact congrFun (map_smul (startCompleteBoundary L) c _) i.2

/-- The actual positive integers appearing at the labelled vertices. -/
def tupleVertex (L : ℕ) (x : ι → ℕ) (v : ι × Fin (L+1)) : ℕ :=
  startCompleteVertexLabel (x v.1) L v.2

omit [Fintype ι] in
theorem tupleBoundary_injective (L : ℕ) : Function.Injective (tupleBoundary (ι := ι) L) := by
  intro u v h
  funext i
  have hh : startCompleteBoundary L (fun j => u (i.1,j)) =
      startCompleteBoundary L (fun j => v (i.1,j)) := by
    funext j
    exact congrFun h (i.1,j)
  exact congrFun (startCompleteBoundary_injective L hh) i.2

omit [Fintype ι] in
theorem tupleBoundary_even (L : ℕ) (u : ι × Fin L → F₂) (i : ι) :
    ∑ j, tupleBoundary L u (i,j) = 0 :=
  startVertexSum_startCompleteBoundary_eq_zero (fun j => u (i,j))

omit [Fintype ι] in
/-- Every tuple of even vertex selections has a unique edge preimage. -/
theorem existsUnique_tupleBoundary (L : ℕ) (w : ι × Fin (L+1) → F₂)
    (hw : ∀ i, ∑ j, w (i,j) = 0) : ∃! u, tupleBoundary L u = w := by
  have hh : ∀ i, ∃ u, startCompleteBoundary L u = fun j => w (i,j) := by
    intro i
    exact (existsUnique_startCompleteBoundary_eq (hw i)).exists
  choose u hu using hh
  refine ⟨fun i => u i.1 i.2, ?_, ?_⟩
  · funext i
    exact congrFun (hu i.1) i.2
  · intro v hv
    apply tupleBoundary_injective L
    exact hv.trans (by funext i; exact (congrFun (hu i.1) i.2).symm)

/-- The actual linear equations pair with the valuation rows on their boundary. -/
theorem dotProduct_tuple_boundary (M L : ℕ) (x : ι → ℕ) (omega : SampleSpace M)
    (u : ι × Fin L → F₂) :
    dotProduct u (tupleSystem M L x omega) =
      dotProduct (tupleBoundary L u) (valueSystem M (tupleVertex L x) omega) := by
  simp only [dotProduct, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  exact sum_startSystem_eq_sum_completeBoundary M (x i) L omega (fun j => u (i,j))

/-- A tuple relation is exactly a full-value relation on its boundary. -/
theorem mem_tuple_relation_iff_boundary (M L : ℕ) (x : ι → ℕ) (u : ι × Fin L → F₂) :
    u ∈ RelationSpace (tupleSystem M L x) ↔
      tupleBoundary L u ∈ RelationSpace (valueSystem M (tupleVertex L x)) := by
  simp only [RelationSpace, LinearMap.mem_ker, LinearMap.ext_iff, relationMap_apply,
    relationFunctional_apply, LinearMap.zero_apply, dotProduct_tuple_boundary]

/-- The affine character is the sum of the selected root bits for all blocks. -/
theorem tuple_affine_character (L : ℕ) (u : ι × Fin L → F₂) :
    dotProduct u (tupleRhs L) = ∑ i, tupleBoundary L u (i,startRootVertex L) := by
  simp only [dotProduct, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  exact (startCompleteBoundary_root_eq_dot_startRhs (fun j => u (i,j))).symm

omit [Fintype ι] in
theorem tupleVertex_pos {L : ℕ} (x : ι → ℕ) (hx : ∀ i, 2 ≤ x i) (v : ι × Fin (L+1)) :
    0 < tupleVertex L x v := by
  have hv := v.2.isLt
  have hh := hx v.1
  simp only [tupleVertex, startCompleteVertexLabel]
  split_ifs <;> omega

omit [Fintype ι] in
theorem tupleVertex_le {M L : ℕ} (x : ι → ℕ) (hcut : ∀ i, x i + L ≤ M)
    (v : ι × Fin (L+1)) : tupleVertex L x v ≤ M := by
  have hv := v.2.isLt
  have hh := hcut v.1
  simp only [tupleVertex, startCompleteVertexLabel]
  split_ifs <;> omega

/-- The square-product interpretation is valid for any finite number of windows. -/
theorem tuple_relation_iff_square_product {M L : ℕ} (x : ι → ℕ) (hx : ∀ i, 2 ≤ x i)
    (hcut : ∀ i, x i + L ≤ M) (u : ι × Fin L → F₂) :
    u ∈ RelationSpace (tupleSystem M L x) ↔
      ∃ r : ℕ, ∏ v ∈ relationSupport (tupleBoundary L u), tupleVertex L x v = r^2 := by
  rw [mem_tuple_relation_iff_boundary]
  exact mem_value_relation_iff_square_product M (tupleVertex L x)
    (tupleVertex_pos x hx) (tupleVertex_le x hcut) _

end
end PaperC.V282.ClosureAlgebraTupleBoundary
