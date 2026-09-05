import PaperCV282.PrescribedValues
import PaperCV282.ValueRelations
import PaperCV282.WindowValues
import PaperC.Affine.StartBoundaryRange
import PaperC.Affine.RationalChannelCode

/-!
# Actual two-window values and the two start parities

The two complete vertex blocks have length `L + 1`. The actual boundary
map identifies start relations with full-value relations of even parity in
each block separately. This instantiates the finite comparison underlying
Proposition 3.26. The correction counts full-value hosts, including hosts
that have no nonzero start relation. No arithmetic host bound is asserted.
-/

namespace PaperC.V282.TwoWindowParity

open Affine PrescribedValues ValueRelations
open scoped BigOperators

local instance : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

noncomputable section

/-- The actual valuation rows of both complete vertex blocks. -/
def twoValueSystem (M x y L : ℕ) :
    SampleSpace M →ₗ[F₂] (Sum (Fin (L + 1)) (Fin (L + 1)) → F₂) :=
  valueSystem M (twoStartCompleteVertexLabel x y L)

/-- The two block sums are separate parity equations. -/
def blockParity (L : ℕ) :
    (Sum (Fin (L + 1)) (Fin (L + 1)) → F₂) →ₗ[F₂] (Fin 2 → F₂) where
  toFun w k := if k = 0 then ∑ i, w (Sum.inl i) else ∑ i, w (Sum.inr i)
  map_add' u v := by
    funext k
    fin_cases k <;> simp [Finset.sum_add_distrib]
  map_smul' c u := by
    funext k
    fin_cases k <;> simp [Finset.mul_sum, smul_eq_mul]

@[simp]
theorem blockParity_zero (L : ℕ)
    (w : Sum (Fin (L + 1)) (Fin (L + 1)) → F₂) :
    blockParity L w 0 = startVertexSum L (fun i => w (Sum.inl i)) := by
  simp [blockParity, startVertexSum]

@[simp]
theorem blockParity_one (L : ℕ)
    (w : Sum (Fin (L + 1)) (Fin (L + 1)) → F₂) :
    blockParity L w 1 = startVertexSum L (fun i => w (Sum.inr i)) := by
  simp [blockParity, startVertexSum]

/-- The actual start equations pair with the boundary of their coefficients. -/
theorem dotProduct_start_eq_boundary_values (M x y L : ℕ)
    (ω : SampleSpace M) (u : Sum (Fin L) (Fin L) → F₂) :
    dotProduct u (twoStartSystem M x y L ω) =
      dotProduct (twoStartCompleteBoundary L u) (twoValueSystem M x y L ω) := by
  exact RationalChannelCode.dotProduct_twoStartSystem_eq_sum_completeBoundary M x y L ω u

/-- A coefficient vector is a start relation exactly when its boundary is a value relation. -/
theorem mem_start_relation_iff_boundary_value_relation (M x y L : ℕ)
    (u : Sum (Fin L) (Fin L) → F₂) :
    u ∈ RelationSpace (twoStartSystem M x y L) ↔
      twoStartCompleteBoundary L u ∈ RelationSpace (twoValueSystem M x y L) := by
  simp only [RelationSpace, LinearMap.mem_ker, LinearMap.ext_iff,
    relationMap_apply, relationFunctional_apply, LinearMap.zero_apply,
    dotProduct_start_eq_boundary_values]

/-- Every complete boundary satisfies both block parities. -/
theorem blockParity_boundary_eq_zero (L : ℕ)
    (u : Sum (Fin L) (Fin L) → F₂) :
    blockParity L (twoStartCompleteBoundary L u) = 0 := by
  funext k
  fin_cases k
  · simpa using startVertexSum_startCompleteBoundary_eq_zero (fun i => u (Sum.inl i))
  · simpa using startVertexSum_startCompleteBoundary_eq_zero (fun i => u (Sum.inr i))

/-- Every vector satisfying both parities is a complete boundary. -/
theorem exists_boundary_of_blockParity_eq_zero (L : ℕ)
    (w : Sum (Fin (L + 1)) (Fin (L + 1)) → F₂) (hw : blockParity L w = 0) :
    ∃ u : Sum (Fin L) (Fin L) → F₂, twoStartCompleteBoundary L u = w := by
  have hl : startVertexSum L (fun i => w (Sum.inl i)) = 0 := by
    simpa using congrFun hw 0
  have hr : startVertexSum L (fun i => w (Sum.inr i)) = 0 := by
    simpa using congrFun hw 1
  obtain ⟨u, hu, _⟩ := existsUnique_startCompleteBoundary_eq hl
  obtain ⟨v, hv, _⟩ := existsUnique_startCompleteBoundary_eq hr
  refine ⟨Sum.elim u v, ?_⟩
  funext s
  cases s with
  | inl i => exact congrFun hu i
  | inr i => exact congrFun hv i

/-- Restriction of the actual boundary to the two relation spaces. -/
def boundaryRelations (M x y L : ℕ) :
    RelationSpace (twoStartSystem M x y L) →ₗ[F₂]
      LinearMap.ker (parityOnRelations (twoValueSystem M x y L) (blockParity L)) where
  toFun u := ⟨⟨twoStartCompleteBoundary L u,
    (mem_start_relation_iff_boundary_value_relation M x y L u).mp u.property⟩,
      blockParity_boundary_eq_zero L u⟩
  map_add' u v := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_add (twoStartCompleteBoundary L) u.val v.val
  map_smul' c u := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_smul (twoStartCompleteBoundary L) c u.val

theorem boundaryRelations_injective (M x y L : ℕ) :
    Function.Injective (boundaryRelations M x y L) := by
  intro u v huv
  apply Subtype.ext
  apply twoStartCompleteBoundary_injective L
  exact congrArg (fun w => w.val.val) huv

theorem boundaryRelations_surjective (M x y L : ℕ) :
    Function.Surjective (boundaryRelations M x y L) := by
  intro w
  have hw : blockParity L w.val.val = 0 := w.property
  obtain ⟨u, hu⟩ := exists_boundary_of_blockParity_eq_zero L w.val.val hw
  have hrel : u ∈ RelationSpace (twoStartSystem M x y L) := by
    apply (mem_start_relation_iff_boundary_value_relation M x y L u).mpr
    rw [hu]
    exact w.val.property
  refine ⟨⟨u, hrel⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hu

/-- The start relations are exactly the even-in-each-block full-value relations. -/
def startRelationEquivParityKernel (M x y L : ℕ) :
    RelationSpace (twoStartSystem M x y L) ≃ₗ[F₂]
      LinearMap.ker (parityOnRelations (twoValueSystem M x y L) (blockParity L)) :=
  LinearEquiv.ofBijective (boundaryRelations M x y L)
    ⟨boundaryRelations_injective M x y L, boundaryRelations_surjective M x y L⟩

/-- The constrained full-value nullity is the nullity of the actual start system. -/
theorem parityNullity_eq_start_relationRho (M x y L : ℕ) :
    parityNullity (twoValueSystem M x y L) (blockParity L) =
      relationRho (twoStartSystem M x y L) :=
  (startRelationEquivParityKernel M x y L).finrank_eq.symm

/-- The actual full-value nullity differs from start nullity by at most two. -/
theorem value_relationRho_le_start_add_two (M x y L : ℕ) :
    relationRho (twoValueSystem M x y L) ≤ relationRho (twoStartSystem M x y L) + 2 := by
  simpa [parityNullity_eq_start_relationRho] using
    relationRho_le_parityNullity_add_two (twoValueSystem M x y L) (blockParity L)

/-- Finite comparison at each actual ordered pair of windows. -/
theorem value_weight_le_four_start_weight_add_host (M x y L : ℕ) :
    2 ^ relationRho (twoValueSystem M x y L) - 1 ≤
      4 * (2 ^ relationRho (twoStartSystem M x y L) - 1) +
        3 * (if relationRho (twoValueSystem M x y L) ≠ 0 then 1 else 0) := by
  simpa [parityNullity_eq_start_relationRho] using
    relation_weight_le_four_parity_weight_add_host (twoValueSystem M x y L) (blockParity L)

/-- Full-value hosts include square relations without any block-parity restriction. -/
def valueRelationalHosts (M L : ℕ) (s : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) := by
  classical
  exact s.filter fun xy => relationRho (twoValueSystem M xy.1 xy.2 L) ≠ 0

/-- Actual finite window comparison with the unrestricted full-value host count. -/
theorem sum_value_weight_le_four_start_weight_add_hosts (M L : ℕ) (s : Finset (ℕ × ℕ)) :
    ∑ xy ∈ s, (2 ^ relationRho (twoValueSystem M xy.1 xy.2 L) - 1) ≤
      4 * (∑ xy ∈ s, (2 ^ relationRho (twoStartSystem M xy.1 xy.2 L) - 1)) +
        3 * (valueRelationalHosts M L s).card := by
  simpa [parityNullity_eq_start_relationRho, valueRelationalHosts] using
    sum_relation_weight_le_four_parity_weight_add_hosts s
      (fun xy => twoValueSystem M xy.1 xy.2 L) (fun _ => blockParity L)

/-- The historical complete labels are the consecutive vertices at positive starts. -/
theorem start_label_eq_consecutive {x L : ℕ} (hx : 1 ≤ x) (i : Fin (L + 1)) :
    startCompleteVertexLabel x L i = WindowValues.vertex x (L + 1) i := by
  unfold startCompleteVertexLabel WindowValues.vertex
  split_ifs <;> omega

/-- Identification with the displayed consecutive-value windows, without reindexing rows. -/
theorem twoValueSystem_eq_consecutive {M x y L : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    twoValueSystem M x y L = valueSystem M
      (Sum.elim (WindowValues.vertex x (L + 1)) (WindowValues.vertex y (L + 1))) := by
  unfold twoValueSystem
  congr 1
  funext s
  cases s with
  | inl i => exact start_label_eq_consecutive hx i
  | inr i => exact start_label_eq_consecutive hy i

/-- Ordered pairs whose length-`L + 1` vertex windows are separated. -/
def separatedPairs (I : Finset ℕ) (L : ℕ) : Finset (ℕ × ℕ) :=
  (I ×ˢ I).filter fun xy => L < Nat.dist xy.1 xy.2

@[simp]
theorem mem_separatedPairs (I : Finset ℕ) (L x y : ℕ) :
    (x, y) ∈ separatedPairs I L ↔ x ∈ I ∧ y ∈ I ∧ L < Nat.dist x y := by
  simp [separatedPairs, and_assoc]

/-- Finite-cylinder comparison underlying (3.24), on ordered separated pairs.
The host term uses full-value nullity. Identifying it with the article requires
positive starts and a cylinder containing the vertices; its arithmetic bound is separate. -/
theorem finite_equation_three_twenty_four (M L : ℕ) (I : Finset ℕ) :
    ∑ xy ∈ separatedPairs I L, (2 ^ relationRho (twoValueSystem M xy.1 xy.2 L) - 1) ≤
      4 * (∑ xy ∈ separatedPairs I L,
        (2 ^ relationRho (twoStartSystem M xy.1 xy.2 L) - 1)) +
          3 * (valueRelationalHosts M L (separatedPairs I L)).card :=
  sum_value_weight_le_four_start_weight_add_hosts M L (separatedPairs I L)

end
end PaperC.V282.TwoWindowParity
