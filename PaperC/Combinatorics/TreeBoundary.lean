import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Powerset

/-!
# Boundaries of edge sets in a finite tree

This file formalizes the elementary tree-boundary lemma used in Paper C.  The boundary of a
finite set of (undirected) edges consists of the vertices incident with an odd number of selected
edges.
-/

open scoped symmDiff

namespace PaperC
namespace TreeBoundary

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Vertices incident with an odd number of edges of `F`. -/
def boundary (F : Finset (Sym2 V)) : Finset V :=
  Finset.univ.filter fun v ↦ Odd ((F.filter fun e ↦ v ∈ e).card)

@[simp]
theorem mem_boundary {F : Finset (Sym2 V)} {v : V} :
    v ∈ boundary F ↔ Odd ((F.filter fun e ↦ v ∈ e).card) := by
  simp [boundary]

@[simp]
theorem boundary_empty : boundary (∅ : Finset (Sym2 V)) = ∅ := by
  ext
  simp

/-- A finite set of genuine edges is exactly the edge finset of the graph it generates. -/
theorem edgeFinset_fromEdgeSet_eq {G : SimpleGraph V} [DecidableRel G.Adj]
    (F : Finset (Sym2 V))
    (hF : F ⊆ G.edgeFinset) :
    (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).edgeFinset = F := by
  classical
  ext e
  constructor
  · intro he
    have he' : e ∈ (F : Set (Sym2 V)) ∧ ¬e.IsDiag := by
      simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_fromEdgeSet] using he
    exact he'.1
  · intro he
    have heG : e ∈ G.edgeSet := by
      simpa [SimpleGraph.mem_edgeFinset] using hF he
    have hnd : ¬e.IsDiag := G.not_isDiag_of_mem_edgeSet heG
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_fromEdgeSet]
    exact ⟨he, hnd⟩

/--
The handshaking half of Paper C, Lemma 2.2: the boundary of every finite edge subset has even
cardinality.  This statement is valid in every finite simple graph; no connectedness or acyclicity
is needed.
-/
theorem even_card_boundary {G : SimpleGraph V} [DecidableRel G.Adj] (F : Finset (Sym2 V))
    (hF : F ⊆ G.edgeFinset) : Even (boundary F).card := by
  classical
  let H : SimpleGraph V := SimpleGraph.fromEdgeSet (F : Set (Sym2 V))
  have hEdges : H.edgeFinset = F := edgeFinset_fromEdgeSet_eq F hF
  have hBoundary :
      boundary F = Finset.univ.filter fun v ↦ Odd (H.degree v) := by
    ext v
    simp only [mem_boundary, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← H.card_incidenceFinset_eq_degree, H.incidenceFinset_eq_filter, hEdges]
  rw [hBoundary]
  exact H.even_card_odd_degree_vertices

omit [Fintype V] in
/-- Filtering commutes with symmetric difference. -/
theorem filter_symmDiff (F K : Finset (Sym2 V)) (p : Sym2 V → Prop) [DecidablePred p] :
    (F ∆ K).filter p = F.filter p ∆ K.filter p := by
  ext e
  simp only [mem_filter, mem_symmDiff]
  tauto

/--
The parity of the cardinality of a symmetric difference is the exclusive-or of the two input
parities.
-/
theorem odd_card_symmDiff_iff {α : Type*} [DecidableEq α] (s t : Finset α) :
    Odd (s ∆ t).card ↔
      (Odd s.card ∧ ¬Odd t.card) ∨ (Odd t.card ∧ ¬Odd s.card) := by
  have hdisj : Disjoint (s ∆ t) (s ∩ t) := by
    rw [Finset.disjoint_left]
    intro x hx hst
    simp only [mem_symmDiff, mem_inter] at hx hst
    tauto
  have hunion : (s ∆ t) ∪ (s ∩ t) = s ∪ t := by
    ext x
    simp only [mem_union, mem_symmDiff, mem_inter]
    tauto
  have hcard :
      (s ∆ t).card + 2 * (s ∩ t).card = s.card + t.card := by
    have h₁ := Finset.card_union_of_disjoint hdisj
    rw [hunion] at h₁
    have h₂ := Finset.card_union_add_card_inter s t
    omega
  have hparity :
      Odd (s ∆ t).card ↔ Odd (s.card + t.card) := by
    constructor
    · intro h
      rw [← hcard]
      exact h.add_even (even_two_mul (s ∩ t).card)
    · intro h
      rw [← hcard] at h
      exact (Nat.odd_add.mp h).mpr (even_two_mul (s ∩ t).card)
  rw [hparity, Nat.odd_add, ← Nat.not_odd_iff_even]
  tauto

/-- Symmetric difference preserves even cardinality. -/
theorem even_card_symmDiff {α : Type*} [DecidableEq α] {s t : Finset α}
    (hs : Even s.card) (ht : Even t.card) : Even (s ∆ t).card := by
  rw [← Nat.not_odd_iff_even]
  rw [odd_card_symmDiff_iff]
  have hns : ¬Odd s.card := Nat.not_odd_iff_even.mpr hs
  have hnt : ¬Odd t.card := Nat.not_odd_iff_even.mpr ht
  tauto

/-- The boundary operation is additive for symmetric difference. -/
theorem boundary_symmDiff (F K : Finset (Sym2 V)) :
    boundary (F ∆ K) = boundary F ∆ boundary K := by
  ext v
  simp only [mem_boundary, mem_symmDiff]
  rw [filter_symmDiff]
  exact odd_card_symmDiff_iff _ _

omit [DecidableEq V] in
/-- The edge finset of a trail is contained in the ambient graph. -/
theorem trailEdges_subset_edgeFinset {G : SimpleGraph V} [DecidableRel G.Adj]
    {u v : V} {p : G.Walk u v} (hp : p.IsTrail) :
    hp.edgesFinset ⊆ G.edgeFinset := by
  intro e he
  rw [SimpleGraph.mem_edgeFinset]
  exact p.edges_subset_edgeSet (by simpa using he)

/--
The boundary of a trail with distinct endpoints consists exactly of its two endpoints.
In particular, this applies to the unique path between two vertices of a tree.
-/
theorem boundary_trailEdges {G : SimpleGraph V} {u v : V} {p : G.Walk u v}
    (hp : p.IsTrail) (huv : u ≠ v) :
    boundary hp.edgesFinset = {u, v} := by
  ext x
  rw [mem_boundary]
  have hcount :
      (hp.edgesFinset.filter fun e ↦ x ∈ e).card =
        p.edges.countP fun e ↦ x ∈ e := by
    rw [← Multiset.coe_countP, Multiset.countP_eq_card_filter]
    rfl
  rw [hcount]
  rw [← Nat.not_even_iff_odd, hp.even_countP_edges_iff x]
  simp only [huv, ne_eq, true_implies, Finset.mem_insert, Finset.mem_singleton]
  tauto

/--
Existence half of the tree-boundary lemma, in the stronger form valid for every finite connected
simple graph: every even vertex set is the boundary of an edge set.
-/
theorem exists_edgeSubset_boundary_eq_of_connected {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : G.Connected) (S : Finset V) (hS : Even S.card) :
    ∃ F : Finset (Sym2 V), F ⊆ G.edgeFinset ∧ boundary F = S := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∀ S : Finset V, S.card = n → Even S.card →
      ∃ F : Finset (Sym2 V), F ⊆ G.edgeFinset ∧ boundary F = S
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro S hcard hEven
        by_cases hSempty : S = ∅
        · subst S
          exact ⟨∅, by simp, boundary_empty⟩
        · have hScardPos : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hSempty)
          have hScardTwo : 2 ≤ S.card := by
            obtain ⟨k, hk⟩ := hEven
            omega
          obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hSempty
          have hEraseU : (S.erase u).Nonempty := by
            rw [← Finset.card_pos, Finset.card_erase_of_mem hu]
            omega
          obtain ⟨v, hvErase⟩ := hEraseU
          have hv : v ∈ S := Finset.mem_of_mem_erase hvErase
          have hvu : v ≠ u := Finset.ne_of_mem_erase hvErase
          have huv : u ≠ v := hvu.symm
          let Q : Finset V := {u, v}
          have hQsub : Q ⊆ S := by
            intro x hx
            simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact hu
            · exact hv
          let S' : Finset V := S ∆ Q
          have hS'sub : S' ⊆ S := by
            intro x hx
            simp only [S', Finset.mem_symmDiff] at hx
            rcases hx with hx | hx
            · exact hx.1
            · exact hQsub hx.1
          have huQ : u ∈ Q := by simp [Q]
          have huNotS' : u ∉ S' := by
            simp only [S', Finset.mem_symmDiff]
            tauto
          have hS'lt : S'.card < n := by
            rw [← hcard]
            apply Finset.card_lt_card
            rw [Finset.ssubset_iff_subset_ne]
            refine ⟨hS'sub, ?_⟩
            intro heq
            have : u ∈ S' := heq.symm ▸ hu
            exact huNotS' this
          have hQeven : Even Q.card := by
            rw [show Q.card = 2 by simp [Q, huv]]
            exact even_two
          have hS'even : Even S'.card :=
            even_card_symmDiff hEven hQeven
          obtain ⟨F', hF'sub, hF'boundary⟩ :=
            ih S'.card hS'lt S' rfl hS'even
          let p : G.Path u v := (hG u v).some.toPath
          let E : Finset (Sym2 V) := p.isTrail.edgesFinset
          have hEsub : E ⊆ G.edgeFinset :=
            trailEdges_subset_edgeFinset p.isTrail
          have hEboundary : boundary E = Q := by
            simpa [E, Q] using boundary_trailEdges p.isTrail huv
          refine ⟨F' ∆ E, ?_, ?_⟩
          · intro e he
            simp only [Finset.mem_symmDiff] at he
            rcases he with he | he
            · exact hF'sub he.1
            · exact hEsub he.1
          · rw [boundary_symmDiff, hF'boundary, hEboundary]
            change (S ∆ Q) ∆ Q = S
            exact symmDiff_symmDiff_cancel_right Q S
  exact hP S.card S rfl hS

/-- Finite edge subsets, represented intrinsically as finsets of graph edges. -/
abbrev EdgeSubset (G : SimpleGraph V) := Finset G.edgeSet

/-- Even-cardinality subsets of the vertex type. -/
def EvenVertexSubset (V : Type*) [Fintype V] [DecidableEq V] :=
  {S : Finset V // Even S.card}

/-- Forget the edge-membership proofs in an intrinsic edge subset. -/
def edgeValueFinset {G : SimpleGraph V} (F : EdgeSubset G) : Finset (Sym2 V) :=
  F.map (Function.Embedding.subtype G.edgeSet)

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem mem_edgeValueFinset {G : SimpleGraph V} {F : EdgeSubset G} {e : Sym2 V} :
    e ∈ edgeValueFinset F ↔ ∃ he : e ∈ G.edgeSet, (⟨e, he⟩ : G.edgeSet) ∈ F := by
  constructor
  · intro he
    rw [edgeValueFinset, Finset.mem_map] at he
    obtain ⟨x, hxF, hxe⟩ := he
    have hval : x.1 = e := hxe
    subst e
    exact ⟨x.2, hxF⟩
  · rintro ⟨heG, heF⟩
    rw [edgeValueFinset, Finset.mem_map]
    exact ⟨⟨e, heG⟩, heF, rfl⟩

omit [DecidableEq V] in
theorem edgeValueFinset_subset_edgeFinset {G : SimpleGraph V} [DecidableRel G.Adj]
    (F : EdgeSubset G) : edgeValueFinset F ⊆ G.edgeFinset := by
  intro e he
  rw [mem_edgeValueFinset] at he
  obtain ⟨heG, _⟩ := he
  simpa [SimpleGraph.mem_edgeFinset] using heG

/-- Turn an extrinsic edge finset together with its membership certificate into intrinsic edges. -/
def toEdgeSubset {G : SimpleGraph V} [DecidableRel G.Adj]
    (F : Finset (Sym2 V)) (_hF : F ⊆ G.edgeFinset) : EdgeSubset G :=
  Finset.univ.filter fun e : G.edgeSet ↦ e.1 ∈ F

@[simp]
theorem edgeValueFinset_toEdgeSubset {G : SimpleGraph V} [DecidableRel G.Adj]
    (F : Finset (Sym2 V)) (hF : F ⊆ G.edgeFinset) :
    edgeValueFinset (toEdgeSubset F hF) = F := by
  ext e
  rw [mem_edgeValueFinset]
  constructor
  · rintro ⟨heG, he⟩
    simpa [toEdgeSubset] using he
  · intro heF
    have heG : e ∈ G.edgeSet :=
      SimpleGraph.mem_edgeFinset.mp (hF heF)
    exact ⟨heG, by simp [toEdgeSubset, heF]⟩

/-- The boundary map from intrinsic edge subsets to even vertex subsets. -/
def boundaryMap (G : SimpleGraph V) [DecidableRel G.Adj] :
    EdgeSubset G → EvenVertexSubset V :=
  fun F ↦ ⟨boundary (edgeValueFinset F), even_card_boundary _ (edgeValueFinset_subset_edgeFinset F)⟩

/-- On a connected graph, the boundary map is surjective onto even vertex subsets. -/
theorem boundaryMap_surjective_of_connected {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : G.Connected) : Function.Surjective (boundaryMap G) := by
  intro S
  obtain ⟨F, hFsub, hFb⟩ :=
    exists_edgeSubset_boundary_eq_of_connected hG S.1 S.2
  refine ⟨toEdgeSubset F hFsub, ?_⟩
  apply Subtype.ext
  change boundary (edgeValueFinset (toEdgeSubset F hFsub)) = S.1
  rw [edgeValueFinset_toEdgeSubset]
  exact hFb

/-- Remove the distinguished root and regard the result as a finset of non-root vertices. -/
def deleteRoot (r : V) (S : Finset V) : Finset {v : V // v ≠ r} :=
  Finset.univ.filter fun v ↦ v.1 ∈ S

/-- Forget the non-root certificates. -/
def nonRootValueFinset (r : V) (S : Finset {v : V // v ≠ r}) : Finset V :=
  S.map (Function.Embedding.subtype fun v : V ↦ v ≠ r)

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem mem_nonRootValueFinset (r : V) {S : Finset {v : V // v ≠ r}} {v : V} :
    v ∈ nonRootValueFinset r S ↔ ∃ hv : v ≠ r, (⟨v, hv⟩ : {w : V // w ≠ r}) ∈ S := by
  simp [nonRootValueFinset]

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem root_not_mem_nonRootValueFinset (r : V) (S : Finset {v : V // v ≠ r}) :
    r ∉ nonRootValueFinset r S := by
  simp

theorem nonRootValueFinset_deleteRoot (r : V) (S : Finset V) :
    nonRootValueFinset r (deleteRoot r S) = S.erase r := by
  ext v
  simp [nonRootValueFinset, deleteRoot, and_comm]

/-- Complete a non-root subset by toggling the root exactly when its cardinality is odd. -/
def evenCompletion (r : V) (S : Finset {v : V // v ≠ r}) : EvenVertexSubset V :=
  let U := nonRootValueFinset r S
  if hU : Even U.card then
    ⟨U, hU⟩
  else
    ⟨insert r U, by
      rw [Finset.card_insert_of_not_mem (root_not_mem_nonRootValueFinset r S)]
      exact (Nat.not_even_iff_odd.mp hU).add_one⟩

@[simp]
theorem deleteRoot_evenCompletion (r : V) (S : Finset {v : V // v ≠ r}) :
    deleteRoot r (evenCompletion r S).1 = S := by
  ext v
  simp only [deleteRoot, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [evenCompletion]
  split_ifs <;> simp [nonRootValueFinset, v.2]

@[simp]
theorem evenCompletion_deleteRoot (r : V) (S : EvenVertexSubset V) :
    evenCompletion r (deleteRoot r S.1) = S := by
  apply Subtype.ext
  by_cases hr : r ∈ S.1
  · have hOddErase : Odd (S.1.erase r).card := by
      have h := S.2
      rw [← Finset.card_erase_add_one hr] at h
      exact Nat.not_even_iff_odd.mp (Nat.even_add_one.mp h)
    simp [evenCompletion, nonRootValueFinset_deleteRoot,
      Nat.not_even_iff_odd.mpr hOddErase, Finset.insert_erase hr]
  · have hErase : S.1.erase r = S.1 := Finset.erase_eq_of_not_mem hr
    simp [evenCompletion, nonRootValueFinset_deleteRoot, hErase, S.2, hr]

/-- Even vertex subsets are canonically equivalent to arbitrary subsets after deleting one root. -/
def evenCompletionEquiv (r : V) :
    Finset {v : V // v ≠ r} ≃ EvenVertexSubset V where
  toFun := evenCompletion r
  invFun := fun S ↦ deleteRoot r S.1
  left_inv := deleteRoot_evenCompletion r
  right_inv := evenCompletion_deleteRoot r

noncomputable instance instFintypeEvenVertexSubset : Fintype (EvenVertexSubset V) :=
  Fintype.ofInjective (fun S : EvenVertexSubset V ↦ S.1) Subtype.val_injective

/-- There are `2^(|V|-1)` even vertex subsets, once a root is chosen. -/
theorem card_evenVertexSubset (r : V) :
    Fintype.card (EvenVertexSubset V) = 2 ^ (Fintype.card V - 1) := by
  have hcardNonRoot :
      Fintype.card {v : V // v ≠ r} = Fintype.card V - 1 := by
    exact Fintype.card_subtype_compl (fun v : V ↦ v = r)
  rw [← Fintype.card_congr (evenCompletionEquiv r), Fintype.card_finset, hcardNonRoot]

/-- On a finite tree the source and target of the boundary map have the same cardinality. -/
theorem card_edgeSubset_eq_evenVertexSubset {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : G.IsTree) :
    Fintype.card (EdgeSubset G) = Fintype.card (EvenVertexSubset V) := by
  let r : V := Classical.choice hG.isConnected.nonempty
  rw [Fintype.card_finset, card_evenVertexSubset r]
  rw [← G.edgeFinset_card]
  congr 1
  have hcard := hG.card_edgeFinset
  omega

/--
Full Paper C, Lemma 2.2: on a finite tree, boundary is a bijection from edge subsets to
even-cardinality vertex subsets.
-/
theorem boundaryMap_bijective_of_isTree {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : G.IsTree) : Function.Bijective (boundaryMap G) :=
  (Fintype.bijective_iff_surjective_and_card (boundaryMap G)).mpr
    ⟨boundaryMap_surjective_of_connected hG.isConnected,
      card_edgeSubset_eq_evenVertexSubset hG⟩

/-- The boundary bijection packaged as a Lean equivalence. -/
noncomputable def treeBoundaryEquiv {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : G.IsTree) : EdgeSubset G ≃ EvenVertexSubset V :=
  Equiv.ofBijective (boundaryMap G) (boundaryMap_bijective_of_isTree hG)

/--
Usable existence-and-uniqueness form: every even vertex set of a finite tree is the boundary of
exactly one intrinsic edge subset.
-/
theorem existsUnique_edgeSubset_boundary_eq {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : G.IsTree) (S : Finset V) (hS : Even S.card) :
    ∃! F : EdgeSubset G, boundary (edgeValueFinset F) = S := by
  let T : EvenVertexSubset V := ⟨S, hS⟩
  obtain ⟨F, hF⟩ := (boundaryMap_bijective_of_isTree hG).2 T
  have hFval : boundary (edgeValueFinset F) = S :=
    congrArg Subtype.val hF
  refine ⟨F, hFval, ?_⟩
  intro K hK
  apply (boundaryMap_bijective_of_isTree hG).1
  exact (Subtype.ext hK).trans hF.symm

end TreeBoundary
end PaperC
