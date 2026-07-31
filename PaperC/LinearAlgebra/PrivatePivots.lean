import PaperC.Arithmetic.ParityVector
import PaperC.Combinatorics.TreeBoundary
import Mathlib.Data.Nat.Dist
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# Linear independence from private pivots

This file isolates the finite linear-algebra mechanism behind Paper C, Lemma 13.1.
The first theorem is the usual column-wise private-pivot criterion over an arbitrary
division ring.  The second theorem is the form used in the paper: private coordinates
belong to the non-root *vertices* of a tree, while columns are indexed by its edges.
The tree-boundary bijection turns vanishing vertex degrees modulo two into vanishing
edge coefficients.
-/

namespace PaperC
namespace PrivatePivots

open Finset SimpleGraph

section ColumnPivots

variable {R ι M : Type*}
variable [DivisionRing R] [AddCommGroup M] [Module R M]

/--
A family is linearly independent if every member has a linear functional which
is nonzero on that member and zero on all the other members.

This is the reusable, coordinate-free private-pivot criterion.
-/
theorem linearIndependent_of_private_pivots
    (v : ι → M) (pivot : ι → (M →ₗ[R] R))
    (hdiag : ∀ i, pivot i (v i) ≠ 0)
    (hoffdiag : ∀ i j, j ≠ i → pivot i (v j) = 0) :
    LinearIndependent R v := by
  rw [linearIndependent_iff']
  intro s g hsum i hi
  have hcoord :
      ∑ j ∈ s, g j * pivot i (v j) = 0 := by
    have h := congrArg (pivot i) hsum
    simpa only [map_sum, map_smul, map_zero, smul_eq_mul] using h
  have hsingle : g i * pivot i (v i) = 0 := by
    have hsum_single :
        ∑ j ∈ s, g j * pivot i (v j) =
          g i * pivot i (v i) := by
      apply Finset.sum_eq_single i
      · intro j _hj hji
        rw [hoffdiag i j hji, mul_zero]
      · intro hni
        exact (hni hi).elim
    rw [← hsum_single]
    exact hcoord
  exact (mul_eq_zero.mp hsingle).resolve_right (hdiag i)

/--
Finsupp specialization of `linearIndependent_of_private_pivots`: each vector
has a coordinate where it is nonzero and every other vector is zero.
-/
theorem finsupp_linearIndependent_of_private_pivots
    {κ : Type*} (v : ι → κ →₀ R) (pivot : ι → κ)
    (hdiag : ∀ i, v i (pivot i) ≠ 0)
    (hoffdiag : ∀ i j, j ≠ i → v j (pivot i) = 0) :
    LinearIndependent R v :=
  linearIndependent_of_private_pivots v
    (fun i => Finsupp.lapply (pivot i)) hdiag hoffdiag

end ColumnPivots

section TreePivots

/-- The sum of the two endpoint vectors of an unordered pair. -/
def edgeSum {V M : Type*} [AddCommMonoid M] (x : V → M) : Sym2 V → M :=
  Sym2.lift ⟨fun a b => x a + x b, fun a b => add_comm (x a) (x b)⟩

@[simp]
theorem edgeSum_pair {V M : Type*} [AddCommMonoid M]
    (x : V → M) (a b : V) :
    edgeSum x s(a, b) = x a + x b :=
  rfl

variable {V κ : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/--
At a coordinate private to `n`, an edge sum over `𝔽₂` is one precisely when
the edge is incident with `n`.
-/
theorem edgeSum_apply_private
    (x : V → κ →₀ F₂) (n : V) (p : κ)
    (hdiag : x n p = 1)
    (hprivate : ∀ m, m ≠ n → x m p = 0)
    (e : Sym2 V) (hne : ¬e.IsDiag) :
    edgeSum x e p = if n ∈ e then 1 else 0 := by
  induction e using Sym2.inductionOn with
  | _ a b =>
      have hab : a ≠ b := by
        simpa only [Sym2.mk_isDiag_iff] using hne
      by_cases han : a = n
      · subst a
        have hbn : b ≠ n := by simpa only [ne_eq, eq_comm] using hab
        simp [edgeSum, hdiag, hprivate b hbn, Sym2.mem_iff]
      · by_cases hbn : b = n
        · subst b
          simp [edgeSum, hdiag, hprivate a han, Sym2.mem_iff, han]
        · have hna : n ≠ a := Ne.symm han
          have hnb : n ≠ b := Ne.symm hbn
          simp [edgeSum, hprivate a han, hprivate b hbn, Sym2.mem_iff, hna, hnb]

private theorem zmod_two_eq_one_of_ne_zero {a : F₂} (ha : a ≠ 0) : a = 1 := by
  apply ZMod.val_injective
  rw [ZMod.val_one_eq_one_mod]
  have hval : a.val ≠ 0 := by
    intro h
    apply ha
    apply ZMod.val_injective
    simpa using h
  have hlt : a.val < 2 := ZMod.val_lt a
  norm_num
  omega

/--
Tree form of the private-pivot lemma.

Each non-root vertex `n` has a coordinate `pivot n` at which its vector is
one and every other vertex vector is zero.  Then the vectors obtained by
adding the endpoint vectors along the edges of a finite tree are linearly
independent over `𝔽₂`.
-/
theorem tree_edgeSum_linearIndependent_of_private_nonroot
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsTree) (r : V)
    (x : V → κ →₀ F₂)
    (pivot : {n : V // n ≠ r} → κ)
    (hdiag : ∀ n, x n.1 (pivot n) = 1)
    (hprivate : ∀ n m, m ≠ n.1 → x m (pivot n) = 0) :
    LinearIndependent F₂
      (fun e : G.edgeSet => edgeSum x e.1) := by
  rw [linearIndependent_iff]
  intro l hlin
  have hnonroot :
      ∀ n : {n : V // n ≠ r},
        n.1 ∉ TreeBoundary.boundary
          (TreeBoundary.edgeValueFinset l.support) := by
    intro n
    rw [TreeBoundary.mem_boundary]
    rw [← Nat.not_even_iff_odd]
    push Not
    have hcoord :
        l.sum (fun e c => c * edgeSum x e.1 (pivot n)) = 0 := by
      have h :=
        congrArg (fun z : κ →₀ F₂ => z (pivot n)) hlin
      simpa only [Finsupp.linearCombination_apply, map_zero,
        Finsupp.zero_apply, Finsupp.sum, Finset.sum_apply',
        Finsupp.smul_apply, smul_eq_mul] using h
    have hedge (e : G.edgeSet) :
        edgeSum x e.1 (pivot n) =
          if n.1 ∈ e.1 then 1 else 0 := by
      exact edgeSum_apply_private x n.1 (pivot n)
        (hdiag n) (hprivate n) e.1
        (G.not_isDiag_of_mem_edgeSet e.2)
    have hcast :
        (((l.support.filter fun e : G.edgeSet => n.1 ∈ e.1).card : ℕ) : F₂) = 0 := by
      rw [Finsupp.sum] at hcoord
      calc
        (((l.support.filter fun e : G.edgeSet => n.1 ∈ e.1).card : ℕ) : F₂) =
            ∑ _e ∈ l.support.filter (fun e : G.edgeSet => n.1 ∈ e.1),
              (1 : F₂) := by simp
        _ = ∑ e ∈ l.support,
              if n.1 ∈ e.1 then (1 : F₂) else 0 := by
              rw [Finset.sum_filter]
        _ = ∑ e ∈ l.support, l e * edgeSum x e.1 (pivot n) := by
              apply Finset.sum_congr rfl
              intro e he
              rw [zmod_two_eq_one_of_ne_zero
                (Finsupp.mem_support_iff.mp he), hedge e]
              by_cases hne : n.1 ∈ e.1 <;> simp [hne]
        _ = 0 := hcoord
    have hcard :
        ((TreeBoundary.edgeValueFinset l.support).filter
            fun e : Sym2 V => n.1 ∈ e).card =
          (l.support.filter fun e : G.edgeSet => n.1 ∈ e.1).card := by
      have hfilter :
          (l.support.map (Function.Embedding.subtype G.edgeSet)).filter
              (fun e : Sym2 V => n.1 ∈ e) =
            (l.support.filter fun e : G.edgeSet => n.1 ∈ e.1).map
              (Function.Embedding.subtype G.edgeSet) := by
        exact Finset.filter_map
      rw [TreeBoundary.edgeValueFinset, hfilter, Finset.card_map]
      rfl
    rw [hcard]
    exact ZMod.natCast_eq_zero_iff_even.mp hcast
  have hboundary :
      TreeBoundary.boundary
          (TreeBoundary.edgeValueFinset l.support) = ∅ := by
    let B :=
      TreeBoundary.boundary (TreeBoundary.edgeValueFinset l.support)
    have hBsub : B ⊆ {r} := by
      intro n hn
      rw [Finset.mem_singleton]
      by_contra hnr
      exact hnonroot ⟨n, hnr⟩ hn
    have hBle : B.card ≤ 1 := by
      simpa using Finset.card_le_card hBsub
    have hBeven : Even B.card :=
      TreeBoundary.even_card_boundary
        (TreeBoundary.edgeValueFinset l.support)
        (TreeBoundary.edgeValueFinset_subset_edgeFinset l.support)
    have hBzero : B.card = 0 := by
      obtain ⟨k, hk⟩ := hBeven
      omega
    exact Finset.card_eq_zero.mp hBzero
  have hsupport :
      l.support = (∅ : TreeBoundary.EdgeSubset G) := by
    apply (TreeBoundary.boundaryMap_bijective_of_isTree hG).1
    apply Subtype.ext
    change
      TreeBoundary.boundary (TreeBoundary.edgeValueFinset l.support) =
        TreeBoundary.boundary
          (TreeBoundary.edgeValueFinset
            (∅ : TreeBoundary.EdgeSubset G))
    have hempty :
        TreeBoundary.edgeValueFinset
            (G := G) (∅ : TreeBoundary.EdgeSubset G) = ∅ := by
      ext e
      simp [TreeBoundary.mem_edgeValueFinset]
    rw [hboundary, hempty, TreeBoundary.boundary_empty]
  exact Finsupp.support_eq_empty.mp hsupport

/--
Two distinct multiples of `p` are at distance at least `p`.  Consequently,
a number at distance less than `Y < p` from a multiple of `p` is not itself
a multiple of `p`.
-/
theorem not_dvd_of_dvd_and_dist_lt
    {a b p Y : ℕ} (hpa : p ∣ a) (hab : a ≠ b)
    (hpY : Y < p) (hdist : Nat.dist a b < Y) :
    ¬p ∣ b := by
  intro hpb
  obtain ⟨ka, hka⟩ := hpa
  obtain ⟨kb, hkb⟩ := hpb
  have hpdist : p ∣ Nat.dist a b := by
    refine ⟨Nat.dist ka kb, ?_⟩
    calc
      Nat.dist a b = Nat.dist (p * ka) (p * kb) := by rw [hka, hkb]
      _ = p * Nat.dist ka kb := Nat.dist_mul_left p ka kb
  have hpos : 0 < Nat.dist a b := Nat.dist_pos_of_ne hab
  have hple : p ≤ Nat.dist a b := Nat.le_of_dvd hpos hpdist
  omega

/--
Arithmetic specialization matching Paper C, Lemma 13.1.

Vertices carry pairwise distinct natural-number labels whose pairwise distance
is less than `Y`.  Every non-root vertex has a prime `p > Y` occurring to odd
valuation in its label.  The prime is then absent from every other vertex
label, so the parity-vector edge family has full rank over `𝔽₂`.
-/
theorem tree_parityEdge_linearIndependent_of_large_odd_primes
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsTree) (r : V)
    (label : V → ℕ) (hlabel : Function.Injective label)
    (Y : ℕ) (privatePrime : {n : V // n ≠ r} → ℕ)
    (_hprime : ∀ n, (privatePrime n).Prime)
    (hlarge : ∀ n, Y < privatePrime n)
    (hodd : ∀ n, Odd ((label n.1).factorization (privatePrime n)))
    (hdiam : ∀ a b, a ≠ b → Nat.dist (label a) (label b) < Y) :
    LinearIndependent F₂
      (fun e : G.edgeSet =>
        edgeSum (fun n => parityVec (label n)) e.1) := by
  apply tree_edgeSum_linearIndependent_of_private_nonroot
    G hG r (fun n => parityVec (label n)) privatePrime
  · intro n
    rw [parityVec_apply, ZMod.natCast_eq_one_iff_odd]
    exact hodd n
  · intro n m hmn
    rw [parityVec_apply]
    have hfacne :
        (label n.1).factorization (privatePrime n) ≠ 0 := by
      intro hz
      have := hodd n
      simp [hz] at this
    have hpLabel : privatePrime n ∣ label n.1 := by
      by_contra hnot
      exact hfacne (Nat.factorization_eq_zero_of_not_dvd hnot)
    have hlabelne : label n.1 ≠ label m := by
      intro heq
      exact hmn (hlabel heq).symm
    have hnotdiv : ¬privatePrime n ∣ label m :=
      not_dvd_of_dvd_and_dist_lt hpLabel hlabelne
        (hlarge n) (hdiam n.1 m (Ne.symm hmn))
    change ((label m).factorization (privatePrime n) : F₂) = 0
    rw [Nat.factorization_eq_zero_of_not_dvd hnotdiv]
    rfl

/--
Parity vector restricted to the coordinates strictly larger than `Y`.
Non-prime coordinates remain present in the indexing type but are automatically
zero, so this is the same projection as the paper's projection to primes `p > Y`.
-/
noncomputable def parityVecAbove (Y n : ℕ) :
    {p : ℕ // Y < p} →₀ F₂ :=
  (parityVec n).comapDomain Subtype.val
    Subtype.val_injective.injOn

@[simp]
theorem parityVecAbove_apply (Y n : ℕ) (p : {p : ℕ // Y < p}) :
    parityVecAbove Y n p = parityVec n p.1 := by
  simp [parityVecAbove]

/--
Exact projected form of Paper C, Lemma 13.1: the edge vectors restricted to
coordinates `p > Y` are linearly independent.
-/
theorem tree_projectedParityEdge_linearIndependent_of_large_odd_primes
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsTree) (r : V)
    (label : V → ℕ) (hlabel : Function.Injective label)
    (Y : ℕ) (privatePrime : {n : V // n ≠ r} → ℕ)
    (_hprime : ∀ n, (privatePrime n).Prime)
    (hlarge : ∀ n, Y < privatePrime n)
    (hodd : ∀ n, Odd ((label n.1).factorization (privatePrime n)))
    (hdiam : ∀ a b, a ≠ b → Nat.dist (label a) (label b) < Y) :
    LinearIndependent F₂
      (fun e : G.edgeSet =>
        edgeSum (fun n => parityVecAbove Y (label n)) e.1) := by
  let projectedPrime : {n : V // n ≠ r} → {p : ℕ // Y < p} :=
    fun n => ⟨privatePrime n, hlarge n⟩
  apply tree_edgeSum_linearIndependent_of_private_nonroot
    G hG r (fun n => parityVecAbove Y (label n)) projectedPrime
  · intro n
    rw [parityVecAbove_apply, parityVec_apply, ZMod.natCast_eq_one_iff_odd]
    exact hodd n
  · intro n m hmn
    rw [parityVecAbove_apply, parityVec_apply]
    have hfacne :
        (label n.1).factorization (privatePrime n) ≠ 0 := by
      intro hz
      have := hodd n
      simp [hz] at this
    have hpLabel : privatePrime n ∣ label n.1 := by
      by_contra hnot
      exact hfacne (Nat.factorization_eq_zero_of_not_dvd hnot)
    have hlabelne : label n.1 ≠ label m := by
      intro heq
      exact hmn (hlabel heq).symm
    have hnotdiv : ¬privatePrime n ∣ label m :=
      not_dvd_of_dvd_and_dist_lt hpLabel hlabelne
        (hlarge n) (hdiam n.1 m (Ne.symm hmn))
    change ((label m).factorization (privatePrime n) : F₂) = 0
    rw [Nat.factorization_eq_zero_of_not_dvd hnotdiv]
    rfl

end TreePivots

end PrivatePivots
end PaperC
