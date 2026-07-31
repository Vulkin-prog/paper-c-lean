import PaperC.Arithmetic.ComponentSquareClass
import PaperC.Arithmetic.SeparatedSmallChannels
import PaperC.Combinatorics.LargePrimeGraph

set_option maxHeartbeats 1600000

/-!
# Components of the large-prime graph

This file connects the concrete graph of Section 6 with the arithmetic
square-class statement.  A connected component which contains no pinned
vertex receives every large prime either zero times or twice.  Consequently
the product of its positive vertex labels is a square times a unique
squarefree integer supported on primes at most the cutoff.

For separated starts the complete vertex labels are injective, so the
component can be passed without loss from occurrence coordinates to the
finite set of integer labels used by `ComponentSquareClass`.
-/

namespace PaperC
namespace LargePrimeComponents

open LargePrimeOccurrences
open LargePrimeGraph
open ComponentSquareClass

noncomputable section

/-- The vertices belonging to a connected component of the concrete graph. -/
noncomputable def componentVertices
    (x y L : ℕ)
    (C : (largePrimeGraph x y L).ConnectedComponent) :
    Finset (Occurrence L) := by
  classical
  exact Finset.univ.filter fun v ↦
    (largePrimeGraph x y L).connectedComponentMk v = C

@[simp]
theorem mem_componentVertices
    {x y L : ℕ}
    {C : (largePrimeGraph x y L).ConnectedComponent}
    {v : Occurrence L} :
    v ∈ componentVertices x y L C ↔
      (largePrimeGraph x y L).connectedComponentMk v = C := by
  simp [componentVertices]

/-- A component is pinned if it contains at least one pinned vertex. -/
def IsPinnedComponent
    (x y L : ℕ)
    (C : (largePrimeGraph x y L).ConnectedComponent) : Prop :=
  ∃ v ∈ componentVertices x y L C,
    IsPinned x y L v

/-- The finite set of integer labels carried by a component. -/
def componentLabels
    (x y L : ℕ)
    (C : (largePrimeGraph x y L).ConnectedComponent) :
    Finset ℕ :=
  (componentVertices x y L C).image
    (Affine.twoStartCompleteVertexLabel x y L)

/-- Every connected component has at least one vertex. -/
theorem componentVertices_nonempty
    (x y L : ℕ)
    (C : (largePrimeGraph x y L).ConnectedComponent) :
    (componentVertices x y L C).Nonempty := by
  obtain ⟨v, hv⟩ := C.exists_rep
  refine ⟨v, ?_⟩
  rw [mem_componentVertices]
  change Quot.mk (largePrimeGraph x y L).Reachable v = C
  exact hv

/-- A complete label lies weakly above the left endpoint minus one. -/
theorem startCompleteVertexLabel_lower
    {x L : ℕ} (hx : 1 ≤ x)
    (v : Fin (L + 1)) :
    x - 1 ≤ Affine.startCompleteVertexLabel x L v := by
  unfold Affine.startCompleteVertexLabel
  split_ifs <;> omega

/-- A complete label lies strictly below the endpoint `x+L`. -/
theorem startCompleteVertexLabel_upper
    {x L : ℕ} (hx : 1 ≤ x)
    (v : Fin (L + 1)) :
    Affine.startCompleteVertexLabel x L v < x + L := by
  unfold Affine.startCompleteVertexLabel
  split_ifs <;> omega

/-- Literal separation by distance gives one of the two ordered gaps. -/
theorem ordered_gap_of_lt_dist
    {x y L : ℕ} (hsep : L < Nat.dist x y) :
    x + L < y ∨ y + L < x := by
  rcases le_total x y with hxy | hyx
  · left
    rw [Nat.dist_eq_sub_of_le hxy] at hsep
    omega
  · right
    rw [Nat.dist_eq_sub_of_le_right hyx] at hsep
    omega

/--
For separated positive starts, all complete labels in the two blocks are
pairwise distinct.
-/
theorem twoStartCompleteVertexLabel_injective_of_separated
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hsep : L < Nat.dist x y) :
    Function.Injective
      (Affine.twoStartCompleteVertexLabel x y L) := by
  intro v w hvw
  rcases ordered_gap_of_lt_dist hsep with hxy | hyx
  · cases v with
    | inl v =>
        cases w with
        | inl w =>
            exact congrArg Sum.inl
              (Affine.RelationalPrimeAssignment.startCompleteVertexLabel_injective
                hx hvw)
        | inr w =>
            have hvUpper :=
              startCompleteVertexLabel_upper hx v
            have hwLower :=
              startCompleteVertexLabel_lower hy w
            simp only [Affine.twoStartCompleteVertexLabel] at hvw
            omega
    | inr v =>
        cases w with
        | inl w =>
            have hvLower :=
              startCompleteVertexLabel_lower hy v
            have hwUpper :=
              startCompleteVertexLabel_upper hx w
            simp only [Affine.twoStartCompleteVertexLabel] at hvw
            omega
        | inr w =>
            exact congrArg Sum.inr
              (Affine.RelationalPrimeAssignment.startCompleteVertexLabel_injective
                hy hvw)
  · cases v with
    | inl v =>
        cases w with
        | inl w =>
            exact congrArg Sum.inl
              (Affine.RelationalPrimeAssignment.startCompleteVertexLabel_injective
                hx hvw)
        | inr w =>
            have hvLower :=
              startCompleteVertexLabel_lower hx v
            have hwUpper :=
              startCompleteVertexLabel_upper hy w
            simp only [Affine.twoStartCompleteVertexLabel] at hvw
            omega
    | inr v =>
        cases w with
        | inl w =>
            have hvUpper :=
              startCompleteVertexLabel_upper hy v
            have hwLower :=
              startCompleteVertexLabel_lower hx w
            simp only [Affine.twoStartCompleteVertexLabel] at hvw
            omega
        | inr w =>
            exact congrArg Sum.inr
              (Affine.RelationalPrimeAssignment.startCompleteVertexLabel_injective
                hy hvw)

/-- A parity coordinate is zero exactly off its occurrence set. -/
theorem parityVec_eq_zero_of_not_mem_primeOccurrences
    {x y L p : ℕ} {v : Occurrence L}
    (hv : v ∉ primeOccurrences x y L p) :
    parityVec
        (Affine.twoStartCompleteVertexLabel x y L v) p = 0 := by
  have hnotone :
      parityVec
          (Affine.twoStartCompleteVertexLabel x y L v) p ≠ 1 := by
    intro hone
    exact hv (mem_primeOccurrences.mpr hone)
  have hbinary : ∀ z : F₂, z ≠ 1 → z = 0 := by
    decide
  exact hbinary _ hnotone

/--
On an arbitrary finite vertex set, a prime-parity sum is the cardinality
modulo two of the intersection with its occurrence set.
-/
theorem sum_parityVec_eq_filtered_card
    (x y L p : ℕ) (s : Finset (Occurrence L)) :
    (∑ v ∈ s,
        parityVec
          (Affine.twoStartCompleteVertexLabel x y L v) p) =
      ((s.filter fun v ↦
        v ∈ primeOccurrences x y L p).card : F₂) := by
  classical
  calc
    (∑ v ∈ s,
        parityVec
          (Affine.twoStartCompleteVertexLabel x y L v) p) =
        ∑ v ∈ s,
          if v ∈ primeOccurrences x y L p
          then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro v hv
      by_cases hmem :
          v ∈ primeOccurrences x y L p
      · rw [if_pos hmem, mem_primeOccurrences.mp hmem]
      · rw [if_neg hmem,
          parityVec_eq_zero_of_not_mem_primeOccurrences hmem]
    _ = ((s.filter fun v ↦
          v ∈ primeOccurrences x y L p).card : F₂) := by
      simp

/--
A nonpinned component contains either zero or both occurrences of every
large prime.  Hence its total parity at that prime vanishes.
-/
theorem component_large_parity_eq_zero
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (C : (largePrimeGraph x y L).ConnectedComponent)
    (hfree : ¬ IsPinnedComponent x y L C)
    (p : ℕ) (hp : IsLargePrime L p) :
    (∑ v ∈ componentVertices x y L C,
        parityVec
          (Affine.twoStartCompleteVertexLabel x y L v) p) = 0 := by
  classical
  rw [sum_parityVec_eq_filtered_card]
  have hcard :=
    card_primeOccurrences_le_two hx hy hp.1 hp.2
  have hcases :
      (primeOccurrences x y L p).card = 0 ∨
        (primeOccurrences x y L p).card = 1 ∨
        (primeOccurrences x y L p).card = 2 := by
    omega
  rcases hcases with hc | hc | hc
  · have hempty :
        primeOccurrences x y L p = ∅ :=
      Finset.card_eq_zero.mp hc
    simp [hempty]
  · obtain ⟨v, hocc⟩ :=
      Finset.card_eq_one.mp hc
    have hvnot :
        v ∉ componentVertices x y L C := by
      intro hvC
      apply hfree
      exact ⟨v, hvC, ⟨p, hp, hocc⟩⟩
    have hfilter :
        (componentVertices x y L C).filter
            (fun z ↦ z ∈ primeOccurrences x y L p) =
          ∅ := by
      ext z
      simp only [Finset.mem_filter, Finset.notMem_empty,
        iff_false]
      rintro ⟨hzC, hzp⟩
      rw [hocc] at hzp
      have hzv : z = v := by simpa using hzp
      exact hvnot (hzv ▸ hzC)
    rw [hfilter]
    simp
  · obtain ⟨v, w, hvw, hocc⟩ :=
      Finset.card_eq_two.mp hc
    have hadj :
        (largePrimeGraph x y L).Adj v w := by
      refine ⟨hvw, p, hp, ?_, ?_⟩ <;>
        rw [hocc] <;> simp
    have hcomponent :
        (largePrimeGraph x y L).connectedComponentMk v =
          (largePrimeGraph x y L).connectedComponentMk w :=
      SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj
    by_cases hvC :
        v ∈ componentVertices x y L C
    · have hwC :
          w ∈ componentVertices x y L C := by
        rw [mem_componentVertices] at hvC ⊢
        rwa [← hcomponent]
      have hfilter :
          (componentVertices x y L C).filter
              (fun z ↦ z ∈ primeOccurrences x y L p) =
            {v, w} := by
        ext z
        simp only [Finset.mem_filter, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · rintro ⟨_hzC, hzp⟩
          rw [hocc] at hzp
          simpa only [Finset.mem_insert,
            Finset.mem_singleton] using hzp
        · intro hz
          rcases hz with rfl | rfl
          · exact ⟨hvC, by rw [hocc]; simp⟩
          · exact ⟨hwC, by rw [hocc]; simp⟩
      rw [hfilter]
      have htwo : ((2 : ℕ) : F₂) = 0 := by
        decide
      simpa [hvw] using htwo
    · have hwC :
          w ∉ componentVertices x y L C := by
        intro hwC
        apply hvC
        rw [mem_componentVertices] at hwC ⊢
        rwa [hcomponent]
      have hfilter :
          (componentVertices x y L C).filter
              (fun z ↦ z ∈ primeOccurrences x y L p) =
            ∅ := by
        ext z
        simp only [Finset.mem_filter, Finset.notMem_empty,
          iff_false]
        rintro ⟨hzC, hzp⟩
        rw [hocc] at hzp
        have hz : z = v ∨ z = w := by simpa using hzp
        rcases hz with rfl | rfl
        · exact hvC hzC
        · exact hwC hzC
      rw [hfilter]
      simp

/-- The labels of every component are positive for starts at least two. -/
theorem componentLabels_pos
    {x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (C : (largePrimeGraph x y L).ConnectedComponent) :
    ∀ n ∈ componentLabels x y L C, 0 < n := by
  intro n hn
  obtain ⟨v, _hvC, rfl⟩ :=
    Finset.mem_image.mp hn
  cases v with
  | inl v =>
      change
        0 < Affine.startCompleteVertexLabel x L v
      have hlower :=
        startCompleteVertexLabel_lower
          (show 1 ≤ x by omega) v
      omega
  | inr v =>
      change
        0 < Affine.startCompleteVertexLabel y L v
      have hlower :=
        startCompleteVertexLabel_lower
          (show 1 ≤ y by omega) v
      omega

/--
The parity sum over a separated component may be rewritten over its set of
integer labels.
-/
theorem componentLabels_large_parity_eq_zero
    {x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hsep : L < Nat.dist x y)
    (C : (largePrimeGraph x y L).ConnectedComponent)
    (hfree : ¬ IsPinnedComponent x y L C)
    (p : ℕ) (hp : p.Prime) (hpL : L + 1 < p) :
    (∑ n ∈ componentLabels x y L C,
        parityVec n p) = 0 := by
  classical
  rw [componentLabels,
    Finset.sum_image
      (fun v _hv w _hw hvw ↦
        twoStartCompleteVertexLabel_injective_of_separated
          (show 1 ≤ x by omega) (show 1 ≤ y by omega) hsep hvw)]
  exact component_large_parity_eq_zero
    (show 1 ≤ x by omega) (show 1 ≤ y by omega)
      C hfree p ⟨hp, hpL⟩

/--
Lemma 6.2, arithmetic conclusion for a concrete nonpinned component.
The squarefree factor and positive root are canonical and unique by
`ComponentSquareClass.decomposition_unique`.
-/
theorem exists_component_square_class
    {x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hsep : L < Nat.dist x y)
    (C : (largePrimeGraph x y L).ConnectedComponent)
    (hfree : ¬ IsPinnedComponent x y L C) :
    ∃ d z : ℕ,
      0 < d ∧ Squarefree d ∧
      (∀ p : ℕ, p.Prime → p ∣ d → p ≤ L + 1) ∧
      0 < z ∧
      componentProduct (componentLabels x y L C) =
        d * z ^ 2 := by
  apply exists_squarefree_mul_sq
  · exact componentLabels_pos hx hy C
  · intro p hpPrime hpLarge
    exact componentLabels_large_parity_eq_zero
      hx hy hsep C hfree p hpPrime hpLarge

end

end LargePrimeComponents
end PaperC
