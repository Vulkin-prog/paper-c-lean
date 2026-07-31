import PaperC.Affine.RationalChannelCode
import PaperC.Combinatorics.LargePrimeGraphResolution

set_option maxHeartbeats 1800000

/-!
# Canonical residual certificates

This module formalizes the graph-theoretic core of Lemma 6.5.  Every
nontrivial unpinned component of the large-prime graph contains an edge.
We orient such edges from the left block to the right block, choose first
the least prime labelling an edge of the component, and then the
lexicographically least pair of complete-boundary vertices carrying that
prime.

The resulting certificates have all local and global properties needed by
the counting argument:

* the selected prime is strictly above the boundary length;
* it divides the two selected labels, equivalently the two start-plus-offset
  integers;
* different components have different left vertices, right vertices, and
  selected primes.

The input family is an arbitrary finite set of nontrivial unpinned
components.  Thus the construction applies directly to the residual family
once the quotient-core module supplies that finite set.
-/

namespace PaperC
namespace ResidualCertificates

open Affine
open Affine.RationalChannelCode
open Affine.RelationalPrimeAssignment
open LargePrimeOccurrences
open LargePrimeGraph
open LargePrimeGraphResolution
open PinnedGraphResolution

noncomputable section

noncomputable local instance instDecidableLargePrimeAdj
    (x y L : ℕ) :
    DecidableRel (largePrimeGraph x y L).Adj :=
  Classical.decRel _

/--
Row-major order on left--right cells.  Since `finProdFinEquiv (i,j)` has
value `j + (L+1)i`, this is precisely lexicographic order, first by the left
offset and then by the right offset.
-/
noncomputable local instance instLinearOrderCertificateCell
    (L : ℕ) :
    LinearOrder (Fin (L + 1) × Fin (L + 1)) :=
  LinearOrder.lift'
    (finProdFinEquiv :
      Fin (L + 1) × Fin (L + 1) ≃
        Fin ((L + 1) * (L + 1)))
    finProdFinEquiv.injective

/-! ## Edges carried by one component -/

/--
An oriented left--right cell is labelled by `p` inside the connected
component `C`.
-/
def IsComponentPrimeCell
    (x y L : ℕ)
    (C : (largePrimeGraph x y L).ConnectedComponent)
    (p : ℕ)
    (cell : Fin (L + 1) × Fin (L + 1)) : Prop :=
  IsLargePrime L p ∧
    Sum.inl cell.1 ∈ primeOccurrences x y L p ∧
    Sum.inr cell.2 ∈ primeOccurrences x y L p ∧
    (largePrimeGraph x y L).connectedComponentMk
        (Sum.inl cell.1) = C

/-- A component carries `p` when one of its oriented edges is labelled by `p`. -/
def ComponentCarriesPrime
    (x y L : ℕ)
    (C : (largePrimeGraph x y L).ConnectedComponent)
    (p : ℕ) : Prop :=
  ∃ cell : Fin (L + 1) × Fin (L + 1),
    IsComponentPrimeCell x y L C p cell

/-- A component-prime cell indeed gives an edge of the large-prime graph. -/
theorem adj_of_isComponentPrimeCell
    {x y L p : ℕ}
    {C : (largePrimeGraph x y L).ConnectedComponent}
    {cell : Fin (L + 1) × Fin (L + 1)}
    (hcell : IsComponentPrimeCell x y L C p cell) :
    (largePrimeGraph x y L).Adj
      (Sum.inl cell.1) (Sum.inr cell.2) := by
  exact
    ⟨by simp, p, hcell.1, hcell.2.1, hcell.2.2.1⟩

/-- The right endpoint of a component-prime cell belongs to the same component. -/
theorem right_component_of_isComponentPrimeCell
    {x y L p : ℕ}
    {C : (largePrimeGraph x y L).ConnectedComponent}
    {cell : Fin (L + 1) × Fin (L + 1)}
    (hcell : IsComponentPrimeCell x y L C p cell) :
    (largePrimeGraph x y L).connectedComponentMk
        (Sum.inr cell.2) = C := by
  have hadj := adj_of_isComponentPrimeCell hcell
  exact
    (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      hadj).symm.trans hcell.2.2.2

/--
A finite connected component with at least two vertices contains an edge
whose two endpoints belong to that component.
-/
theorem exists_adj_in_component_of_two_le_card
    (x y L : ℕ)
    (C : (largePrimeGraph x y L).ConnectedComponent)
    (hcard : 2 ≤ Fintype.card C.supp) :
    ∃ v w : Occurrence L,
      v ∈ C.supp ∧ w ∈ C.supp ∧
        (largePrimeGraph x y L).Adj v w := by
  classical
  by_contra hno
  have hnone :
      ∀ v w : Occurrence L,
        v ∈ C.supp → w ∈ C.supp →
          ¬(largePrimeGraph x y L).Adj v w := by
    intro v w hv hw hadj
    exact hno ⟨v, w, hv, hw, hadj⟩
  have hisolated :
      ∀ w : Occurrence L,
        ¬(largePrimeGraph x y L).Adj C.out w := by
    intro w hadj
    have hout : C.out ∈ C.supp := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      exact C.out_eq
    have hw : w ∈ C.supp := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      exact
        (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          hadj).symm.trans C.out_eq
    exact hnone C.out w hout hw hadj
  have hone : Fintype.card C.supp = 1 := by
    rw [Fintype.card_eq_one_iff]
    let root : C.supp :=
      ⟨C.out, by
        rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
        exact C.out_eq⟩
    refine ⟨root, ?_⟩
    intro z
    apply Subtype.ext
    have hreach :
        (largePrimeGraph x y L).Reachable C.out z.1 := by
      apply SimpleGraph.ConnectedComponent.exact
      exact C.out_eq.trans z.2.symm
    exact
      LargePrimeGraphResolution.eq_of_reachable_of_no_adj
        hisolated hreach
  omega

/--
Every nontrivial component of the concrete graph carries at least one large
prime and at least one oriented left--right cell for that prime.
-/
theorem exists_componentCarriesPrime
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (C : (largePrimeGraph x y L).ConnectedComponent)
    (hC :
      IsNontrivialUnpinnedComponent
        (largePrimeGraph x y L)
        (pinnedVertices x y L) C) :
    ∃ p : ℕ, ComponentCarriesPrime x y L C p := by
  obtain ⟨v, w, hvC, hwC, hvw⟩ :=
    exists_adj_in_component_of_two_le_card
      x y L C hC.2
  obtain ⟨hne, p, hp, hv, hw⟩ := hvw
  have hopposite :=
    inOppositeBlocks_of_mem_of_ne
      hx hy hp.1 hp.2 hv hw hne
  rcases hopposite with
      ⟨i, j, rfl, rfl⟩ |
      ⟨j, i, rfl, rfl⟩
  · exact
      ⟨p, ⟨(i, j), hp, hv, hw,
        (SimpleGraph.ConnectedComponent.mem_supp_iff C _).mp hvC⟩⟩
  · exact
      ⟨p, ⟨(i, j), hp, hw, hv,
        (SimpleGraph.ConnectedComponent.mem_supp_iff C _).mp hwC⟩⟩

/-! ## The two-stage canonical choice -/

/-- The least prime labelling an edge in `C`. -/
noncomputable def leastComponentPrime
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (C : (largePrimeGraph x y L).ConnectedComponent)
    (hC :
      IsNontrivialUnpinnedComponent
        (largePrimeGraph x y L)
        (pinnedVertices x y L) C) : ℕ := by
  classical
  exact Nat.find (exists_componentCarriesPrime hx hy C hC)

/-- The least selected prime really labels an edge of the component. -/
theorem leastComponentPrime_spec
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (C : (largePrimeGraph x y L).ConnectedComponent)
    (hC :
      IsNontrivialUnpinnedComponent
        (largePrimeGraph x y L)
        (pinnedVertices x y L) C) :
    ComponentCarriesPrime x y L C
      (leastComponentPrime hx hy C hC) := by
  classical
  exact Nat.find_spec (exists_componentCarriesPrime hx hy C hC)

/-- Minimality of the selected prime among all edge labels of `C`. -/
theorem leastComponentPrime_le
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (C : (largePrimeGraph x y L).ConnectedComponent)
    (hC :
      IsNontrivialUnpinnedComponent
        (largePrimeGraph x y L)
        (pinnedVertices x y L) C)
    {q : ℕ}
    (hq : ComponentCarriesPrime x y L C q) :
    leastComponentPrime hx hy C hC ≤ q := by
  classical
  exact Nat.find_min'
    (exists_componentCarriesPrime hx hy C hC) hq

/-- All oriented cells of `C` carrying a fixed prime `p`. -/
noncomputable def componentPrimeCells
    (x y L : ℕ)
    (C : (largePrimeGraph x y L).ConnectedComponent)
    (p : ℕ) :
    Finset (Fin (L + 1) × Fin (L + 1)) := by
  classical
  exact Finset.univ.filter
    (IsComponentPrimeCell x y L C p)

@[simp]
theorem mem_componentPrimeCells
    {x y L p : ℕ}
    {C : (largePrimeGraph x y L).ConnectedComponent}
    {cell : Fin (L + 1) × Fin (L + 1)} :
    cell ∈ componentPrimeCells x y L C p ↔
      IsComponentPrimeCell x y L C p cell := by
  classical
  simp [componentPrimeCells]

/-- The cell set at the selected least prime is nonempty. -/
theorem componentPrimeCells_least_nonempty
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (C : (largePrimeGraph x y L).ConnectedComponent)
    (hC :
      IsNontrivialUnpinnedComponent
        (largePrimeGraph x y L)
        (pinnedVertices x y L) C) :
    (componentPrimeCells x y L C
      (leastComponentPrime hx hy C hC)).Nonempty := by
  obtain ⟨cell, hcell⟩ :=
    leastComponentPrime_spec hx hy C hC
  exact ⟨cell, mem_componentPrimeCells.mpr hcell⟩

/--
After choosing the least prime, choose the lexicographically least
left--right cell carrying it.
-/
noncomputable def leastComponentCell
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (C : (largePrimeGraph x y L).ConnectedComponent)
    (hC :
      IsNontrivialUnpinnedComponent
        (largePrimeGraph x y L)
        (pinnedVertices x y L) C) :
    Fin (L + 1) × Fin (L + 1) :=
  (componentPrimeCells x y L C
      (leastComponentPrime hx hy C hC)).min'
    (componentPrimeCells_least_nonempty hx hy C hC)

/-- The lexicographically least cell has the required label and component. -/
theorem leastComponentCell_spec
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (C : (largePrimeGraph x y L).ConnectedComponent)
    (hC :
      IsNontrivialUnpinnedComponent
        (largePrimeGraph x y L)
        (pinnedVertices x y L) C) :
    IsComponentPrimeCell x y L C
      (leastComponentPrime hx hy C hC)
      (leastComponentCell hx hy C hC) := by
  exact mem_componentPrimeCells.mp
    (Finset.min'_mem _ _)

/-- Lexicographic minimality at the already selected least prime. -/
theorem leastComponentCell_le
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (C : (largePrimeGraph x y L).ConnectedComponent)
    (hC :
      IsNontrivialUnpinnedComponent
        (largePrimeGraph x y L)
        (pinnedVertices x y L) C)
    {cell : Fin (L + 1) × Fin (L + 1)}
    (hcell :
      IsComponentPrimeCell x y L C
        (leastComponentPrime hx hy C hC) cell) :
    finProdFinEquiv (leastComponentCell hx hy C hC) ≤
      finProdFinEquiv cell := by
  change
    @LE.le (Fin (L + 1) × Fin (L + 1))
      (instLinearOrderCertificateCell L).toLE
      (leastComponentCell hx hy C hC) cell
  exact Finset.min'_le _ _ (mem_componentPrimeCells.mpr hcell)

/-! ## Packaged certificates -/

/-- The data and proofs carried by one residual certificate. -/
structure ComponentCertificate
    (x y L : ℕ)
    (C : (largePrimeGraph x y L).ConnectedComponent) where
  prime : ℕ
  left : Fin (L + 1)
  right : Fin (L + 1)
  prime_large : IsLargePrime L prime
  left_mem :
    Sum.inl left ∈ primeOccurrences x y L prime
  right_mem :
    Sum.inr right ∈ primeOccurrences x y L prime
  left_component :
    (largePrimeGraph x y L).connectedComponentMk
        (Sum.inl left) = C

/-- The canonical certificate attached to one nontrivial unpinned component. -/
noncomputable def canonicalComponentCertificate
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (C : (largePrimeGraph x y L).ConnectedComponent)
    (hC :
      IsNontrivialUnpinnedComponent
        (largePrimeGraph x y L)
        (pinnedVertices x y L) C) :
    ComponentCertificate x y L C := by
  let p := leastComponentPrime hx hy C hC
  let cell := leastComponentCell hx hy C hC
  have hcell :
      IsComponentPrimeCell x y L C p cell := by
    exact leastComponentCell_spec hx hy C hC
  exact
    ⟨p, cell.1, cell.2,
      hcell.1, hcell.2.1, hcell.2.2.1, hcell.2.2.2⟩

@[simp]
theorem canonicalComponentCertificate_prime
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (C : (largePrimeGraph x y L).ConnectedComponent)
    (hC :
      IsNontrivialUnpinnedComponent
        (largePrimeGraph x y L)
        (pinnedVertices x y L) C) :
    (canonicalComponentCertificate hx hy C hC).prime =
      leastComponentPrime hx hy C hC :=
  rfl

@[simp]
theorem canonicalComponentCertificate_cell
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (C : (largePrimeGraph x y L).ConnectedComponent)
    (hC :
      IsNontrivialUnpinnedComponent
        (largePrimeGraph x y L)
        (pinnedVertices x y L) C) :
    ((canonicalComponentCertificate hx hy C hC).left,
        (canonicalComponentCertificate hx hy C hC).right) =
      leastComponentCell hx hy C hC :=
  rfl

/-- Every packaged certificate gives an edge. -/
theorem ComponentCertificate.adj
    {x y L : ℕ}
    {C : (largePrimeGraph x y L).ConnectedComponent}
    (cert : ComponentCertificate x y L C) :
    (largePrimeGraph x y L).Adj
      (Sum.inl cert.left) (Sum.inr cert.right) := by
  exact
    ⟨by simp, cert.prime, cert.prime_large,
      cert.left_mem, cert.right_mem⟩

/-- The right endpoint of a certificate lies in its indexed component. -/
theorem ComponentCertificate.right_component
    {x y L : ℕ}
    {C : (largePrimeGraph x y L).ConnectedComponent}
    (cert : ComponentCertificate x y L C) :
    (largePrimeGraph x y L).connectedComponentMk
        (Sum.inr cert.right) = C := by
  exact
    (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      cert.adj).symm.trans cert.left_component

/-- The selected prime divides the natural left label. -/
theorem ComponentCertificate.prime_dvd_left_label
    {x y L : ℕ}
    {C : (largePrimeGraph x y L).ConnectedComponent}
    (cert : ComponentCertificate x y L C) :
    cert.prime ∣
      startCompleteVertexLabel x L cert.left :=
  dvd_of_parityVec_ne_zero
    (parityVec_ne_zero_of_mem cert.left_mem)

/-- The selected prime divides the natural right label. -/
theorem ComponentCertificate.prime_dvd_right_label
    {x y L : ℕ}
    {C : (largePrimeGraph x y L).ConnectedComponent}
    (cert : ComponentCertificate x y L C) :
    cert.prime ∣
      startCompleteVertexLabel y L cert.right :=
  dvd_of_parityVec_ne_zero
    (parityVec_ne_zero_of_mem cert.right_mem)

/--
In the manuscript's signed offset coordinates, `p ∣ x+i` for the left
certificate offset.
-/
theorem ComponentCertificate.prime_dvd_left_start_add_offset
    {x y L : ℕ}
    {C : (largePrimeGraph x y L).ConnectedComponent}
    (cert : ComponentCertificate x y L C)
    (hx : 1 ≤ x) :
    (cert.prime : ℤ) ∣
      (x : ℤ) + channelVertexOffset cert.left := by
  rw [← startCompleteVertexLabel_cast hx]
  exact_mod_cast cert.prime_dvd_left_label

/--
In the manuscript's signed offset coordinates, `p ∣ y+j` for the right
certificate offset.
-/
theorem ComponentCertificate.prime_dvd_right_start_add_offset
    {x y L : ℕ}
    {C : (largePrimeGraph x y L).ConnectedComponent}
    (cert : ComponentCertificate x y L C)
    (hy : 1 ≤ y) :
    (cert.prime : ℤ) ∣
      (y : ℤ) + channelVertexOffset cert.right := by
  rw [← startCompleteVertexLabel_cast hy]
  exact_mod_cast cert.prime_dvd_right_label

/-- The signed vertex-offset map is injective. -/
theorem channelVertexOffset_injective
    {L : ℕ} :
    Function.Injective
      (channelVertexOffset : Fin (L + 1) → ℤ) := by
  intro v w hvw
  apply Fin.ext
  simp only [channelVertexOffset] at hvw
  omega

/-! ## Extraction from an arbitrary residual family -/

/--
Canonical certificates indexed by a finite family of nontrivial unpinned
components.
-/
noncomputable def canonicalCertificates
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (components :
      Finset (largePrimeGraph x y L).ConnectedComponent)
    (hcomponents :
      ∀ C ∈ components,
        IsNontrivialUnpinnedComponent
          (largePrimeGraph x y L)
          (pinnedVertices x y L) C)
    (C : {C // C ∈ components}) :
    ComponentCertificate x y L C.1 :=
  canonicalComponentCertificate
    hx hy C.1 (hcomponents C.1 C.2)

/--
Certificates indexed by different components cannot reuse a left
complete-boundary occurrence.
-/
theorem canonicalCertificates_left_injective
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (components :
      Finset (largePrimeGraph x y L).ConnectedComponent)
    (hcomponents :
      ∀ C ∈ components,
        IsNontrivialUnpinnedComponent
          (largePrimeGraph x y L)
          (pinnedVertices x y L) C) :
    Function.Injective
      (fun C : {C // C ∈ components} ↦
        (canonicalCertificates
          hx hy components hcomponents C).left) := by
  intro C D hleft
  apply Subtype.ext
  let certC :=
    canonicalCertificates hx hy components hcomponents C
  let certD :=
    canonicalCertificates hx hy components hcomponents D
  calc
    C.1 =
        (largePrimeGraph x y L).connectedComponentMk
          (Sum.inl certC.left) :=
      certC.left_component.symm
    _ =
        (largePrimeGraph x y L).connectedComponentMk
          (Sum.inl certD.left) := by
      rw [show certC.left = certD.left by exact hleft]
    _ = D.1 :=
      certD.left_component

/--
Certificates indexed by different components cannot reuse a right
complete-boundary occurrence.
-/
theorem canonicalCertificates_right_injective
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (components :
      Finset (largePrimeGraph x y L).ConnectedComponent)
    (hcomponents :
      ∀ C ∈ components,
        IsNontrivialUnpinnedComponent
          (largePrimeGraph x y L)
          (pinnedVertices x y L) C) :
    Function.Injective
      (fun C : {C // C ∈ components} ↦
        (canonicalCertificates
          hx hy components hcomponents C).right) := by
  intro C D hright
  apply Subtype.ext
  let certC :=
    canonicalCertificates hx hy components hcomponents C
  let certD :=
    canonicalCertificates hx hy components hcomponents D
  calc
    C.1 =
        (largePrimeGraph x y L).connectedComponentMk
          (Sum.inr certC.right) :=
      certC.right_component.symm
    _ =
        (largePrimeGraph x y L).connectedComponentMk
          (Sum.inr certD.right) := by
      rw [show certC.right = certD.right by exact hright]
    _ = D.1 :=
      certD.right_component

/--
A fixed large prime labels at most one component.  Hence the selected
primes of different components are distinct.
-/
theorem canonicalCertificates_prime_injective
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (components :
      Finset (largePrimeGraph x y L).ConnectedComponent)
    (hcomponents :
      ∀ C ∈ components,
        IsNontrivialUnpinnedComponent
          (largePrimeGraph x y L)
          (pinnedVertices x y L) C) :
    Function.Injective
      (fun C : {C // C ∈ components} ↦
        (canonicalCertificates
          hx hy components hcomponents C).prime) := by
  intro C D hprime
  apply canonicalCertificates_left_injective
    hx hy components hcomponents
  let certC :=
    canonicalCertificates hx hy components hcomponents C
  let certD :=
    canonicalCertificates hx hy components hcomponents D
  change certC.prime = certD.prime at hprime
  change certC.left = certD.left
  have hCmem := certC.left_mem
  change
    Sum.inl certC.left ∈
      primeOccurrences x y L certC.prime at hCmem
  rw [hprime] at hCmem
  apply inl_eq_of_mem hx certD.prime_large.1 certD.prime_large.2
  · exact hCmem
  · exact certD.left_mem

/-- The actual signed left offsets are pairwise distinct. -/
theorem canonicalCertificates_leftOffset_injective
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (components :
      Finset (largePrimeGraph x y L).ConnectedComponent)
    (hcomponents :
      ∀ C ∈ components,
        IsNontrivialUnpinnedComponent
          (largePrimeGraph x y L)
          (pinnedVertices x y L) C) :
    Function.Injective
      (fun C : {C // C ∈ components} ↦
        channelVertexOffset
          (canonicalCertificates
            hx hy components hcomponents C).left) := by
  intro C D hoffset
  apply canonicalCertificates_left_injective
    hx hy components hcomponents
  exact channelVertexOffset_injective hoffset

/-- The actual signed right offsets are pairwise distinct. -/
theorem canonicalCertificates_rightOffset_injective
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (components :
      Finset (largePrimeGraph x y L).ConnectedComponent)
    (hcomponents :
      ∀ C ∈ components,
        IsNontrivialUnpinnedComponent
          (largePrimeGraph x y L)
          (pinnedVertices x y L) C) :
    Function.Injective
      (fun C : {C // C ∈ components} ↦
        channelVertexOffset
          (canonicalCertificates
            hx hy components hcomponents C).right) := by
  intro C D hoffset
  apply canonicalCertificates_right_injective
    hx hy components hcomponents
  exact channelVertexOffset_injective hoffset

/-! ## Excluding exact cells and the one-unit exception -/

/-- The pair of signed offsets carried by a packaged certificate. -/
def ComponentCertificate.offsetCell
    {x y L : ℕ}
    {C : (largePrimeGraph x y L).ConnectedComponent}
    (cert : ComponentCertificate x y L C) :
    ℤ × ℤ :=
  (channelVertexOffset cert.left,
    channelVertexOffset cert.right)

/--
The manuscript's residual nonvanishing expression is equivalent to saying
that the selected cell does not lie on the rational channel.
-/
theorem not_onChannel_iff_residualExpression_ne
    (a b : ℕ) (h i j : ℤ) :
    ¬OnChannel a b h (i, j) ↔
      h + (b : ℤ) * j - (a : ℤ) * i ≠ 0 := by
  unfold OnChannel
  constructor
  · intro hnot hzero
    apply hnot
    linarith
  · intro hnon hchannel
    apply hnon
    linarith

/--
Abstract bridge to the residual quotient: if every exact channel cell has
its connected component excluded from `components`, then no extracted
certificate is exact.

The quotient-core formalization only has to establish the exclusion
hypothesis for its concrete definition of `C_res`.
-/
theorem canonicalCertificates_not_onChannel_of_excluded
    {x y L a b : ℕ} {h : ℤ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (components :
      Finset (largePrimeGraph x y L).ConnectedComponent)
    (hcomponents :
      ∀ C ∈ components,
        IsNontrivialUnpinnedComponent
          (largePrimeGraph x y L)
          (pinnedVertices x y L) C)
    (hexcluded :
      ∀ cell : Fin (L + 1) × Fin (L + 1),
        OnChannel a b h
          (channelVertexOffset cell.1,
            channelVertexOffset cell.2) →
        (largePrimeGraph x y L).connectedComponentMk
            (Sum.inl cell.1) ∉ components)
    (C : {C // C ∈ components}) :
    ¬OnChannel a b h
      (canonicalCertificates
        hx hy components hcomponents C).offsetCell := by
  intro hexact
  let cert :=
    canonicalCertificates hx hy components hcomponents C
  have hnot :=
    hexcluded (cert.left, cert.right) (by
      exact hexact)
  apply hnot
  rw [cert.left_component]
  exact C.2

/--
Direct form of part (iv) of Lemma 6.5 under the residual-component
exclusion hypothesis.
-/
theorem canonicalCertificates_residualExpression_ne
    {x y L a b : ℕ} {h : ℤ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (components :
      Finset (largePrimeGraph x y L).ConnectedComponent)
    (hcomponents :
      ∀ C ∈ components,
        IsNontrivialUnpinnedComponent
          (largePrimeGraph x y L)
          (pinnedVertices x y L) C)
    (hexcluded :
      ∀ cell : Fin (L + 1) × Fin (L + 1),
        OnChannel a b h
          (channelVertexOffset cell.1,
            channelVertexOffset cell.2) →
        (largePrimeGraph x y L).connectedComponentMk
            (Sum.inl cell.1) ∉ components)
    (C : {C // C ∈ components}) :
    h +
        (b : ℤ) *
          channelVertexOffset
            (canonicalCertificates
              hx hy components hcomponents C).right -
        (a : ℤ) *
          channelVertexOffset
            (canonicalCertificates
              hx hy components hcomponents C).left ≠
      0 := by
  rw [← not_onChannel_iff_residualExpression_ne]
  exact
    canonicalCertificates_not_onChannel_of_excluded
      hx hy components hcomponents hexcluded C

/--
Components in a residual family meeting one of two distinguished
occurrences.  This is the abstract exceptional family in the `m=1` branch.
-/
noncomputable def componentsMeetingPair
    {x y L : ℕ}
    (components :
      Finset (largePrimeGraph x y L).ConnectedComponent)
    (v w : Occurrence L) :
    Finset (largePrimeGraph x y L).ConnectedComponent := by
  classical
  exact components.filter fun C ↦
    (largePrimeGraph x y L).connectedComponentMk v = C ∨
      (largePrimeGraph x y L).connectedComponentMk w = C

@[simp]
theorem mem_componentsMeetingPair
    {x y L : ℕ}
    {components :
      Finset (largePrimeGraph x y L).ConnectedComponent}
    {v w : Occurrence L}
    {C : (largePrimeGraph x y L).ConnectedComponent} :
    C ∈ componentsMeetingPair components v w ↔
      C ∈ components ∧
        ((largePrimeGraph x y L).connectedComponentMk v = C ∨
          (largePrimeGraph x y L).connectedComponentMk w = C) := by
  classical
  simp [componentsMeetingPair]

/--
At most two connected components can meet a distinguished pair of
occurrences.  This is the exact combinatorial bound used for the possible
exceptions when a channel has one unit.
-/
theorem card_componentsMeetingPair_le_two
    {x y L : ℕ}
    (components :
      Finset (largePrimeGraph x y L).ConnectedComponent)
    (v w : Occurrence L) :
    (componentsMeetingPair components v w).card ≤ 2 := by
  classical
  have hsubset :
      componentsMeetingPair components v w ⊆
        {(largePrimeGraph x y L).connectedComponentMk v,
          (largePrimeGraph x y L).connectedComponentMk w} := by
    intro C hC
    rw [mem_componentsMeetingPair] at hC
    rcases hC.2 with hCv | hCw
    · simp [hCv]
    · simp [hCw]
  calc
    (componentsMeetingPair components v w).card ≤
        ({(largePrimeGraph x y L).connectedComponentMk v,
          (largePrimeGraph x y L).connectedComponentMk w} :
            Finset
              (largePrimeGraph x y L).ConnectedComponent).card :=
      Finset.card_le_card hsubset
    _ ≤ 2 := Finset.card_le_two

/--
The selected primes form a finite set with exactly as many elements as the
residual component family.
-/
noncomputable def canonicalCertificatePrimes
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (components :
      Finset (largePrimeGraph x y L).ConnectedComponent)
    (hcomponents :
      ∀ C ∈ components,
        IsNontrivialUnpinnedComponent
          (largePrimeGraph x y L)
          (pinnedVertices x y L) C) :
    Finset ℕ :=
  components.attach.image fun C ↦
    (canonicalCertificates
      hx hy components hcomponents C).prime

theorem card_canonicalCertificatePrimes
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (components :
      Finset (largePrimeGraph x y L).ConnectedComponent)
    (hcomponents :
      ∀ C ∈ components,
        IsNontrivialUnpinnedComponent
          (largePrimeGraph x y L)
          (pinnedVertices x y L) C) :
    (canonicalCertificatePrimes
        hx hy components hcomponents).card =
      components.card := by
  classical
  calc
    (canonicalCertificatePrimes
        hx hy components hcomponents).card =
        components.attach.card := by
      exact Finset.card_image_of_injective
        components.attach
        (canonicalCertificates_prime_injective
          hx hy components hcomponents)
    _ = components.card :=
      Finset.card_attach

end

end ResidualCertificates
end PaperC
