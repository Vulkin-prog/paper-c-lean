import PaperC.LinearAlgebra.CanonicalExactRank
import PaperC.Combinatorics.ComponentProductParity
import PaperC.Combinatorics.LargePrimeRelationBoundary
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.ToLin

set_option maxHeartbeats 1600000

/-!
# The concrete rows and nonaligned closure of Lemma 9.10

`CanonicalExactRank` previously packaged the last step of Lemma 9.10 as an
existential presentation: a finite matrix together with an equivalence
between the residual quotient and its kernel.  This file removes the matrix
from that debt.

The columns below are the actual corrected defective vertices and residual
large-prime components.  Each column is realized as the indicator of its
connected component in the complete two-start boundary.  The rows are:

* one prime-parity equation for every prime `p ≤ L + 1`, using the canonical
  enumeration `PrimesUpTo.smallPrime`;
* the even-boundary equation in the left block;
* the even-boundary equation in the right block.

Thus `canonicalArithmeticSmallRowMatrix` is a concrete arithmetic matrix,
not supplied data.  We prove that its component columns evaluate to the
parity vector of the corresponding component product, and that its column
synthesis is an injective map into the genuine large-prime solution space.

The last section closes the quotient--kernel identification in the exact
scope of Lemma 9.10: the canonical selector is nonaligned, so the rational
code is zero, and the finite cylinder covers both complete boundaries.  In
that branch the core synthesis is an equivalence onto the full large-prime
solution, and restricting it to genuine relations gives the desired kernel
equivalence without an arithmetic bridge.
-/

namespace PaperC
namespace CanonicalSmallRows

open scoped BigOperators
open Affine
open Affine.CanonicalRationalCode
open CanonicalExactRank
open CanonicalResidualComponents
open CanonicalResidualQuotient
open ComponentProductParity
open LargePrimeComponents
open LargePrimeGraph
open LargePrimeGraphResolution
open LargePrimeOccurrences
open LargePrimeRelationBoundary
open PinnedGraphResolution
open ResidualComponentCounts
open ResidualMasses

noncomputable section

noncomputable local instance instDecidableLargePrimeAdj
    (x y L : ℕ) :
    DecidableRel (largePrimeGraph x y L).Adj :=
  Classical.decRel _

noncomputable local instance instDecidableEqLargePrimeComponent
    (x y L : ℕ) :
    DecidableEq (largePrimeGraph x y L).ConnectedComponent :=
  Classical.decEq _

/-! ## The canonical boundary columns -/

/--
The large-prime connected component represented by one corrected core
coordinate.
-/
def canonicalCoreComponent
    {A x y L : ℕ} :
    CanonicalCoreCoordinate A x y L →
      (largePrimeGraph x y L).ConnectedComponent
  | Sum.inl v =>
      (largePrimeGraph x y L).connectedComponentMk v.1
  | Sum.inr C => C.1

/--
Deleting exact defective vertices never introduces a new defective
coordinate.
-/
theorem correctedDefectiveVertices_subset_defectiveVertices
    {x y L a b : ℕ} {h : ℤ} :
    correctedDefectiveVertices x y L a b h ⊆
      defectiveVertices x y L := by
  classical
  intro v hv
  unfold correctedDefectiveVertices at hv
  split at hv
  · exact (Finset.mem_sdiff.mp hv).1
  · exact hv

/-- Every canonical corrected defective coordinate is genuinely defective. -/
theorem isDefective_of_mem_canonicalCorrectedDefectiveVertices
    {A x y L : ℕ} {v : Occurrence L}
    (hv : v ∈ canonicalCorrectedDefectiveVertices A x y L) :
    IsDefective x y L v := by
  classical
  generalize hchoice :
      canonicalReducedCandidate?
        x y (L + 1) ((L + 1) ^ A) = choice
  cases choice with
  | none =>
      apply mem_defectiveVertices.mp
      simpa [canonicalCorrectedDefectiveVertices, hchoice] using hv
  | some c =>
      apply mem_defectiveVertices.mp
      apply correctedDefectiveVertices_subset_defectiveVertices
      simpa [canonicalCorrectedDefectiveVertices, hchoice] using hv

/-- The component represented by every core coordinate contains no pin. -/
theorem canonicalCoreComponent_unpinned
    {A x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (coord : CanonicalCoreCoordinate A x y L) :
    ¬ComponentPinned
      (largePrimeGraph x y L)
      (pinnedVertices x y L)
      (canonicalCoreComponent coord) := by
  cases coord with
  | inl v =>
      exact
        (isIsolatedUnpinnedComponent_of_isDefective
          (show 1 ≤ x by omega) (show 1 ≤ y by omega)
          (isDefective_of_mem_canonicalCorrectedDefectiveVertices
            v.2)).1
  | inr C =>
      exact
        (isNontrivialUnpinnedComponent_of_mem_canonicalResidualComponents
          C.2).1

/--
A defective component really is the singleton containing its defective
vertex.
-/
theorem componentVertices_defective_eq_singleton
    {x y L : ℕ} {v : Occurrence L}
    (hv : IsDefective x y L v) :
    componentVertices x y L
        ((largePrimeGraph x y L).connectedComponentMk v) =
      {v} := by
  classical
  ext w
  simp only [mem_componentVertices, Finset.mem_singleton]
  constructor
  · intro hw
    have hreach :
        (largePrimeGraph x y L).Reachable v w :=
      SimpleGraph.ConnectedComponent.exact hw.symm
    exact
      (eq_of_reachable_of_no_adj
        (not_adj_of_isDefective hv) hreach)
  · rintro rfl
    rfl

/--
Indicator vector of the connected component represented by a core
coordinate.
-/
noncomputable def canonicalCoreBoundaryColumn
    {A x y L : ℕ}
    (coord : CanonicalCoreCoordinate A x y L) :
    Occurrence L → F₂ := by
  classical
  exact fun v ↦
    if (largePrimeGraph x y L).connectedComponentMk v =
        canonicalCoreComponent coord then
      1
    else
      0

@[simp]
theorem canonicalCoreBoundaryColumn_apply
    {A x y L : ℕ}
    (coord : CanonicalCoreCoordinate A x y L)
    (v : Occurrence L) :
    canonicalCoreBoundaryColumn coord v =
      if (largePrimeGraph x y L).connectedComponentMk v =
          canonicalCoreComponent coord then
        1
      else
        0 := by
  classical
  rfl

/-- A core column is the characteristic function of its component finset. -/
theorem canonicalCoreBoundaryColumn_eq_indicator
    {A x y L : ℕ}
    (coord : CanonicalCoreCoordinate A x y L) :
    canonicalCoreBoundaryColumn coord =
      fun v ↦
        if v ∈ componentVertices x y L
            (canonicalCoreComponent coord) then
          1
        else
          0 := by
  classical
  funext v
  simp [canonicalCoreBoundaryColumn]

/-- A corrected defective column is literally a singleton vector. -/
theorem canonicalCoreBoundaryColumn_inl
    {A x y L : ℕ}
    (v :
      {v : Occurrence L //
        v ∈ canonicalCorrectedDefectiveVertices A x y L}) :
    canonicalCoreBoundaryColumn
        (Sum.inl v :
          CanonicalCoreCoordinate A x y L) =
      Pi.single v.1 1 := by
  classical
  funext w
  rw [canonicalCoreBoundaryColumn_eq_indicator]
  simp only [canonicalCoreComponent]
  simp [componentVertices_defective_eq_singleton
      (isDefective_of_mem_canonicalCorrectedDefectiveVertices v.2),
    Pi.single_apply, eq_comm]

/--
Each concrete core column satisfies all equations belonging to primes above
`L + 1`.
-/
theorem canonicalCoreBoundaryColumn_mem_largePrimeSolution
    {A x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (coord : CanonicalCoreCoordinate A x y L) :
    canonicalCoreBoundaryColumn coord ∈
      largePrimeSolution x y L := by
  rw [largePrimeSolution_eq_pinnedGraphSpace
    (show 1 ≤ x by omega) (show 1 ≤ y by omega)]
  constructor
  · intro u v huv
    have hcomponent :
        (largePrimeGraph x y L).connectedComponentMk u =
          (largePrimeGraph x y L).connectedComponentMk v :=
      SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj huv
    unfold canonicalCoreBoundaryColumn
    rw [hcomponent]
  · intro v hvPin
    have hne :
        (largePrimeGraph x y L).connectedComponentMk v ≠
          canonicalCoreComponent coord := by
      intro heq
      exact
        (canonicalCoreComponent_unpinned hx hy coord)
          ⟨v, hvPin, heq⟩
    simp [canonicalCoreBoundaryColumn, hne]

/--
The component map on corrected core coordinates is injective.  The mixed
case uses the actual geometry: a defective coordinate gives a singleton
component, whereas every residual component has at least two vertices.
-/
theorem canonicalCoreComponent_injective
    {A x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y) :
    Function.Injective
      (canonicalCoreComponent :
        CanonicalCoreCoordinate A x y L →
          (largePrimeGraph x y L).ConnectedComponent) := by
  intro u v huv
  cases u with
  | inl u =>
      cases v with
      | inl v =>
          apply congrArg Sum.inl
          apply Subtype.ext
          have hreach :
              (largePrimeGraph x y L).Reachable u.1 v.1 :=
            SimpleGraph.ConnectedComponent.exact huv
          exact
            (eq_of_reachable_of_no_adj
              (v := u.1) (w := v.1)
              (not_adj_of_isDefective
                (isDefective_of_mem_canonicalCorrectedDefectiveVertices
                  u.2))
              hreach).symm
      | inr v =>
          have hisolated :=
            isIsolatedUnpinnedComponent_of_isDefective
              (show 1 ≤ x by omega) (show 1 ≤ y by omega)
              (isDefective_of_mem_canonicalCorrectedDefectiveVertices
                u.2)
          have hnontrivial :=
            isNontrivialUnpinnedComponent_of_mem_canonicalResidualComponents
              v.2
          have hcardOne :
              Fintype.card v.1.supp = 1 := by
            have huv' :
                (largePrimeGraph x y L).connectedComponentMk u.1 =
                  v.1 := huv
            rw [huv'] at hisolated
            exact hisolated.2
          have hcardTwo :
              2 ≤ Fintype.card v.1.supp :=
            hnontrivial.2
          omega
  | inr u =>
      cases v with
      | inl v =>
          have hisolated :=
            isIsolatedUnpinnedComponent_of_isDefective
              (show 1 ≤ x by omega) (show 1 ≤ y by omega)
              (isDefective_of_mem_canonicalCorrectedDefectiveVertices
                v.2)
          have hnontrivial :=
            isNontrivialUnpinnedComponent_of_mem_canonicalResidualComponents
              u.2
          have hcardOne :
              Fintype.card u.1.supp = 1 := by
            have huv' :
                u.1 =
                  (largePrimeGraph x y L).connectedComponentMk v.1 :=
              huv
            rw [← huv'] at hisolated
            exact hisolated.2
          have hcardTwo :
              2 ≤ Fintype.card u.1.supp :=
            hnontrivial.2
          omega
      | inr v =>
          apply congrArg Sum.inr
          apply Subtype.ext
          exact huv

/-! ## Boundary synthesis -/

/--
Synthesize a complete-boundary vector from the corrected core coordinates.
This is the literal sum of the characteristic vectors above.
-/
noncomputable def canonicalCoreBoundarySynthesis
    (A x y L : ℕ) :
    (CanonicalCoreCoordinate A x y L → F₂) →ₗ[F₂]
      (Occurrence L → F₂) :=
  Fintype.linearCombination F₂
    (canonicalCoreBoundaryColumn :
      CanonicalCoreCoordinate A x y L →
        Occurrence L → F₂)

@[simp]
theorem canonicalCoreBoundarySynthesis_apply
    {A x y L : ℕ}
    (coeff : CanonicalCoreCoordinate A x y L → F₂)
    (v : Occurrence L) :
    canonicalCoreBoundarySynthesis A x y L coeff v =
      ∑ coord : CanonicalCoreCoordinate A x y L,
        coeff coord * canonicalCoreBoundaryColumn coord v := by
  simp [canonicalCoreBoundarySynthesis,
    Fintype.linearCombination_apply, smul_eq_mul]

/-- The synthesized boundary still solves every large-prime equation. -/
theorem canonicalCoreBoundarySynthesis_mem_largePrimeSolution
    {A x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (coeff : CanonicalCoreCoordinate A x y L → F₂) :
    canonicalCoreBoundarySynthesis A x y L coeff ∈
      largePrimeSolution x y L := by
  change
    (∑ coord : CanonicalCoreCoordinate A x y L,
      coeff coord • canonicalCoreBoundaryColumn coord) ∈
        largePrimeSolution x y L
  exact Submodule.sum_mem _ fun coord _hcoord ↦
    Submodule.smul_mem _
      (coeff coord)
      (canonicalCoreBoundaryColumn_mem_largePrimeSolution hx hy coord)

/-- Restriction of the boundary synthesis to the genuine large-prime space. -/
noncomputable def canonicalCoreBoundaryToLargePrime
    {A x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y) :
    (CanonicalCoreCoordinate A x y L → F₂) →ₗ[F₂]
      largePrimeSolution x y L :=
  (canonicalCoreBoundarySynthesis A x y L).codRestrict
    (largePrimeSolution x y L)
    (canonicalCoreBoundarySynthesis_mem_largePrimeSolution hx hy)

/-- Evaluation of the synthesis at a component representative recovers its
coefficient. -/
theorem canonicalCoreBoundarySynthesis_apply_componentOut
    {A x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (coeff : CanonicalCoreCoordinate A x y L → F₂)
    (coord : CanonicalCoreCoordinate A x y L) :
    canonicalCoreBoundarySynthesis A x y L coeff
        (canonicalCoreComponent coord).out =
      coeff coord := by
  classical
  rw [canonicalCoreBoundarySynthesis_apply]
  have hout :
      (largePrimeGraph x y L).connectedComponentMk
          (canonicalCoreComponent coord).out =
        canonicalCoreComponent coord :=
    (canonicalCoreComponent coord).out_eq
  simp only [canonicalCoreBoundaryColumn_apply, hout]
  rw [Finset.sum_eq_single coord]
  · simp
  · intro other _hother hne
    have hcomponents :
        canonicalCoreComponent coord ≠
          canonicalCoreComponent other := by
      intro heq
      exact hne
        (canonicalCoreComponent_injective hx hy heq.symm)
    simp [hcomponents]
  · intro hnot
    exact (hnot (Finset.mem_univ coord)).elim

/-- The concrete core synthesis loses no coordinate. -/
theorem canonicalCoreBoundarySynthesis_injective
    {A x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y) :
    Function.Injective
      (canonicalCoreBoundarySynthesis A x y L) := by
  intro coeff₁ coeff₂ heq
  funext coord
  have hout :=
    congrFun heq (canonicalCoreComponent coord).out
  simpa only [
    canonicalCoreBoundarySynthesis_apply_componentOut hx hy]
    using hout

/-- The codomain-restricted synthesis is injective as well. -/
theorem canonicalCoreBoundaryToLargePrime_injective
    {A x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y) :
    Function.Injective
      (canonicalCoreBoundaryToLargePrime
        (A := A) (L := L) hx hy) := by
  intro coeff₁ coeff₂ heq
  apply canonicalCoreBoundarySynthesis_injective hx hy
  exact congrArg Subtype.val heq

/-! ## The actual small-prime and block rows -/

/-- Prime-parity equation evaluated on a complete-boundary vector. -/
def primeBoundaryRow
    (x y L p : ℕ) :
    (Occurrence L → F₂) →ₗ[F₂] F₂ where
  toFun boundary :=
    ∑ v : Occurrence L,
      boundary v *
        parityVec (twoStartCompleteVertexLabel x y L v) p
  map_add' boundary₁ boundary₂ := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c boundary := by
    change
      (∑ v : Occurrence L,
        (c * boundary v) *
          parityVec (twoStartCompleteVertexLabel x y L v) p) =
        c *
          ∑ v : Occurrence L,
            boundary v *
              parityVec (twoStartCompleteVertexLabel x y L v) p
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _hv
    ring

@[simp]
theorem primeBoundaryRow_apply
    (x y L p : ℕ) (boundary : Occurrence L → F₂) :
    primeBoundaryRow x y L p boundary =
      ∑ v : Occurrence L,
        boundary v *
          parityVec (twoStartCompleteVertexLabel x y L v) p :=
  rfl

/-- One of the two even-boundary equations. -/
def blockBoundaryRow
    (L : ℕ) (block : Fin 2) :
    (Occurrence L → F₂) →ₗ[F₂] F₂ where
  toFun boundary :=
    if block.1 = 0 then
      ∑ v : Fin (L + 1), boundary (Sum.inl v)
    else
      ∑ v : Fin (L + 1), boundary (Sum.inr v)
  map_add' boundary₁ boundary₂ := by
    split_ifs <;>
      simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c boundary := by
    split
    · change
        (∑ v : Fin (L + 1), c * boundary (Sum.inl v)) =
          c * ∑ v : Fin (L + 1), boundary (Sum.inl v)
      rw [Finset.mul_sum]
    · change
        (∑ v : Fin (L + 1), c * boundary (Sum.inr v)) =
          c * ∑ v : Fin (L + 1), boundary (Sum.inr v)
      rw [Finset.mul_sum]

@[simp]
theorem blockBoundaryRow_zero_apply
    (L : ℕ) (boundary : Occurrence L → F₂) :
    blockBoundaryRow L (0 : Fin 2) boundary =
      ∑ v : Fin (L + 1), boundary (Sum.inl v) := by
  simp [blockBoundaryRow]

@[simp]
theorem blockBoundaryRow_one_apply
    (L : ℕ) (boundary : Occurrence L → F₂) :
    blockBoundaryRow L (1 : Fin 2) boundary =
      ∑ v : Fin (L + 1), boundary (Sum.inr v) := by
  simp [blockBoundaryRow]

/-- The semantic row index before conversion to the `Fin` matrix API. -/
abbrev CanonicalArithmeticRow (L : ℕ) :=
  Fin (PrimesUpTo.count (L + 1)) ⊕ Fin 2

/-- The row functional selected by a semantic arithmetic row. -/
def canonicalArithmeticRow
    (x y L : ℕ) :
    CanonicalArithmeticRow L →
      (Occurrence L → F₂) →ₗ[F₂] F₂
  | Sum.inl j =>
      primeBoundaryRow x y L
        (PrimesUpTo.smallPrime (L + 1) j)
  | Sum.inr block =>
      blockBoundaryRow L block

/--
Semantic form of the concrete small-row matrix.  Each entry is the value of
one genuine boundary equation on one genuine component indicator.
-/
noncomputable def canonicalArithmeticSmallRowMatrixRaw
    (A x y L : ℕ) :
    Matrix (CanonicalArithmeticRow L)
      (CanonicalCoreCoordinate A x y L) F₂ :=
  fun row coord ↦
    canonicalArithmeticRow x y L row
      (canonicalCoreBoundaryColumn coord)

/--
The concrete matrix in the `CanonicalSmallRowMatrix` type expected by
`CanonicalExactRank`.
-/
noncomputable def canonicalArithmeticSmallRowMatrix
    (A x y L : ℕ) :
    CanonicalSmallRowMatrix
      (PrimesUpTo.count (L + 1) + 2) A x y L :=
  Matrix.reindex finSumFinEquiv (Equiv.refl _)
    (canonicalArithmeticSmallRowMatrixRaw A x y L)

@[simp]
theorem canonicalArithmeticSmallRowMatrix_prime_apply
    {A x y L : ℕ}
    (j : Fin (PrimesUpTo.count (L + 1)))
    (coord : CanonicalCoreCoordinate A x y L) :
    canonicalArithmeticSmallRowMatrix A x y L
        (finSumFinEquiv (Sum.inl j)) coord =
      primeBoundaryRow x y L
        (PrimesUpTo.smallPrime (L + 1) j)
        (canonicalCoreBoundaryColumn coord) := by
  simp [canonicalArithmeticSmallRowMatrix,
    canonicalArithmeticSmallRowMatrixRaw,
    canonicalArithmeticRow, Matrix.reindex_apply]

@[simp]
theorem canonicalArithmeticSmallRowMatrix_block_apply
    {A x y L : ℕ}
    (block : Fin 2)
    (coord : CanonicalCoreCoordinate A x y L) :
    canonicalArithmeticSmallRowMatrix A x y L
        (finSumFinEquiv (Sum.inr block)) coord =
      blockBoundaryRow L block
        (canonicalCoreBoundaryColumn coord) := by
  simp [canonicalArithmeticSmallRowMatrix,
    canonicalArithmeticSmallRowMatrixRaw,
    canonicalArithmeticRow, Matrix.reindex_apply]

/-- Defective columns use the actual parity of their integer label. -/
theorem canonicalArithmeticSmallRowMatrix_prime_inl
    {A x y L : ℕ}
    (j : Fin (PrimesUpTo.count (L + 1)))
    (v :
      {v : Occurrence L //
        v ∈ canonicalCorrectedDefectiveVertices A x y L}) :
    canonicalArithmeticSmallRowMatrix A x y L
        (finSumFinEquiv (Sum.inl j))
        (Sum.inl v) =
      parityVec
        (twoStartCompleteVertexLabel x y L v.1)
        (PrimesUpTo.smallPrime (L + 1) j) := by
  classical
  rw [canonicalArithmeticSmallRowMatrix_prime_apply,
    canonicalCoreBoundaryColumn_inl]
  rw [primeBoundaryRow_apply]
  rw [Finset.sum_eq_single v.1]
  · simp [Pi.single_apply]
  · intro w _hw hne
    simp [Pi.single_apply, hne]
  · intro hnot
    exact (hnot (Finset.mem_univ v.1)).elim

/--
Residual-component columns use the parity vector of the actual product of
all labels in that component.
-/
theorem canonicalArithmeticSmallRowMatrix_prime_inr
    {A x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (j : Fin (PrimesUpTo.count (L + 1)))
    (C :
      {C : (largePrimeGraph x y L).ConnectedComponent //
        C ∈ canonicalResidualComponents A x y L}) :
    canonicalArithmeticSmallRowMatrix A x y L
        (finSumFinEquiv (Sum.inl j))
        (Sum.inr C) =
      parityVec
        (componentVertexProduct x y L C.1)
        (PrimesUpTo.smallPrime (L + 1) j) := by
  classical
  rw [canonicalArithmeticSmallRowMatrix_prime_apply]
  rw [canonicalCoreBoundaryColumn_eq_indicator]
  simp only [canonicalCoreComponent, primeBoundaryRow_apply]
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hnonzero :
      ∀ v ∈ componentVertices x y L C.1,
        twoStartCompleteVertexLabel x y L v ≠ 0 := by
    intro v hv
    exact
      (componentVertexLabel_pos hx hy C.1 hv).ne'
  have hparity :=
    DFunLike.congr_fun
      (parityVec_prod
        (componentVertices x y L C.1)
        (twoStartCompleteVertexLabel x y L)
        hnonzero)
      (PrimesUpTo.smallPrime (L + 1) j)
  simpa only [componentVertexProduct,
    Finsupp.finset_sum_apply, one_mul] using hparity.symm

/-! ## Matrix evaluation equals evaluation of the concrete boundary -/

/--
Before row reindexing, matrix multiplication is exactly evaluation of the
corresponding arithmetic row on the synthesized boundary.
-/
theorem canonicalArithmeticSmallRowMatrixRaw_mulVec
    {A x y L : ℕ}
    (row : CanonicalArithmeticRow L)
    (coeff : CanonicalCoreCoordinate A x y L → F₂) :
    (canonicalArithmeticSmallRowMatrixRaw A x y L).mulVec coeff row =
      canonicalArithmeticRow x y L row
        (canonicalCoreBoundarySynthesis A x y L coeff) := by
  classical
  simp only [Matrix.mulVec, dotProduct,
    canonicalArithmeticSmallRowMatrixRaw]
  change
    (∑ coord : CanonicalCoreCoordinate A x y L,
      canonicalArithmeticRow x y L row
          (canonicalCoreBoundaryColumn coord) *
        coeff coord) =
      canonicalArithmeticRow x y L row
        (∑ coord : CanonicalCoreCoordinate A x y L,
          coeff coord • canonicalCoreBoundaryColumn coord)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro coord _hcoord
  rw [map_smul]
  simp [smul_eq_mul, mul_comm]

/-- Concrete prime-row evaluation formula for the `Fin`-indexed matrix. -/
theorem canonicalArithmeticSmallRowMatrix_mulVec_prime
    {A x y L : ℕ}
    (j : Fin (PrimesUpTo.count (L + 1)))
    (coeff : CanonicalCoreCoordinate A x y L → F₂) :
    (canonicalArithmeticSmallRowMatrix A x y L).mulVec coeff
        (finSumFinEquiv (Sum.inl j)) =
      primeBoundaryRow x y L
        (PrimesUpTo.smallPrime (L + 1) j)
        (canonicalCoreBoundarySynthesis A x y L coeff) := by
  classical
  rw [Matrix.mulVec]
  simp only [dotProduct,
    canonicalArithmeticSmallRowMatrix_prime_apply]
  change
    (∑ coord : CanonicalCoreCoordinate A x y L,
      primeBoundaryRow x y L
          (PrimesUpTo.smallPrime (L + 1) j)
          (canonicalCoreBoundaryColumn coord) *
        coeff coord) =
      primeBoundaryRow x y L
        (PrimesUpTo.smallPrime (L + 1) j)
        (∑ coord : CanonicalCoreCoordinate A x y L,
          coeff coord • canonicalCoreBoundaryColumn coord)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro coord _hcoord
  rw [map_smul]
  simp [canonicalCoreBoundarySynthesis, smul_eq_mul, mul_comm]

/-- Concrete block-row evaluation formula for the `Fin`-indexed matrix. -/
theorem canonicalArithmeticSmallRowMatrix_mulVec_block
    {A x y L : ℕ}
    (block : Fin 2)
    (coeff : CanonicalCoreCoordinate A x y L → F₂) :
    (canonicalArithmeticSmallRowMatrix A x y L).mulVec coeff
        (finSumFinEquiv (Sum.inr block)) =
      blockBoundaryRow L block
        (canonicalCoreBoundarySynthesis A x y L coeff) := by
  classical
  rw [Matrix.mulVec]
  simp only [dotProduct,
    canonicalArithmeticSmallRowMatrix_block_apply]
  change
    (∑ coord : CanonicalCoreCoordinate A x y L,
      blockBoundaryRow L block
          (canonicalCoreBoundaryColumn coord) *
        coeff coord) =
      blockBoundaryRow L block
        (∑ coord : CanonicalCoreCoordinate A x y L,
          coeff coord • canonicalCoreBoundaryColumn coord)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro coord _hcoord
  rw [map_smul]
  simp [canonicalCoreBoundarySynthesis, smul_eq_mul, mul_comm]

/-! ## Arithmetic meaning of the kernel -/

/--
A complete two-block boundary is in the range of
`twoStartCompleteBoundary` exactly when its two block sums vanish.  This
direction is the one needed below; uniqueness follows from the already
proved injectivity of the boundary map.
-/
theorem existsUnique_twoStartCompleteBoundary_eq_of_blockRows
    {L : ℕ} {boundary : Occurrence L → F₂}
    (hleft :
      blockBoundaryRow L (0 : Fin 2) boundary = 0)
    (hright :
      blockBoundaryRow L (1 : Fin 2) boundary = 0) :
    ∃! coeff : Sum (Fin L) (Fin L) → F₂,
      twoStartCompleteBoundary L coeff = boundary := by
  have hleftEven :
      startVertexSum L (fun v ↦ boundary (Sum.inl v)) = 0 := by
    simpa [startVertexSum] using hleft
  have hrightEven :
      startVertexSum L (fun v ↦ boundary (Sum.inr v)) = 0 := by
    simpa [startVertexSum] using hright
  obtain ⟨leftCoeff, hleftCoeff, _hleftUnique⟩ :=
    existsUnique_startCompleteBoundary_eq hleftEven
  obtain ⟨rightCoeff, hrightCoeff, _hrightUnique⟩ :=
    existsUnique_startCompleteBoundary_eq hrightEven
  let coeff : Sum (Fin L) (Fin L) → F₂
    | Sum.inl i => leftCoeff i
    | Sum.inr i => rightCoeff i
  refine ⟨coeff, ?_, ?_⟩
  · funext v
    cases v with
    | inl v =>
        exact congrFun hleftCoeff v
    | inr v =>
        exact congrFun hrightCoeff v
  · intro other hother
    exact twoStartCompleteBoundary_injective L
      (hother.trans (by
        funext v
        cases v with
        | inl v =>
            exact (congrFun hleftCoeff v).symm
        | inr v =>
            exact (congrFun hrightCoeff v).symm))

/-- Every large-prime solution annihilates the corresponding prime row. -/
theorem primeBoundaryRow_eq_zero_of_mem_largePrimeSolution
    {x y L p : ℕ}
    (boundary : Occurrence L → F₂)
    (hboundary : boundary ∈ largePrimeSolution x y L)
    (hp : p.Prime) (hpLarge : L + 1 < p) :
    primeBoundaryRow x y L p boundary = 0 := by
  rw [primeBoundaryRow_apply,
    LargePrimeGraph.sum_mul_parityVec_eq_sum_primeOccurrences]
  exact
    (mem_largePrimeSolution.mp hboundary)
      p ⟨hp, hpLarge⟩

/--
The kernel of the concrete matrix has an exact arithmetic interpretation.
When the finite cylinder contains all small primes (`L + 1 ≤ M`), a core
coefficient vector is killed by the matrix if and only if its synthesized
boundary is the boundary of a unique genuine relation of the two-start
system.

This theorem proves the small-row equations themselves are complete.  The
later nonaligned closure combines it with the fact that, when the canonical
selector is `none`, the core columns are all free large-prime components and
the rational code is zero.
-/
theorem mem_kernel_iff_existsUnique_relation_boundary
    {M A x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hLM : L + 1 ≤ M)
    (coeff : CanonicalCoreCoordinate A x y L → F₂) :
    coeff ∈
        LinearMap.ker
          (canonicalArithmeticSmallRowMatrix A x y L).mulVecLin ↔
      ∃! relation :
          RelationSpace (twoStartSystem M x y L),
        relationBoundaryMap M x y L relation =
          canonicalCoreBoundarySynthesis A x y L coeff := by
  constructor
  · intro hkernel
    have hmatrix :
        (canonicalArithmeticSmallRowMatrix A x y L).mulVec coeff = 0 := by
      simpa only [Matrix.mulVecLin_apply] using
        (LinearMap.mem_ker.mp hkernel)
    have hprime
        (j : Fin (PrimesUpTo.count (L + 1))) :
        primeBoundaryRow x y L
            (PrimesUpTo.smallPrime (L + 1) j)
            (canonicalCoreBoundarySynthesis A x y L coeff) =
          0 := by
      have hrow :=
        congrFun hmatrix (finSumFinEquiv (Sum.inl j))
      rw [canonicalArithmeticSmallRowMatrix_mulVec_prime] at hrow
      exact hrow
    have hblock
        (block : Fin 2) :
        blockBoundaryRow L block
            (canonicalCoreBoundarySynthesis A x y L coeff) =
          0 := by
      have hrow :=
        congrFun hmatrix (finSumFinEquiv (Sum.inr block))
      rw [canonicalArithmeticSmallRowMatrix_mulVec_block] at hrow
      exact hrow
    obtain ⟨ambientCoeff, hambientBoundary, _hambientUnique⟩ :=
      existsUnique_twoStartCompleteBoundary_eq_of_blockRows
        (hblock 0) (hblock 1)
    have hambientRelation :
        ambientCoeff ∈
          RelationSpace (twoStartSystem M x y L) := by
      apply
        (mem_relationSpace_twoStartSystem_iff_boundary_prime_equations
          ambientCoeff).2
      intro p
      by_cases hpSmall : p.1.1 ≤ L + 1
      · obtain ⟨j, hj⟩ :=
          PrimesUpTo.exists_smallPrime_eq_of_prime_le
            p.2 hpSmall
        simpa [primeBoundaryRow_apply, hambientBoundary, hj] using
          hprime j
      · have hpLarge : L + 1 < p.1.1 := by omega
        have hlarge :=
          primeBoundaryRow_eq_zero_of_mem_largePrimeSolution
            (canonicalCoreBoundarySynthesis A x y L coeff)
            (canonicalCoreBoundarySynthesis_mem_largePrimeSolution
              hx hy coeff)
            p.2 hpLarge
        simpa [primeBoundaryRow_apply, hambientBoundary] using hlarge
    let relation :
        RelationSpace (twoStartSystem M x y L) :=
      ⟨ambientCoeff, hambientRelation⟩
    refine ⟨relation, ?_, ?_⟩
    · exact hambientBoundary
    · intro other hother
      apply relationBoundaryMap_injective M x y L
      exact hother.trans hambientBoundary.symm
  · rintro ⟨relation, hrelationBoundary, _hunique⟩
    apply LinearMap.mem_ker.mpr
    funext row
    obtain ⟨semanticRow, rfl⟩ :=
      finSumFinEquiv.surjective row
    cases semanticRow with
    | inl j =>
        rw [Matrix.mulVecLin_apply,
          canonicalArithmeticSmallRowMatrix_mulVec_prime,
          ← hrelationBoundary]
        let p : PrimeUpTo M :=
          ⟨⟨PrimesUpTo.smallPrime (L + 1) j,
              Nat.lt_succ_of_le
                ((PrimesUpTo.smallPrime_le (L + 1) j).trans hLM)⟩,
            PrimesUpTo.smallPrime_prime (L + 1) j⟩
        have hp :=
          (mem_relationSpace_twoStartSystem_iff_boundary_prime_equations
            (relation :
              Sum (Fin L) (Fin L) → F₂)).1
            relation.2 p
        simpa [primeBoundaryRow_apply, relationBoundaryMap, p] using hp
    | inr block =>
        rw [Matrix.mulVecLin_apply,
          canonicalArithmeticSmallRowMatrix_mulVec_block,
          ← hrelationBoundary]
        fin_cases block
        · change
            (∑ v : Fin (L + 1),
              startCompleteBoundary L
                (fun i ↦
                  (relation :
                    Sum (Fin L) (Fin L) → F₂) (Sum.inl i)) v) =
              0
          simpa only [startVertexSum_apply] using
            startVertexSum_startCompleteBoundary_eq_zero
              (fun i ↦
                (relation :
                  Sum (Fin L) (Fin L) → F₂) (Sum.inl i))
        · change
            (∑ v : Fin (L + 1),
              startCompleteBoundary L
                (fun i ↦
                  (relation :
                    Sum (Fin L) (Fin L) → F₂) (Sum.inr i)) v) =
              0
          simpa only [startVertexSum_apply] using
            startVertexSum_startCompleteBoundary_eq_zero
              (fun i ↦
                (relation :
                  Sum (Fin L) (Fin L) → F₂) (Sum.inr i))

/-! ## The reduced interface -/

/--
The source-exact arithmetic-kernel statement.  Lemma 9.10 is used only in
the nonaligned branch, i.e. when the canonical selector is `none`.  The two
endpoint inequalities state that the finite cylinder contains every label
on both complete boundaries.  Under these hypotheses, the residual quotient
is linearly equivalent to the kernel of the concrete arithmetic matrix.
-/
/- AUDIT_BRIDGE
{
  "id": "PCv07c-L9.10-arithmetic-kernel-equivalence",
  "kind": "internal",
  "status": "discharged",
  "lean_name": "PaperC.CanonicalSmallRows.CanonicalArithmeticKernelStatement",
  "discharged_by": [
    "PaperC.CanonicalSmallRows.canonicalArithmeticKernelStatement",
    "PaperC.CanonicalSmallRows.residualTau_eq_corrected_add_components_sub_arithmeticRank_of_choice_none"
  ],
  "citation": {
    "authors": ["Brice Pouly"],
    "title": "Loi de Poisson critique dans un bloc dyadique — Débuts de longues plages constantes d’une fonction aléatoire complètement multiplicative de Rademacher étendue",
    "version": "7c, juillet 2026",
    "target_pdf_sha256": "23a5db3c8d024cab3fb8ca9f8f1443f40cf9502b1fb6682a331f5948f57a3336",
    "locator": "Lemme 9.10, démonstration, p. 32"
  },
  "source_statement": {
    "verbatim": "Le lemme 6.1 identifie l’espace des solutions des grands premiers à F_2^{D#+c#} dans la branche non alignée. Les seules équations qui restent sont les lignes de M̃.",
    "source_url": "paper_C_complete_v07c.pdf#page=32",
    "verification": "manual_primary_source_check_required"
  },
  "manuscript_locator": {
    "result": "Lemma 9.10",
    "equation": "(9.9)",
    "pages": "32"
  },
  "formalization_relation": "source-exact nonaligned statement for Lemma 9.10: when no canonical rational channel exists and the finite cylinder covers both complete boundaries, the residual quotient is the kernel of the fixed prime-and-block matrix"
}
AUDIT_BRIDGE -/
def CanonicalArithmeticKernelStatement
    (M A x y L : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (_hLM : L + 1 ≤ M) : Prop :=
  canonicalReducedCandidate?
        x y (L + 1) ((L + 1) ^ A) =
      none →
    x + L ≤ M →
    y + L ≤ M →
    Nonempty
      (ResidualQuotient M A x y L hx hy ≃ₗ[F₂]
        LinearMap.ker
          (canonicalArithmeticSmallRowMatrix A x y L).mulVecLin)

/-! ## Source-exact closure in the nonaligned branch -/

/--
When the canonical selector finds no rational channel, the concrete core
coordinates have the same dimension as the full large-prime solution.
-/
theorem finrank_canonicalCoreCoordinates_eq_largePrimeSolution_of_choice_none
    {A x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hchoice :
      canonicalReducedCandidate?
          x y (L + 1) ((L + 1) ^ A) =
        none) :
    Module.finrank F₂
        (CanonicalCoreCoordinate A x y L → F₂) =
      Module.finrank F₂ (largePrimeSolution x y L) := by
  rw [Module.finrank_pi,
    card_canonicalCoreCoordinate hx hy,
    finrank_largePrimeSolution_eq_defective_add_components
      (show 1 ≤ x by omega) (show 1 ≤ y by omega)]
  simp [canonicalCorrectedDefectCount,
    canonicalResidualComponentCount, hchoice]

/--
In the nonaligned branch, the concrete component synthesis is a linear
equivalence onto the full space of large-prime solutions.
-/
noncomputable def canonicalCoreBoundaryLinearEquivLargePrime_of_choice_none
    {A x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hchoice :
      canonicalReducedCandidate?
          x y (L + 1) ((L + 1) ^ A) =
        none) :
    (CanonicalCoreCoordinate A x y L → F₂) ≃ₗ[F₂]
      largePrimeSolution x y L :=
  (canonicalCoreBoundaryToLargePrime
      (A := A) (L := L) hx hy).linearEquivOfInjective
    (canonicalCoreBoundaryToLargePrime_injective
      (A := A) (L := L) hx hy)
    (finrank_canonicalCoreCoordinates_eq_largePrimeSolution_of_choice_none
      hx hy hchoice)

/--
Coordinates of a complete relation in the nonaligned component basis.
Endpoint coverage is exactly what places every relation boundary in the
large-prime solution.
-/
noncomputable def relationToCanonicalCoreCoordinates_of_choice_none
    {M A x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hxM : x + L ≤ M) (hyM : y + L ≤ M)
    (hchoice :
      canonicalReducedCandidate?
          x y (L + 1) ((L + 1) ^ A) =
        none) :
    RelationSpace (twoStartSystem M x y L) →ₗ[F₂]
      (CanonicalCoreCoordinate A x y L → F₂) :=
  (canonicalCoreBoundaryLinearEquivLargePrime_of_choice_none
      hx hy hchoice).symm.toLinearMap.comp
    (relationBoundaryToLargePrime M x y L
      hx hy hxM hyM)

/-- Synthesizing the preceding coordinates recovers the original boundary. -/
theorem canonicalCoreBoundarySynthesis_relationToCoordinates_of_choice_none
    {M A x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hxM : x + L ≤ M) (hyM : y + L ≤ M)
    (hchoice :
      canonicalReducedCandidate?
          x y (L + 1) ((L + 1) ^ A) =
        none)
    (relation : RelationSpace (twoStartSystem M x y L)) :
    canonicalCoreBoundarySynthesis A x y L
        (relationToCanonicalCoreCoordinates_of_choice_none
          hx hy hxM hyM hchoice relation) =
      relationBoundaryMap M x y L relation := by
  have heq :=
    (canonicalCoreBoundaryLinearEquivLargePrime_of_choice_none
      hx hy hchoice).apply_symm_apply
        (relationBoundaryToLargePrime M x y L
          hx hy hxM hyM relation)
  exact congrArg Subtype.val heq

/--
Every complete relation determines a vector in the kernel of the concrete
small-row matrix.
-/
noncomputable def relationToCanonicalArithmeticKernel_of_choice_none
    {M A x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hLM : L + 1 ≤ M)
    (hxM : x + L ≤ M) (hyM : y + L ≤ M)
    (hchoice :
      canonicalReducedCandidate?
          x y (L + 1) ((L + 1) ^ A) =
        none) :
    RelationSpace (twoStartSystem M x y L) →ₗ[F₂]
      LinearMap.ker
        (canonicalArithmeticSmallRowMatrix A x y L).mulVecLin :=
  (relationToCanonicalCoreCoordinates_of_choice_none
      hx hy hxM hyM hchoice).codRestrict
    (LinearMap.ker
      (canonicalArithmeticSmallRowMatrix A x y L).mulVecLin)
    (fun relation ↦ by
      apply
        (mem_kernel_iff_existsUnique_relation_boundary
          hx hy hLM
          (relationToCanonicalCoreCoordinates_of_choice_none
            hx hy hxM hyM hchoice relation)).2
      refine ⟨relation, ?_, ?_⟩
      · exact
          (canonicalCoreBoundarySynthesis_relationToCoordinates_of_choice_none
            hx hy hxM hyM hchoice relation).symm
      · intro other hother
        apply relationBoundaryMap_injective M x y L
        exact hother.trans
          (canonicalCoreBoundarySynthesis_relationToCoordinates_of_choice_none
            hx hy hxM hyM hchoice relation))

/-- The relation-to-kernel map is injective. -/
theorem relationToCanonicalArithmeticKernel_of_choice_none_injective
    {M A x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hLM : L + 1 ≤ M)
    (hxM : x + L ≤ M) (hyM : y + L ≤ M)
    (hchoice :
      canonicalReducedCandidate?
          x y (L + 1) ((L + 1) ^ A) =
        none) :
    Function.Injective
      (relationToCanonicalArithmeticKernel_of_choice_none
        hx hy hLM hxM hyM hchoice) := by
  intro relation₁ relation₂ heq
  apply relationBoundaryMap_injective M x y L
  rw [←
    canonicalCoreBoundarySynthesis_relationToCoordinates_of_choice_none
      hx hy hxM hyM hchoice relation₁,
    ←
    canonicalCoreBoundarySynthesis_relationToCoordinates_of_choice_none
      hx hy hxM hyM hchoice relation₂]
  have hcoords :
      relationToCanonicalCoreCoordinates_of_choice_none
          hx hy hxM hyM hchoice relation₁ =
        relationToCanonicalCoreCoordinates_of_choice_none
          hx hy hxM hyM hchoice relation₂ := by
    simpa [relationToCanonicalArithmeticKernel_of_choice_none] using
      congrArg Subtype.val heq
  exact congrArg
    (canonicalCoreBoundarySynthesis A x y L) hcoords

/-- The relation-to-kernel map is surjective. -/
theorem relationToCanonicalArithmeticKernel_of_choice_none_surjective
    {M A x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hLM : L + 1 ≤ M)
    (hxM : x + L ≤ M) (hyM : y + L ≤ M)
    (hchoice :
      canonicalReducedCandidate?
          x y (L + 1) ((L + 1) ^ A) =
        none) :
    Function.Surjective
      (relationToCanonicalArithmeticKernel_of_choice_none
        hx hy hLM hxM hyM hchoice) := by
  intro coeff
  obtain ⟨relation, hboundary, _hunique⟩ :=
    (mem_kernel_iff_existsUnique_relation_boundary
      hx hy hLM coeff.1).1 coeff.2
  refine ⟨relation, Subtype.ext ?_⟩
  change
    relationToCanonicalCoreCoordinates_of_choice_none
        hx hy hxM hyM hchoice relation =
      coeff.1
  apply canonicalCoreBoundarySynthesis_injective hx hy
  rw [
    canonicalCoreBoundarySynthesis_relationToCoordinates_of_choice_none
      hx hy hxM hyM hchoice relation]
  exact hboundary

/--
The complete relation space is linearly equivalent to the concrete
small-row kernel in the exact nonaligned scope of Lemma 9.10.
-/
noncomputable def relationLinearEquivCanonicalArithmeticKernel_of_choice_none
    {M A x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hLM : L + 1 ≤ M)
    (hxM : x + L ≤ M) (hyM : y + L ≤ M)
    (hchoice :
      canonicalReducedCandidate?
          x y (L + 1) ((L + 1) ^ A) =
        none) :
    RelationSpace (twoStartSystem M x y L) ≃ₗ[F₂]
      LinearMap.ker
        (canonicalArithmeticSmallRowMatrix A x y L).mulVecLin :=
  LinearEquiv.ofBijective
    (relationToCanonicalArithmeticKernel_of_choice_none
      hx hy hLM hxM hyM hchoice)
    ⟨relationToCanonicalArithmeticKernel_of_choice_none_injective
        hx hy hLM hxM hyM hchoice,
      relationToCanonicalArithmeticKernel_of_choice_none_surjective
        hx hy hLM hxM hyM hchoice⟩

/--
Unconditional, source-exact closure of the arithmetic kernel statement in
the nonaligned branch.  The endpoint hypotheses are the finite-cylinder
coverage assumptions used by the boundary embedding.
-/
theorem canonicalArithmeticKernelEquivalence_of_choice_none
    {M A x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hLM : L + 1 ≤ M)
    (hxM : x + L ≤ M) (hyM : y + L ≤ M)
    (hchoice :
      canonicalReducedCandidate?
          x y (L + 1) ((L + 1) ^ A) =
        none) :
    Nonempty
      (ResidualQuotient M A x y L hx hy ≃ₗ[F₂]
        LinearMap.ker
          (canonicalArithmeticSmallRowMatrix A x y L).mulVecLin) := by
  have hcode :
      canonicalRationalCode M A x y L hx hy = ⊥ := by
    simp [canonicalRationalCode, hchoice]
  exact
    ⟨(canonicalRationalCode M A x y L hx hy).quotEquivOfEqBot hcode
      |>.trans
        (relationLinearEquivCanonicalArithmeticKernel_of_choice_none
          hx hy hLM hxM hyM hchoice)⟩

/--
Lemma 9.10 in its complete source scope, with no arithmetic bridge.
-/
theorem canonicalArithmeticKernelStatement
    (M A x y L : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hLM : L + 1 ≤ M) :
    CanonicalArithmeticKernelStatement M A x y L hx hy hLM := by
  intro hchoice hxM hyM
  exact
    canonicalArithmeticKernelEquivalence_of_choice_none
      hx hy hLM hxM hyM hchoice

/--
The reduced quotient--kernel statement supplies concrete presentation data,
with the fixed row count and fixed arithmetic matrix.
-/
theorem canonicalSmallRowPresentation_of_arithmeticKernel
    {M A x y L : ℕ}
    {hx : 2 ≤ x} {hy : 2 ≤ y}
    (hLM : L + 1 ≤ M)
    (hchoice :
      canonicalReducedCandidate?
          x y (L + 1) ((L + 1) ^ A) =
        none)
    (hxM : x + L ≤ M) (hyM : y + L ≤ M)
    (hkernel :
      CanonicalArithmeticKernelStatement M A x y L hx hy hLM) :
    Nonempty (CanonicalSmallRowPresentation M A x y L hx hy) := by
  obtain ⟨equiv⟩ := hkernel hchoice hxM hyM
  exact
    ⟨{
      rowCount := PrimesUpTo.count (L + 1) + 2
      matrix := canonicalArithmeticSmallRowMatrix A x y L
      quotientEquivKernel := equiv
    }⟩

/--
Lemma 9.10 with the reduced internal boundary: `k̃` is now the rank of the
fixed arithmetic matrix rather than the rank of an existentially supplied
matrix.
-/
theorem residualTau_eq_corrected_add_components_sub_arithmeticRank
    {M A x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hLM : L + 1 ≤ M)
    (hchoice :
      canonicalReducedCandidate?
          x y (L + 1) ((L + 1) ^ A) =
        none)
    (hxM : x + L ≤ M) (hyM : y + L ≤ M)
    (hkernel :
      CanonicalArithmeticKernelStatement M A x y L hx hy hLM) :
    residualTau M A x y L hx hy =
      canonicalCorrectedDefectCount A x y L +
          canonicalResidualComponentCount A x y L -
        canonicalSmallRowRank
          (canonicalArithmeticSmallRowMatrix A x y L) := by
  obtain ⟨equiv⟩ := hkernel hchoice hxM hyM
  let presentation :
      CanonicalSmallRowPresentation M A x y L hx hy := {
    rowCount := PrimesUpTo.count (L + 1) + 2
    matrix := canonicalArithmeticSmallRowMatrix A x y L
    quotientEquivKernel := equiv
  }
  simpa [presentation, CanonicalSmallRowPresentation.kTilde] using
    residualTau_eq_corrected_add_components_sub_kTilde
      hx hy presentation

/--
Unconditional exact-rank formula in the nonaligned branch of Lemma 9.10.
-/
theorem residualTau_eq_corrected_add_components_sub_arithmeticRank_of_choice_none
    {M A x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hLM : L + 1 ≤ M)
    (hxM : x + L ≤ M) (hyM : y + L ≤ M)
    (hchoice :
      canonicalReducedCandidate?
          x y (L + 1) ((L + 1) ^ A) =
        none) :
    residualTau M A x y L hx hy =
      canonicalCorrectedDefectCount A x y L +
          canonicalResidualComponentCount A x y L -
        canonicalSmallRowRank
          (canonicalArithmeticSmallRowMatrix A x y L) := by
  exact
    residualTau_eq_corrected_add_components_sub_arithmeticRank
      hx hy hLM hchoice hxM hyM
      (canonicalArithmeticKernelStatement
        M A x y L hx hy hLM)

end

end CanonicalSmallRows
end PaperC
