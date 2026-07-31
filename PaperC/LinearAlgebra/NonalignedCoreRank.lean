import PaperC.Combinatorics.LargePrimeGraphResolution
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option maxHeartbeats 800000

/-!
# Exact rank of the nonaligned core

This file isolates the rank--nullity calculation in Lemma 9.10.

After Lemma 6.1, a large-prime solution is described by one binary
coordinate on every unpinned connected component.  Any equations that
remain to be imposed therefore form a linear map on that component
coordinate space.  We denote the rank of this map by `kTilde`.  Its kernel
has the exact dimension

`number of free components - kTilde`.

The final theorem transports the calculation back through
`largePrimeSolutionLinearEquiv` and rewrites the number of free components
as `D + c`.
-/

namespace PaperC
namespace NonalignedCoreRank

open LargePrimeGraph
open LargePrimeGraphResolution
open PinnedGraphResolution

noncomputable section

variable {W : Type*} [AddCommGroup W] [Module F₂ W]

/--
The manuscript's `k̃`: the rank of the remaining linear constraints on a
finite family of free component coordinates.
-/
noncomputable def kTilde
    {ι : Type*} [Fintype ι]
    (constraints : (ι → F₂) →ₗ[F₂] W) : ℕ :=
  Module.finrank F₂ (LinearMap.range constraints)

/--
Rank--nullity on the free component coordinates, in the exact truncated
subtraction form used in Lemma 9.10.
-/
theorem finrank_componentKernel_eq_card_sub_kTilde
    {ι : Type*} [Fintype ι]
    (constraints : (ι → F₂) →ₗ[F₂] W) :
    Module.finrank F₂ (LinearMap.ker constraints) =
      Fintype.card ι - kTilde constraints := by
  have h :=
    LinearMap.finrank_range_add_finrank_ker constraints
  rw [Module.finrank_pi] at h
  unfold kTilde
  omega

/--
Transport component-coordinate constraints back to the concrete
large-prime solution space.
-/
noncomputable def largePrimeConstraintMap
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (constraints :
      (UnpinnedComponent
          (largePrimeGraph x y L)
          (pinnedVertices x y L) → F₂) →ₗ[F₂] W) :
    largePrimeSolution x y L →ₗ[F₂] W :=
  constraints.comp
    (largePrimeSolutionLinearEquiv hx hy).toLinearMap

/--
The rank of the remaining constraints after the component resolution.
This definition makes explicit that the equations are evaluated on the
concrete space `W_{>B}(x,y)`, after transport through Lemma 6.1.
-/
noncomputable def largePrimeKTilde
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (constraints :
      (UnpinnedComponent
          (largePrimeGraph x y L)
          (pinnedVertices x y L) → F₂) →ₗ[F₂] W) : ℕ :=
  Module.finrank F₂
    (LinearMap.range
      (largePrimeConstraintMap hx hy constraints))

/--
Transport through the component equivalence does not change the rank of
the remaining constraints.
-/
theorem largePrimeKTilde_eq_kTilde
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (constraints :
      (UnpinnedComponent
          (largePrimeGraph x y L)
          (pinnedVertices x y L) → F₂) →ₗ[F₂] W) :
    largePrimeKTilde hx hy constraints =
      kTilde constraints := by
  unfold largePrimeKTilde largePrimeConstraintMap kTilde
  rw [LinearMap.range_comp_of_range_eq_top]
  exact (largePrimeSolutionLinearEquiv hx hy).range

/--
Exact-rank formula on the uncorrected large-prime component coordinates.

For arbitrary remaining binary linear constraints, the admissible
large-prime solutions have dimension `D + c - k̃`.
-/
theorem largePrime_exact_rank
    {x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (constraints :
      (UnpinnedComponent
          (largePrimeGraph x y L)
          (pinnedVertices x y L) → F₂) →ₗ[F₂] W) :
    Module.finrank F₂
        (LinearMap.ker
          (largePrimeConstraintMap hx hy constraints)) =
      defectiveVertexCount x y L +
          nontrivialComponentCount x y L -
        kTilde constraints := by
  rw [← largePrimeKTilde_eq_kTilde hx hy constraints]
  have h :=
    LinearMap.finrank_range_add_finrank_ker
      (largePrimeConstraintMap hx hy constraints)
  rw [finrank_largePrimeSolution_eq_defective_add_components hx hy] at h
  unfold largePrimeKTilde
  omega

/--
Lemma 9.10 in residual-coordinate form.

Once the nonaligned quotient has been identified with an index type having
exactly `D# + c#` coordinates, rank--nullity gives

`τ = D# + c# - k̃`.

The cardinality equality is kept explicit: constructing this residual
coordinate equivalence from the canonical rational quotient is a separate
graph-theoretic interface, and is not hidden in the rank calculation.
-/
theorem lemma_nine_ten_exact_rank
    {ι : Type*} [Fintype ι]
    {Dsharp csharp : ℕ}
    (hcard : Fintype.card ι = Dsharp + csharp)
    (constraints : (ι → F₂) →ₗ[F₂] W) :
    Module.finrank F₂ (LinearMap.ker constraints) =
      Dsharp + csharp - kTilde constraints := by
  rw [finrank_componentKernel_eq_card_sub_kTilde, hcard]

end

end NonalignedCoreRank
end PaperC
