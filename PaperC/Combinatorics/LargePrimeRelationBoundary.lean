import PaperC.Affine.RelationBoundaryIff
import PaperC.Combinatorics.ExactUnitIsolation
import PaperC.LinearAlgebra.QuotientParity

set_option maxHeartbeats 1600000

/-!
# Complete relations inside the large-prime solution

This module supplies the concrete boundary map used in Lemma 6.4.  Provided
the finite Rademacher cylinder contains every complete vertex label, the
boundary of every complete two-start relation satisfies all equations at
primes above `L+1`.  The boundary map is injective and every one of its
values has even parity in the left block.

One exact unit gives a vector of `W_{>B}` with odd left-block parity.
Consequently the complete relation space lies in a codimension-one
hyperplane of `W_{>B}`.
-/

namespace PaperC
namespace LargePrimeRelationBoundary

open Affine
open Affine.RationalChannelCode
open ExactUnitIsolation
open ExactUnitLargeKernel
open LargePrimeOccurrences
open LargePrimeGraph
open LargePrimeComponents

noncomputable section

/-- Complete boundary, restricted to the full relation space. -/
def relationBoundaryMap
    (M x y L : ℕ) :
    RelationSpace (twoStartSystem M x y L) →ₗ[F₂]
      (Occurrence L → F₂) :=
  (twoStartCompleteBoundary L).domRestrict
    (RelationSpace (twoStartSystem M x y L))

@[simp]
theorem relationBoundaryMap_apply
    (M x y L : ℕ)
    (u : RelationSpace (twoStartSystem M x y L)) :
    relationBoundaryMap M x y L u =
      twoStartCompleteBoundary L
        (u : Sum (Fin L) (Fin L) → F₂) :=
  rfl

/-- Injectivity is inherited from the complete two-block boundary. -/
theorem relationBoundaryMap_injective
    (M x y L : ℕ) :
    Function.Injective (relationBoundaryMap M x y L) := by
  intro u v huv
  apply Subtype.ext
  apply twoStartCompleteBoundary_injective L
  exact huv

/-- Every complete label is positive for a start based at least at two. -/
theorem twoStartCompleteVertexLabel_pos
    {x y L : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y)
    (v : Occurrence L) :
    0 < twoStartCompleteVertexLabel x y L v := by
  cases v with
  | inl v =>
      exact RationalChannelCode.startCompleteVertexLabel_pos hx v
  | inr v =>
      exact RationalChannelCode.startCompleteVertexLabel_pos hy v

/--
If the cylinder reaches both right endpoints, it contains every complete
vertex label.
-/
theorem twoStartCompleteVertexLabel_le
    {M x y L : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hxM : x + L ≤ M) (hyM : y + L ≤ M)
    (v : Occurrence L) :
    twoStartCompleteVertexLabel x y L v ≤ M := by
  cases v with
  | inl v =>
      exact
        (Nat.le_of_lt
          (startCompleteVertexLabel_upper
            (show 1 ≤ x by omega) v)).trans hxM
  | inr v =>
      exact
        (Nat.le_of_lt
          (startCompleteVertexLabel_upper
            (show 1 ≤ y by omega) v)).trans hyM

/--
Every complete relation boundary solves the large-prime equations, as soon
as the finite cylinder contains all labels occurring in the two boundaries.
-/
theorem relationBoundaryMap_mem_largePrimeSolution
    {M x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hxM : x + L ≤ M) (hyM : y + L ≤ M)
    (u : RelationSpace (twoStartSystem M x y L)) :
    relationBoundaryMap M x y L u ∈
      largePrimeSolution x y L := by
  rw [mem_largePrimeSolution_iff_boundary_prime_equations]
  intro p hp
  by_cases hpM : p ≤ M
  · let q : PrimeUpTo M :=
      ⟨⟨p, Nat.lt_succ_of_le hpM⟩, hp.1⟩
    have hrelation :=
      (mem_relationSpace_twoStartSystem_iff_boundary_prime_equations
        (u : Sum (Fin L) (Fin L) → F₂)).mp u.2 q
    simpa [relationBoundaryMap, q] using hrelation
  · have hzero :
        ∀ v : Occurrence L,
          parityVec (twoStartCompleteVertexLabel x y L v) p = 0 := by
      intro v
      by_contra hv
      have hpdvd :
          p ∣ twoStartCompleteVertexLabel x y L v :=
        RelationalPrimeAssignment.dvd_of_parityVec_ne_zero hv
      have hpLabel :
          p ≤ twoStartCompleteVertexLabel x y L v :=
        Nat.le_of_dvd
          (twoStartCompleteVertexLabel_pos hx hy v) hpdvd
      exact hpM
        (hpLabel.trans
          (twoStartCompleteVertexLabel_le
            hx hy hxM hyM v))
    apply Finset.sum_eq_zero
    intro v _hv
    rw [hzero v, mul_zero]

/-- The complete relation boundary with codomain restricted to `W_{>B}`. -/
def relationBoundaryToLargePrime
    (M x y L : ℕ)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hxM : x + L ≤ M) (hyM : y + L ≤ M) :
    RelationSpace (twoStartSystem M x y L) →ₗ[F₂]
      largePrimeSolution x y L :=
  (relationBoundaryMap M x y L).codRestrict
    (largePrimeSolution x y L)
    (relationBoundaryMap_mem_largePrimeSolution
      hx hy hxM hyM)

/-- The boundary embedding into `W_{>B}` remains injective. -/
theorem relationBoundaryToLargePrime_injective
    {M x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hxM : x + L ≤ M) (hyM : y + L ≤ M) :
    Function.Injective
      (relationBoundaryToLargePrime M x y L
        hx hy hxM hyM) := by
  intro u v huv
  apply relationBoundaryMap_injective M x y L
  exact congrArg Subtype.val huv

/-- Parity of the selected occurrences in the left block. -/
def leftBlockParity (L : ℕ) :
    (Occurrence L → F₂) →ₗ[F₂] F₂ where
  toFun u := ∑ v : Fin (L + 1), u (Sum.inl v)
  map_add' u v := by
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c u := by
    change
      (∑ v : Fin (L + 1), c * u (Sum.inl v)) =
        c * ∑ v : Fin (L + 1), u (Sum.inl v)
    rw [Finset.mul_sum]

@[simp]
theorem leftBlockParity_apply
    (L : ℕ) (u : Occurrence L → F₂) :
    leftBlockParity L u =
      ∑ v : Fin (L + 1), u (Sum.inl v) :=
  rfl

/-- Every complete boundary has even parity separately in the left block. -/
theorem leftBlockParity_relationBoundaryMap
    (M x y L : ℕ)
    (u : RelationSpace (twoStartSystem M x y L)) :
    leftBlockParity L (relationBoundaryMap M x y L u) = 0 := by
  change
    ∑ v : Fin (L + 1),
      startCompleteBoundary L
        (fun i => (u : Sum (Fin L) (Fin L) → F₂) (Sum.inl i)) v = 0
  simpa only [startVertexSum_apply] using
    (startVertexSum_startCompleteBoundary_eq_zero
      (fun i => (u : Sum (Fin L) (Fin L) → F₂) (Sum.inl i)))

/-- The two boundary occurrences belonging to one exact unit. -/
def exactUnitBoundaryVector
    {L a b : ℕ} {h : ℤ}
    (unit : ChannelUnit L a b h) :
    Occurrence L → F₂ :=
  Pi.single (Sum.inl unit.1.1) 1 +
    Pi.single (Sum.inr unit.1.2) 1

/-- Pairing the unit vector with one prime selects its two endpoints. -/
theorem sum_exactUnitBoundaryVector_mul_parityVec
    {x y L a b p : ℕ} {h : ℤ}
    (unit : ChannelUnit L a b h) :
    (∑ v : Occurrence L,
        exactUnitBoundaryVector unit v *
          parityVec
            (twoStartCompleteVertexLabel x y L v) p) =
      parityVec
          (startCompleteVertexLabel x L unit.1.1) p +
        parityVec
          (startCompleteVertexLabel y L unit.1.2) p := by
  classical
  simp [exactUnitBoundaryVector, twoStartCompleteVertexLabel,
    Pi.single_apply, add_mul, Finset.sum_add_distrib]

/-- Each exact unit individually supplies a vector of `W_{>B}`. -/
theorem exactUnitBoundaryVector_mem_largePrimeSolution
    {x y L a b : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hheight : h = (b : ℤ) * y - (a : ℤ) * x)
    (hsmall : Nat.max a b < L + 1)
    (unit : ChannelUnit L a b h) :
    exactUnitBoundaryVector unit ∈
      largePrimeSolution x y L := by
  rw [mem_largePrimeSolution_iff_boundary_prime_equations]
  intro p hp
  rw [sum_exactUnitBoundaryVector_mul_parityVec unit]
  obtain ⟨t, hfactor⟩ :=
    channelUnit_exactUnitFactorization
      ha hb hab hx hy hheight hsmall unit
  have hparity :=
    exactUnit_large_parity_eq hfactor hp.1 hp.2
  rw [hparity.1, hparity.2]
  exact ZModModule.add_self _

/-- One unit has odd left-block parity. -/
@[simp]
theorem leftBlockParity_exactUnitBoundaryVector
    {L a b : ℕ} {h : ℤ}
    (unit : ChannelUnit L a b h) :
    leftBlockParity L (exactUnitBoundaryVector unit) = 1 := by
  classical
  simp [leftBlockParity, exactUnitBoundaryVector,
    Pi.single_apply]

/-- Restriction of the left-block parity functional to `W_{>B}`. -/
def leftBlockParityOnLargePrime
    (x y L : ℕ) :
    largePrimeSolution x y L →ₗ[F₂] F₂ :=
  (leftBlockParity L).domRestrict
    (largePrimeSolution x y L)

/-- The presence of one exact unit makes the restricted parity surjective. -/
theorem leftBlockParityOnLargePrime_surjective
    {x y L a b : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hheight : h = (b : ℤ) * y - (a : ℤ) * x)
    (hsmall : Nat.max a b < L + 1)
    (unit : ChannelUnit L a b h) :
    Function.Surjective
      (leftBlockParityOnLargePrime x y L) := by
  let w : largePrimeSolution x y L :=
    ⟨exactUnitBoundaryVector unit,
      exactUnitBoundaryVector_mem_largePrimeSolution
        ha hb hab hx hy hheight hsmall unit⟩
  intro c
  refine ⟨c • w, ?_⟩
  change
    leftBlockParity L
      (c • (w : Occurrence L → F₂)) = c
  rw [LinearMap.map_smul]
  have hleft :=
    leftBlockParity_exactUnitBoundaryVector unit
  change
    c * (∑ v : Fin (L + 1),
      exactUnitBoundaryVector unit (Sum.inl v)) = c
  change
    (∑ v : Fin (L + 1),
      exactUnitBoundaryVector unit (Sum.inl v)) = 1 at hleft
  rw [hleft, mul_one]

/-- In particular the left-block parity survives on `W_{>B}`. -/
theorem leftBlockParityOnLargePrime_ne_zero
    {x y L a b : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hheight : h = (b : ℤ) * y - (a : ℤ) * x)
    (hsmall : Nat.max a b < L + 1)
    (unit : ChannelUnit L a b h) :
    leftBlockParityOnLargePrime x y L ≠ 0 := by
  intro hzero
  obtain ⟨w, hw⟩ :=
    leftBlockParityOnLargePrime_surjective
      ha hb hab hx hy hheight hsmall unit 1
  rw [hzero] at hw
  simp at hw

/--
Without using an exact unit, injectivity of the complete boundary already
gives the elementary inclusion `ρ ≤ dim W_{>B}`.
-/
theorem relationRho_le_finrank_largePrimeSolution
    {M x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hxM : x + L ≤ M) (hyM : y + L ≤ M) :
    relationRho (twoStartSystem M x y L) ≤
      Module.finrank F₂ (largePrimeSolution x y L) := by
  unfold relationRho
  exact
    LinearMap.finrank_le_finrank_of_injective
      (relationBoundaryToLargePrime_injective
        hx hy hxM hyM)

/--
The complete relation space loses one dimension inside `W_{>B}` because all
its boundaries have even left-block parity.
-/
theorem relationRho_le_finrank_largePrimeSolution_sub_one
    {M x y L a b : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hxM : x + L ≤ M) (hyM : y + L ≤ M)
    (hheight : h = (b : ℤ) * y - (a : ℤ) * x)
    (hsmall : Nat.max a b < L + 1)
    (unit : ChannelUnit L a b h) :
    relationRho (twoStartSystem M x y L) ≤
      Module.finrank F₂ (largePrimeSolution x y L) - 1 := by
  let R : Submodule F₂ (largePrimeSolution x y L) :=
    LinearMap.range
      (relationBoundaryToLargePrime M x y L
        hx hy hxM hyM)
  have hRker :
      R ≤ LinearMap.ker
        (leftBlockParityOnLargePrime x y L) := by
    intro w hw
    obtain ⟨u, rfl⟩ := hw
    exact leftBlockParity_relationBoundaryMap M x y L u
  have hRdim :
      Module.finrank F₂ R =
        relationRho (twoStartSystem M x y L) := by
    change
      Module.finrank F₂
          (LinearMap.range
            (relationBoundaryToLargePrime M x y L
              hx hy hxM hyM)) =
        relationRho (twoStartSystem M x y L)
    rw [LinearMap.finrank_range_of_inj
      (relationBoundaryToLargePrime_injective
        hx hy hxM hyM)]
    rfl
  rw [← hRdim]
  exact
    QuotientParity.finrank_le_finrank_sub_one_of_le_ker
      (leftBlockParityOnLargePrime x y L)
      (leftBlockParityOnLargePrime_ne_zero
        ha hb hab hx hy hheight hsmall unit)
      hRker

end

end LargePrimeRelationBoundary
end PaperC
