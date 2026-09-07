import PaperCV282.ClosureAlgebraFourier
import PaperC.Affine.StartBoundaryRange

/-! # The affine law of an arbitrary finite tuple of starts

Tuple labels are retained, so repeated or overlapping windows cause no
identification of equations. The only cutoff condition is that it covers
every actual start support.
-/
namespace PaperC.V282.ClosureAlgebraStartTuple

open Affine AffineBorderCylinders ClosureAlgebraFourier InfiniteRademacher InfiniteCylinderTransfer
open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι]

local instance instDecidableIndex : DecidableEq ι := Classical.decEq _

/-- The literal stack of all L equations for every tuple label. -/
def tupleSystem (M L : ℕ) (x : ι → ℕ) :
    SampleSpace M →ₗ[F₂] (ι × Fin L → F₂) :=
  LinearMap.pi (fun i => startRow M (x i.1) L i.2)

/-- Each block has exactly its own left-boundary affine equation. -/
def tupleRhs (L : ℕ) : ι × Fin L → F₂ := fun i => startRhs L i.2

/-- The true tuple event in the infinite multiplicative model. -/
def tupleStartEvent (L : ℕ) (x : ι → ℕ) : Set InfiniteSample :=
  {omega | ∀ i, StartEvent (infiniteValueBit omega) (x i) L}

omit [Fintype ι] in
theorem tupleSystem_eq_iff {M L : ℕ} (x : ι → ℕ) (omega : SampleSpace M) (hL : 0 < L) :
    tupleSystem M L x omega = tupleRhs L ↔ ∀ i, startAt omega (x i) L := by
  constructor
  · intro h i
    apply (startSystem_eq_startRhs_iff_startAt omega hL).mp
    funext j
    exact congrFun h (i,j)
  · intro h
    funext i
    exact congrFun ((startSystem_eq_startRhs_iff_startAt omega hL).mpr (h i.1)) i.2

omit [Fintype ι] in
theorem tupleStartEvent_eq_cylinder {M L : ℕ} (x : ι → ℕ) (hL : 0 < L)
    (hcut : ∀ i, x i + L ≤ M) :
    tupleStartEvent L x = affineCylinder (tupleSystem M L x) (tupleRhs L) := by
  ext omega
  rw [affineCylinder, Set.mem_setOf_eq, tupleSystem_eq_iff x _ hL]
  simp only [tupleStartEvent, Set.mem_setOf_eq, startAt_restrictToFinite_iff omega (hcut _)]

/-- Lemma 2.1 for every finite tuple, with no disjointness or compatibility premise. -/
theorem lemma_two_one {M L : ℕ} (x : ι → ℕ) (hL : 0 < L)
    (hcut : ∀ i, x i + L ≤ M) :
    infiniteRademacherMeasure.real (tupleStartEvent L x) =
      (relationEta (tupleSystem M L x) (tupleRhs L) : ℝ) *
        2 ^ relationRho (tupleSystem M L x) / 2 ^ (Fintype.card ι * L) ∧
    (2 : ℝ) ^ (Fintype.card ι * L) * infiniteRademacherMeasure.real (tupleStartEvent L x) =
      (relationSignedSum (tupleSystem M L x) (tupleRhs L) : ℝ) ∧
    |(2 : ℝ) ^ (Fintype.card ι * L) * infiniteRademacherMeasure.real (tupleStartEvent L x) - 1| ≤
      (2 : ℝ) ^ relationRho (tupleSystem M L x) - 1 := by
  classical
  rw [tupleStartEvent_eq_cylinder x hL hcut]
  simpa only [Fintype.card_prod, Fintype.card_fin] using
    And.intro (affine_probability_eq_eta (tupleSystem M L x) (tupleRhs L))
      (And.intro (affine_fourier_identity (tupleSystem M L x) (tupleRhs L))
        (affine_normalized_discrepancy_le (tupleSystem M L x) (tupleRhs L)))

end
end PaperC.V282.ClosureAlgebraStartTuple
