import PaperC.Affine.TwoStartSystem
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The range of the complete start boundary

The complete boundary of the `L` rows of one start is precisely the
codimension-one space of vertex vectors having even total parity.  This is
the linear-algebra interface needed to turn even collections of rational
channel units into row relations in Lemma 5.1.
-/

namespace PaperC
namespace Affine

open scoped BigOperators

noncomputable section

/-- Sum of all coordinates of a complete start-boundary vector. -/
def startVertexSum (L : ℕ) :
    (Fin (L + 1) → F₂) →ₗ[F₂] F₂ where
  toFun w := ∑ v : Fin (L + 1), w v
  map_add' w z := by
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c w := by
    change (∑ v : Fin (L + 1), c * w v) =
      c * ∑ v : Fin (L + 1), w v
    rw [Finset.mul_sum]

@[simp]
theorem startVertexSum_apply
    (L : ℕ) (w : Fin (L + 1) → F₂) :
    startVertexSum L w = ∑ v : Fin (L + 1), w v :=
  rfl

/-- Every incidence column has even total parity. -/
theorem sum_startIncidenceColumn_eq_zero
    {L : ℕ} (i : Fin L) :
    ∑ v : Fin (L + 1), startIncidenceColumn i v = 0 := by
  classical
  unfold startIncidenceColumn
  simp only [Pi.add_apply]
  rw [Finset.sum_add_distrib]
  simp

/-- Every complete boundary has even total parity. -/
theorem startVertexSum_startCompleteBoundary_eq_zero
    {L : ℕ} (u : Fin L → F₂) :
    startVertexSum L (startCompleteBoundary L u) = 0 := by
  classical
  simp only [startVertexSum_apply, startCompleteBoundary_apply]
  rw [Finset.sum_comm]
  calc
    (∑ i : Fin L, ∑ v : Fin (L + 1),
        u i * startIncidenceColumn i v) =
        ∑ i : Fin L,
          u i * (∑ v : Fin (L + 1),
            startIncidenceColumn i v) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i _hi
      rw [sum_startIncidenceColumn_eq_zero, mul_zero]

/-- The coordinate-sum map is onto because the root coordinate is free. -/
theorem startVertexSum_surjective (L : ℕ) :
    Function.Surjective (startVertexSum L) := by
  intro c
  let w : Fin (L + 1) → F₂ :=
    Pi.single (startRootVertex L) c
  refine ⟨w, ?_⟩
  simp [startVertexSum, w]

/--
The range of the complete boundary is exactly the even-parity hyperplane.
-/
theorem range_startCompleteBoundary_eq_ker_startVertexSum
    (L : ℕ) :
    LinearMap.range (startCompleteBoundary L) =
      LinearMap.ker (startVertexSum L) := by
  have hle :
      LinearMap.range (startCompleteBoundary L) ≤
        LinearMap.ker (startVertexSum L) := by
    intro w hw
    obtain ⟨u, rfl⟩ := hw
    exact startVertexSum_startCompleteBoundary_eq_zero u
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hrangeBoundary :
      Module.finrank F₂
          (LinearMap.range (startCompleteBoundary L)) = L := by
    rw [LinearMap.finrank_range_of_inj
      (startCompleteBoundary_injective L)]
    simp [Module.finrank_pi]
  have hnullity :=
    LinearMap.finrank_range_add_finrank_ker
      (startVertexSum L)
  have hrange :
      LinearMap.range (startVertexSum L) = ⊤ :=
    LinearMap.range_eq_top.mpr (startVertexSum_surjective L)
  rw [hrange] at hnullity
  simp [Module.finrank_pi] at hnullity
  have hkerSum :
      Module.finrank F₂
          (LinearMap.ker (startVertexSum L)) = L := by
    omega
  exact hrangeBoundary.trans hkerSum.symm

/-- The complete boundary with codomain restricted to even vertex vectors. -/
def startBoundaryToEven (L : ℕ) :
    (Fin L → F₂) →ₗ[F₂] LinearMap.ker (startVertexSum L) :=
  (startCompleteBoundary L).codRestrict
    (LinearMap.ker (startVertexSum L))
    (fun u ↦ startVertexSum_startCompleteBoundary_eq_zero u)

theorem startBoundaryToEven_injective (L : ℕ) :
    Function.Injective (startBoundaryToEven L) := by
  intro u v huv
  apply startCompleteBoundary_injective L
  exact congrArg Subtype.val huv

theorem startBoundaryToEven_surjective (L : ℕ) :
    Function.Surjective (startBoundaryToEven L) := by
  intro w
  have hwRange :
      (w : Fin (L + 1) → F₂) ∈
        LinearMap.range (startCompleteBoundary L) := by
    rw [range_startCompleteBoundary_eq_ker_startVertexSum L]
    exact w.property
  obtain ⟨u, hu⟩ := hwRange
  refine ⟨u, ?_⟩
  apply Subtype.ext
  exact hu

/--
Canonical linear equivalence between row coefficients and even complete
boundaries.
-/
noncomputable def startBoundaryEquivEven (L : ℕ) :
    (Fin L → F₂) ≃ₗ[F₂] LinearMap.ker (startVertexSum L) :=
  LinearEquiv.ofBijective (startBoundaryToEven L)
    ⟨startBoundaryToEven_injective L,
      startBoundaryToEven_surjective L⟩

@[simp]
theorem startBoundaryEquivEven_apply_coe
    (L : ℕ) (u : Fin L → F₂) :
    ((startBoundaryEquivEven L u :
      LinearMap.ker (startVertexSum L)) :
        Fin (L + 1) → F₂) =
      startCompleteBoundary L u :=
  rfl

/--
An even complete-boundary vector has a unique row-coefficient preimage.
-/
theorem existsUnique_startCompleteBoundary_eq
    {L : ℕ} {w : Fin (L + 1) → F₂}
    (hw : startVertexSum L w = 0) :
    ∃! u : Fin L → F₂, startCompleteBoundary L u = w := by
  have hwKer : w ∈ LinearMap.ker (startVertexSum L) := hw
  rw [← range_startCompleteBoundary_eq_ker_startVertexSum L] at hwKer
  obtain ⟨u, hu⟩ := hwKer
  refine ⟨u, hu, ?_⟩
  intro v hv
  exact startCompleteBoundary_injective L (hv.trans hu.symm)

end

end Affine
end PaperC
