import PaperCV282.SimpleIncidenceRank

/-! # Private coordinates and the remaining matrix rank

Coordinate vectors in the column image survive as independent private directions.
Projection to the other rows computes the quotient image exactly, without any
disjointness assumption on the other columns.
-/
namespace PaperC.V282.PrivateIncidenceRank

open Matrix Finset

noncomputable section

local instance instPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {R C V : Type*} [Fintype R] [Fintype C] [Fintype V] [DecidableEq R]

def deleteRows (A : Matrix R C F₂) (D : Finset R) : Matrix {r // r ∉ D} C F₂ :=
  A.submatrix Subtype.val id

def rowProjection (D : Finset R) : (R → F₂) →ₗ[F₂] ({r // r ∉ D} → F₂) :=
  LinearMap.funLeft F₂ F₂ Subtype.val

omit [Fintype R] [Fintype C] [Fintype V] in
theorem rowProjection_surjective (D : Finset R) : Function.Surjective (rowProjection D) := by
  intro f
  refine ⟨fun r => if h : r ∈ D then 0 else f ⟨r,h⟩, ?_⟩
  funext r
  simp [rowProjection, r.property]

omit [Fintype C] [Fintype V] in
theorem finrank_ker_rowProjection (D : Finset R) :
    Module.finrank F₂ (LinearMap.ker (rowProjection D)) = D.card := by
  have h := LinearMap.finrank_range_add_finrank_ker (K := F₂) (rowProjection D)
  rw [LinearMap.range_eq_top.mpr (rowProjection_surjective D)] at h
  simp only [finrank_top, Module.finrank_pi, Fintype.card_subtype_compl,
    Fintype.card_coe] at h
  have hD : D.card ≤ Fintype.card R := Finset.card_le_univ D
  omega

omit [Fintype R] [Fintype V] [DecidableEq R] in
theorem mulVecLin_deleteRows (A : Matrix R C F₂) (D : Finset R) :
    (deleteRows A D).mulVecLin = (rowProjection D).comp A.mulVecLin := by
  ext f r
  rfl

omit [Fintype R] [Fintype C] [Fintype V] in
theorem ker_rowProjection_le_of_private (D : Finset R) (S : Submodule F₂ (R → F₂))
    (hprivate : ∀ r ∈ D, Pi.single r (1 : F₂) ∈ S) :
    LinearMap.ker (rowProjection D) ≤ S := by
  intro f hf
  have hzero : ∀ r, r ∉ D → f r = 0 := by
    intro r hr
    exact congrFun (LinearMap.mem_ker.mp hf) ⟨r,hr⟩
  have hexpand : f = ∑ r ∈ D, f r • Pi.single r (1 : F₂) := by
    funext r
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hr : r ∈ D
    · rw [Finset.sum_eq_single r]
      · simp
      · intro s hs hsr
        simp [hsr]
      · exact fun h => (h hr).elim
    · rw [hzero r hr]
      symm
      apply Finset.sum_eq_zero
      intro s hs
      have hsr : s ≠ r := fun h => hr (h ▸ hs)
      simp [hsr]
  rw [hexpand]
  exact Submodule.sum_mem S (fun r hr => S.smul_mem (f r) (hprivate r hr))

omit [Fintype V] in
/-- The quotient by genuinely private coordinate directions loses exactly their number. -/
theorem rank_eq_private_add_deleted (A : Matrix R C F₂) (D : Finset R)
    (hprivate : ∀ r ∈ D, Pi.single r (1 : F₂) ∈ LinearMap.range A.mulVecLin) :
    A.rank = D.card + (deleteRows A D).rank := by
  let S := LinearMap.range A.mulVecLin
  let f := (rowProjection D).comp S.subtype
  have hker : LinearMap.ker (rowProjection D) ≤ S :=
    ker_rowProjection_le_of_private D S hprivate
  have hk : Module.finrank F₂ (LinearMap.ker f) = D.card := by
    change Module.finrank F₂ (LinearMap.ker ((rowProjection D).comp S.subtype)) = _
    rw [LinearMap.ker_comp]
    exact (Submodule.comapSubtypeEquivOfLe hker).finrank_eq.trans (finrank_ker_rowProjection D)
  have hr : LinearMap.range f = LinearMap.range (deleteRows A D).mulVecLin := by
    change LinearMap.range ((rowProjection D).comp S.subtype) = _
    rw [mulVecLin_deleteRows, LinearMap.range_comp, LinearMap.range_comp, Submodule.range_subtype]
  have hn := LinearMap.finrank_range_add_finrank_ker (K := F₂) f
  rw [hr, hk] at hn
  exact (Nat.add_comm _ _).trans hn |>.symm

omit [Fintype R] [Fintype V] in
theorem private_column_mem_range (A : Matrix R C F₂) (r : R) (c : C)
    (hc : A.col c = Pi.single r (1 : F₂)) :
    Pi.single r (1 : F₂) ∈ LinearMap.range A.mulVecLin := by
  classical
  refine ⟨Pi.single c 1, ?_⟩
  simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_single_one] using hc

omit [Fintype V] in
theorem rank_eq_of_private_columns (A : Matrix R C F₂) (D : Finset R)
    (pivot : {r // r ∈ D} → C)
    (hpivot : ∀ r, A.col (pivot r) = Pi.single r.val (1 : F₂)) :
    A.rank = D.card + (deleteRows A D).rank := by
  apply rank_eq_private_add_deleted
  intro r hr
  exact private_column_mem_range A r (pivot ⟨r,hr⟩) (hpivot ⟨r,hr⟩)

theorem private_add_selected_rank_le (A : Matrix R C F₂) (D : Finset R)
    (select : V → C)
    (hprivate : ∀ r ∈ D, Pi.single r (1 : F₂) ∈ LinearMap.range A.mulVecLin) :
    D.card + (deleteRows (A.submatrix id select) D).rank ≤ A.rank := by
  rw [rank_eq_private_add_deleted A D hprivate]
  apply Nat.add_le_add_left
  exact Matrix.rank_submatrix_le (deleteRows A D) id select

end
end PaperC.V282.PrivateIncidenceRank
