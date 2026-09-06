import PaperCV282.PrivateIncidenceCounting
import Mathlib.Data.Real.Basic

/-! # Private rank plus surviving simple incidences

This is the finite quotient assembly used in companion E.4. The count is the
number of nonzero entries, and the subtraction records at most one lost
incidence per private row. No rank inequality is assumed.
-/
namespace PaperC.V282.PrivateIncidenceBudget

open Matrix Finset SimpleIncidenceModel PrivateIncidenceRank PrivateIncidenceCounting

noncomputable section

variable {R C V : Type*} [Fintype R] [Fintype C] [Fintype V]
  [DecidableEq R] [DecidableEq V]

theorem private_incidence_rank_budget (A : Matrix R C F₂) (D : Finset R)
    (select : V → C) (K : ℕ)
    (hprivate : ∀ r ∈ D, Pi.single r (1 : F₂) ∈ LinearMap.range A.mulVecLin)
    (hrow : ∀ r, (rowSupport (A.submatrix id select) r).card ≤ 2)
    (hcol : ∀ v, (columnSupport (A.submatrix id select) v).card ≤ K)
    (hsimple : ∀ r s, (rowSupport (A.submatrix id select) r).card = 2 →
      rowSupport (A.submatrix id select) r = rowSupport (A.submatrix id select) s → r = s)
    (hloss : ∀ r ∈ D, (rowSupport (A.submatrix id select) r).card ≤ 1) :
    (K + 1) * D.card + (incidenceMass (A.submatrix id select) - D.card) ≤
      (K + 1) * A.rank := by
  have hr := private_add_selected_rank_le A D select hprivate
  have he := incidenceMass_le_private_add_deleted_rank (A.submatrix id select) D K
    hrow hcol hsimple hloss
  have hs : incidenceMass (A.submatrix id select) - D.card ≤
      (K + 1) * (deleteRows (A.submatrix id select) D).rank := by omega
  calc
    _ ≤ (K + 1) * D.card + (K + 1) * (deleteRows (A.submatrix id select) D).rank :=
      Nat.add_le_add_left hs _
    _ = (K + 1) * (D.card + (deleteRows (A.submatrix id select) D).rank) := by ring
    _ ≤ _ := Nat.mul_le_mul_left (K + 1) hr

theorem private_incidence_rank_real (A : Matrix R C F₂) (D : Finset R)
    (select : V → C) (K : ℕ)
    (hprivate : ∀ r ∈ D, Pi.single r (1 : F₂) ∈ LinearMap.range A.mulVecLin)
    (hrow : ∀ r, (rowSupport (A.submatrix id select) r).card ≤ 2)
    (hcol : ∀ v, (columnSupport (A.submatrix id select) v).card ≤ K)
    (hsimple : ∀ r s, (rowSupport (A.submatrix id select) r).card = 2 →
      rowSupport (A.submatrix id select) r = rowSupport (A.submatrix id select) s → r = s)
    (hloss : ∀ r ∈ D, (rowSupport (A.submatrix id select) r).card ≤ 1) :
    (D.card : ℝ) + (incidenceMass (A.submatrix id select) - D.card : ℕ) / (K + 1 : ℝ) ≤
      (A.rank : ℝ) := by
  have h := private_incidence_rank_budget A D select K hprivate hrow hcol hsimple hloss
  have hc : ((K : ℝ) + 1) * D.card +
      (incidenceMass (A.submatrix id select) - D.card : ℕ) ≤ ((K : ℝ) + 1) * A.rank := by
    exact_mod_cast h
  have hk : (0 : ℝ) < K + 1 := by positivity
  calc
    _ = (((K : ℝ) + 1) * D.card +
        (incidenceMass (A.submatrix id select) - D.card : ℕ)) / (K + 1) := by
      field_simp
    _ ≤ _ := (div_le_iff₀ hk).mpr (by nlinarith [hc])

/-- The exact K=11 denominator, with the incidence loss truncated at zero. -/
theorem private_incidence_rank_twelfth (A : Matrix R C F₂) (D : Finset R)
    (select : V → C)
    (hprivate : ∀ r ∈ D, Pi.single r (1 : F₂) ∈ LinearMap.range A.mulVecLin)
    (hrow : ∀ r, (rowSupport (A.submatrix id select) r).card ≤ 2)
    (hcol : ∀ v, (columnSupport (A.submatrix id select) v).card ≤ 11)
    (hsimple : ∀ r s, (rowSupport (A.submatrix id select) r).card = 2 →
      rowSupport (A.submatrix id select) r = rowSupport (A.submatrix id select) s → r = s)
    (hloss : ∀ r ∈ D, (rowSupport (A.submatrix id select) r).card ≤ 1) :
    (D.card : ℝ) + (incidenceMass (A.submatrix id select) - D.card : ℕ) / 12 ≤
      (A.rank : ℝ) := by
  convert private_incidence_rank_real A D select 11 hprivate hrow hcol hsimple hloss using 1
  norm_num

end
end PaperC.V282.PrivateIncidenceBudget
