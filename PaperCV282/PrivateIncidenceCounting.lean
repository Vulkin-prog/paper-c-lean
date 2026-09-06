import PaperCV282.PrivateIncidenceRank

/-! # Incidence surviving deletion of private rows

The surviving matrix inherits the simple-incidence hypotheses. Deleting a row
with at most one incidence loses at most one from the actual incidence total.
-/
namespace PaperC.V282.PrivateIncidenceCounting

open Matrix Finset SimpleIncidenceModel SimpleIncidenceRank PrivateIncidenceRank

noncomputable section

variable {R V : Type*} [Fintype R] [Fintype V] [DecidableEq R] [DecidableEq V]

omit [Fintype R] [DecidableEq R] [DecidableEq V] in
theorem rowSupport_deleteRows (H : Matrix R V F₂) (D : Finset R) (r : {r // r ∉ D}) :
    rowSupport (deleteRows H D) r = rowSupport H r.val := rfl

omit [Fintype V] [DecidableEq V] in
theorem columnSupport_deleteRows_le (H : Matrix R V F₂) (D : Finset R) (v : V) :
    (columnSupport (deleteRows H D) v).card ≤ (columnSupport H v).card := by
  classical
  let f : {r // r ∈ columnSupport (deleteRows H D) v} → {r // r ∈ columnSupport H v} :=
    fun r => ⟨r.val.val, (mem_columnSupport H r.val.val v).mpr
      ((mem_columnSupport (deleteRows H D) r.val v).mp r.property)⟩
  have hf : Function.Injective f := by
    intro r s hrs
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun a => a.val) hrs
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

omit [DecidableEq V] in
theorem incidenceMass_deleteRows_add_private (H : Matrix R V F₂) (D : Finset R) :
    incidenceMass (deleteRows H D) + (∑ r : D, (rowSupport H r.val).card) =
      incidenceMass H := by
  have h := Fintype.sum_subtype_add_sum_subtype (fun r => r ∈ D)
    (fun r => (rowSupport H r).card)
  unfold incidenceMass
  simp only [rowSupport_deleteRows]
  rw [Nat.add_comm]
  convert h using 1
  congr 1
  exact Finset.sum_congr (by ext; simp) (fun _ _ => rfl)

omit [DecidableEq V] in
theorem incidenceMass_le_deleted_add_private (H : Matrix R V F₂) (D : Finset R)
    (hprivate : ∀ r ∈ D, (rowSupport H r).card ≤ 1) :
    incidenceMass H ≤ incidenceMass (deleteRows H D) + D.card := by
  rw [← incidenceMass_deleteRows_add_private H D]
  apply Nat.add_le_add_left
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun (r : D) _ => hprivate r.val r.property)
  simpa using h

theorem deleted_incidence_le_rank (H : Matrix R V F₂) (D : Finset R) (K : ℕ)
    (hrow : ∀ r, (rowSupport H r).card ≤ 2)
    (hcol : ∀ v, (columnSupport H v).card ≤ K)
    (hsimple : ∀ r s, (rowSupport H r).card = 2 → rowSupport H r = rowSupport H s → r = s) :
    incidenceMass (deleteRows H D) ≤ (K + 1) * (deleteRows H D).rank := by
  apply lemma_e_two
  · intro r
    exact hrow r.val
  · intro v
    exact (columnSupport_deleteRows_le H D v).trans (hcol v)
  · intro r s hr hrs
    apply Subtype.ext
    exact hsimple r.val s.val hr hrs

theorem incidenceMass_le_private_add_deleted_rank (H : Matrix R V F₂) (D : Finset R) (K : ℕ)
    (hrow : ∀ r, (rowSupport H r).card ≤ 2)
    (hcol : ∀ v, (columnSupport H v).card ≤ K)
    (hsimple : ∀ r s, (rowSupport H r).card = 2 → rowSupport H r = rowSupport H s → r = s)
    (hprivate : ∀ r ∈ D, (rowSupport H r).card ≤ 1) :
    incidenceMass H ≤ D.card + (K + 1) * (deleteRows H D).rank := by
  have h := incidenceMass_le_deleted_add_private H D hprivate
  have hr := deleted_incidence_le_rank H D K hrow hcol hsimple
  omega

end
end PaperC.V282.PrivateIncidenceCounting
