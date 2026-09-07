import PaperCV282.SimpleIncidenceKernel
import PaperCV282.SimpleIncidenceCounting

/-! # Companion Lemma E.2: simple incidence rank

The incidence count of each genuine component is controlled using both its
column-weight bound and the injective other-endpoint map. Rank-nullity then
proves the stated matrix inequality, including all zero and pinned components.
-/
namespace PaperC.V282.SimpleIncidenceRank

open Matrix Finset SimpleGraph PinnedGraphResolution
open SimpleIncidenceModel SimpleIncidenceKernel SimpleIncidenceCounting

noncomputable section

variable {R V : Type*} [Fintype R] [Fintype V] [DecidableEq V]

local instance instDecidableComponentPinned (H : Matrix R V F₂) :
    DecidablePred (ComponentPinned (incidenceGraph H) (pinnedColumns H)) := Classical.decPred _

/-- The two elementary incidence bounds give the exact cost of one free component. -/
theorem unpinned_component_numeric_bound (mass r K : ℕ) (hr : 0 < r)
    (hdegree : mass ≤ K * r) (hsimple : mass ≤ r * (r - 1)) :
    mass + (K + 1) ≤ (K + 1) * r := by
  by_cases hsmall : r ≤ K + 1
  · have hmul := Nat.mul_le_mul_right (r - 1) hsmall
    have hpred : r - 1 + 1 = r := Nat.sub_add_cancel (by omega)
    nlinarith
  · nlinarith

/-- A pinned component costs its full size; an unpinned component costs size minus one. -/
theorem component_mass_budget (H : Matrix R V F₂) (K : ℕ)
    (hrow : ∀ r, (rowSupport H r).card ≤ 2)
    (hcol : ∀ v, (columnSupport H v).card ≤ K)
    (hsimple : ∀ r s, (rowSupport H r).card = 2 → rowSupport H r = rowSupport H s → r = s)
    (c : (incidenceGraph H).ConnectedComponent) :
    componentMass H c + (K + 1) *
      (if ComponentPinned (incidenceGraph H) (pinnedColumns H) c then 0 else 1) ≤
      (K + 1) * Fintype.card c.supp := by
  have hd := componentMass_le_degree H K hcol c
  by_cases hc : ComponentPinned (incidenceGraph H) (pinnedColumns H) c
  · simp only [if_pos hc, Nat.mul_zero, Nat.add_zero]
    nlinarith
  · simp only [if_neg hc, Nat.mul_one]
    have hnonempty := ConnectedComponent.nonempty_supp c
    have hr : 0 < Fintype.card c.supp :=
      Fintype.card_pos_iff.mpr ⟨⟨hnonempty.some,hnonempty.some_mem⟩⟩
    exact unpinned_component_numeric_bound _ _ K hr hd (componentMass_le_simple H hrow hsimple c hc)

/-- Summing the exact zero-or-one component nullities counts the true free components. -/
theorem sum_unpinned_indicator (H : Matrix R V F₂) :
    (∑ c : (incidenceGraph H).ConnectedComponent,
      if ComponentPinned (incidenceGraph H) (pinnedColumns H) c then 0 else 1) =
      Fintype.card (UnpinnedComponent (incidenceGraph H) (pinnedColumns H)) := by
  classical
  rw [card_unpinnedComponents]
  unfold unpinnedComponents
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : ComponentPinned (incidenceGraph H) (pinnedColumns H) c <;> simp [hc]

/-- The component budgets add without discarding zero columns or repeated pins. -/
theorem incidenceMass_add_nullity_le (H : Matrix R V F₂) (K : ℕ)
    (hrow : ∀ r, (rowSupport H r).card ≤ 2)
    (hcol : ∀ v, (columnSupport H v).card ≤ K)
    (hsimple : ∀ r s, (rowSupport H r).card = 2 → rowSupport H r = rowSupport H s → r = s) :
    incidenceMass H + (K + 1) *
      Fintype.card (UnpinnedComponent (incidenceGraph H) (pinnedColumns H)) ≤
      (K + 1) * Fintype.card V := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun c _ => component_mass_budget H K hrow hcol hsimple c)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_componentMass, sum_unpinned_indicator,
    ← Finset.mul_sum, sum_card_component_support] at h
  exact h

/-- Companion Lemma E.2: E ≤ (K+1) rank H for the actual binary matrix. -/
theorem lemma_e_two (H : Matrix R V F₂) (K : ℕ)
    (hrow : ∀ r, (rowSupport H r).card ≤ 2)
    (hcol : ∀ v, (columnSupport H v).card ≤ K)
    (hsimple : ∀ r s, (rowSupport H r).card = 2 → rowSupport H r = rowSupport H s → r = s) :
    incidenceMass H ≤ (K + 1) * H.rank := by
  have hcount := incidenceMass_add_nullity_le H K hrow hcol hsimple
  have hrank := rank_add_unpinned_eq_card H hrow
  nlinarith

end
end PaperC.V282.SimpleIncidenceRank
