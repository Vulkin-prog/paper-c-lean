import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity

/-!
# Finite probability mass functions

All events in a fixed dyadic block are cylindrical.  This small finite API is
therefore sufficient for the algebraic and conditioning stages of the paper.
The unrestricted product law and its exact projection back to these finite
cylinders are supplied later by `InfiniteRademacher` and
`InfiniteCylinderTransfer`.
-/

open scoped BigOperators

namespace PaperC

/-- A probability mass function on a finite type, represented without any
measure-theoretic overhead. -/
structure FinitePMF (α : Type*) [Fintype α] where
  prob : α → ℝ
  nonneg : ∀ a, 0 ≤ prob a
  sum_prob : ∑ a, prob a = 1

namespace FinitePMF

variable {α : Type*} [Fintype α]

/-- The uniform probability mass function on a nonempty finite type. -/
noncomputable def uniform (α : Type*) [Fintype α] [Nonempty α] :
    FinitePMF α where
  prob _ := (Fintype.card α : ℝ)⁻¹
  nonneg _ := by positivity
  sum_prob := by
    classical
    simp [Fintype.card_ne_zero]

@[simp]
theorem uniform_prob (α : Type*) [Fintype α] [Nonempty α] (a : α) :
    (uniform α).prob a = (Fintype.card α : ℝ)⁻¹ :=
  rfl

/-- Total variation distance on a finite state space, in its half-`L¹`
form. -/
noncomputable def tvDist (μ ν : FinitePMF α) : ℝ :=
  (2 : ℝ)⁻¹ * ∑ a, |μ.prob a - ν.prob a|

theorem tvDist_nonneg (μ ν : FinitePMF α) : 0 ≤ tvDist μ ν := by
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem tvDist_self (μ : FinitePMF α) : tvDist μ μ = 0 := by
  simp [tvDist]

theorem tvDist_comm (μ ν : FinitePMF α) : tvDist μ ν = tvDist ν μ := by
  simp only [tvDist, abs_sub_comm]

end FinitePMF

end PaperC
