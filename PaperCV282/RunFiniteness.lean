import PaperCV282.ExactMarkedModel
import PaperC.Probability.InfiniteExactLengthDecomposition

/-! # Actual run termination and the complete signed exact-mark decomposition -/
namespace PaperC.V282.RunFiniteness

open MeasureTheory InfiniteRademacher InfiniteExactLengthDecomposition
open ExactLengthDecomposition ExactMarkedModel MixedLengthAffine
open scoped BigOperators

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- The genuine source has no infinite rightward run, simultaneously at every site. -/
theorem ae_all_runs_end :
    ∀ᵐ omega ∂infiniteRademacherMeasure, ∀ x : ℕ, 2 ≤ x →
      ∃ n : ℕ, x ≤ n ∧ infiniteValueBit omega n ≠ infiniteValueBit omega x :=
  ae_tailChangesAt_infiniteValueBit

/-- After termination, a start activates exactly one excess and one actual sign. -/
theorem start_iff_unique_signed_exact {g : ℕ → F₂} {x L : ℕ}
    (hL : 1 ≤ L) (hchange : TailChangesAt g x) :
    StartEvent g x L ↔ ∃! a : ℕ × F₂, SignedExactMark g x L a.1 a.2 := by
  constructor
  · intro hs
    obtain ⟨e,he⟩ := exists_exactLengthEvent_of_start_of_tailChangesAt hs hchange
    refine ⟨(e,g x),⟨he,rfl⟩,?_⟩
    intro b hb
    obtain ⟨heq,hsign⟩ := signedExactMark_unique hL hb ⟨he,rfl⟩
    exact Prod.ext heq hsign
  · rintro ⟨a,ha,_⟩
    exact exactLengthEvent_start ha.1

/-- Equation (5.11), with both signs retained until after summation. -/
theorem sum_signed_exact_eq_start_of_tail_changes {g : ℕ → F₂} {x L : ℕ}
    (hL : 1 ≤ L) (hchange : TailChangesAt g x) :
    (∑' a : ℕ × F₂, signedMarkValue g x L a.1 a.2)=baseStartValue g x L := by
  by_cases hs : StartEvent g x L
  · obtain ⟨a,ha,hu⟩ := (start_iff_unique_signed_exact hL hchange).mp hs
    rw [tsum_eq_single a]
    · simp [signedMarkValue,baseStartValue,hs,ha]
    · intro b hb
      have hn : ¬SignedExactMark g x L b.1 b.2 := fun hh => hb (hu b hh)
      simp [signedMarkValue,hn]
  · have hn (a : ℕ × F₂) : ¬SignedExactMark g x L a.1 a.2 :=
      fun h => hs (exactLengthEvent_start h.1)
    simp [signedMarkValue,baseStartValue,hs,hn]

/-- The complete identity holds almost surely for every positive length and every start x≥2. -/
theorem ae_sum_signed_exact_eq_start :
    ∀ᵐ omega ∂infiniteRademacherMeasure, ∀ x : ℕ, 2 ≤ x → ∀ L : ℕ, 1 ≤ L →
      (∑' a : ℕ × F₂, signedMarkValue (infiniteValueBit omega) x L a.1 a.2)=
        baseStartValue (infiniteValueBit omega) x L := by
  filter_upwards [ae_all_runs_end] with omega homega
  intro x hx L hL
  exact sum_signed_exact_eq_start_of_tail_changes hL (homega x hx)

end
end PaperC.V282.RunFiniteness
