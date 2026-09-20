import PaperCPrel8.FiniteConditioning
import PaperCPrel8.PalmDeficit

/-! # Ordinary deletion cost after exact Palm mass cancellation -/
namespace PaperC.Prel8.PalmDeletionIdentity
open PaperC.ArratiaGoldsteinGordonInput PaperC.IndependentThinning
open PaperC.Prel8.FiniteConditioning
open scoped BigOperators
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P
variable {Ω Z : Type*} [Fintype Ω]

/-- Disjoint retained configurations sum to one ordinary deleted-event probability. -/
theorem sum_deleted_configurations (mu : FinitePMF Ω) (f : Ω → Z)
    (regular : Z → Prop) (outside : Ω → Prop) :
    (∑' z, if regular z then eventProbability mu (fun w => f w=z ∧ outside w) else 0)=
      eventProbability mu (fun w => regular (f w) ∧ outside w) := by
  have he (w : Ω) (z : Z) :
      (if regular z then (if f w=z ∧ outside w then mu.prob w else 0) else 0)=
      (if f w=z then (if regular (f w) ∧ outside w then mu.prob w else 0) else 0) := by
    by_cases h : f w=z
    · subst z; by_cases hr : regular (f w) <;> simp [hr]
    · simp [h]
  unfold eventProbability
  calc
    _ = ∑' z, ∑ w, (if regular z then (if f w=z ∧ outside w then mu.prob w else 0) else 0) := by
      apply tsum_congr
      intro z
      by_cases hz : regular z
      · simp only [hz,ite_true]
        apply Finset.sum_congr rfl
        intro w _
        by_cases h : f w=z ∧ outside w <;> simp [h]
      · simp [hz]
    _ = ∑' z, ∑ w, (if f w=z then (if regular (f w) ∧ outside w then mu.prob w else 0) else 0) := by
      apply tsum_congr
      intro z
      apply Finset.sum_congr rfl
      intro w _
      exact he w z
    _ = _ := by
      rw [Summable.tsum_finsetSum]
      · simp
        apply Finset.sum_congr rfl
        intro w _
        by_cases h : regular (f w) ∧ outside w <;> simp [h]
      · intro w _
        exact summable_of_ne_finset_zero (s := {f w}) (by intro z hz; simp only [Finset.mem_singleton] at hz; simp [Ne.symm hz])

/-- Removing the regularity restriction only increases the deleted-event cost. -/
theorem sum_deleted_le (mu : FinitePMF Ω) (f : Ω → Z)
    (regular : Z → Prop) (outside : Ω → Prop) :
    (∑' z, if regular z then eventProbability mu (fun w => f w=z ∧ outside w) else 0) ≤
      eventProbability mu outside := by
  rw [sum_deleted_configurations]
  unfold eventProbability
  apply Finset.sum_le_sum
  intro w _
  by_cases ho : outside w <;> by_cases hr : regular (f w) <;> simp [ho,hr,mu.nonneg w]

/-- Palm conditioning does not introduce an exponential deletion factor. -/
theorem palm_deleted_mass (mu : FinitePMF Ω) (f : Ω → Z) (outside : Ω → Prop)
    (presence : Z → Ω → Prop) (z : Z)
    (hp : 0 < eventProbability mu (presence z))
    (hpresence : ∀ w, f w=z → presence z w) :
    eventProbability mu (presence z)*
      (eventProbability (conditional mu (presence z) hp) (fun w => f w=z)-
       eventProbability (conditional mu (presence z) hp) (fun w => f w=z ∧ ¬outside w))=
      eventProbability mu (fun w => f w=z ∧ outside w) := by
  rw [probability_conditional,probability_conditional]
  have h1 : eventProbability mu (fun w => presence z w ∧ f w=z)=
      eventProbability mu (fun w => f w=z) := by
    unfold eventProbability
    apply Finset.sum_congr rfl
    intro w _
    by_cases h : f w=z
    · simp [h,hpresence w h]
    · simp [h]
  have h2 : eventProbability mu (fun w => presence z w ∧ (f w=z ∧ ¬outside w))=
      eventProbability mu (fun w => f w=z ∧ ¬outside w) := by
    unfold eventProbability
    apply Finset.sum_congr rfl
    intro w _
    by_cases h : f w=z
    · simp [h,hpresence w h]
    · simp [h]
  rw [h1,h2,← sub_div,mul_div_cancel₀ _ hp.ne']
  unfold eventProbability
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hf : f w=z <;> by_cases ho : outside w <;> simp [hf,ho]

end
end PaperC.Prel8.PalmDeletionIdentity
