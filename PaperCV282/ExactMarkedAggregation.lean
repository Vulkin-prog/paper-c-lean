import PaperCV282.ExactMarkedDependency

/-!
# Probability aggregation at the base threshold

Mutually exclusive excess/sign labels are summed before any probability
or arithmetic estimate. No cardinality of the mark set enters these bounds.
-/
namespace PaperC.V282.ExactMarkedAggregation

open ExactMarkedModel ExactMarkedDependency LabelledSupportGraph LabelledProcessCosts
open ConditionalStartProbability ArratiaGoldsteinGordonInput MixedLengthAffine
open ExactLengthDecomposition SectionTwelveMoments ConditionalAGGInstantiation
open scoped BigOperators

noncomputable section
local instance instDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- Disjoint alternatives included in an event have at most its probability. -/
theorem sum_exclusive_probability_le {κ Ω : Type*} [Fintype κ] [Fintype Ω]
    (μ : FinitePMF Ω) (P : κ → Ω → Prop) (R : Ω → Prop)
    (hunique : ∀ omega a b, P a omega → P b omega → a = b)
    (hsub : ∀ a omega, P a omega → R omega) :
    (∑ a, eventProbability μ (P a)) ≤ eventProbability μ R := by
  unfold eventProbability
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro omega _
  by_cases hex : ∃ a, P a omega
  · obtain ⟨a,ha⟩ := hex
    rw [Finset.sum_eq_single a]
    · simp [ha,hsub a omega ha]
    · intro b _ hba
      have hb : ¬P b omega := fun hb => hba (hunique omega b a hb ha)
      simp [hb]
    · simp
  · push Not at hex
    simp only [hex,if_false,Finset.sum_const_zero]
    split_ifs <;> first | exact μ.nonneg omega | exact le_rfl

/-- Signed probabilities at one site sum to at most the base start probability. -/
theorem sum_signed_probability_le_base {Ω : Type*} [Fintype Ω]
    (μ : FinitePMF Ω) (g : Ω → ℕ → F₂) (x L E : ℕ) (hL : 1 ≤ L) :
    (∑ a : Fin (E+1) × F₂, eventProbability μ
      (fun omega => SignedExactMark (g omega) x L a.1.val a.2)) ≤
        eventProbability μ (fun omega => StartEvent (g omega) x L) := by
  apply sum_exclusive_probability_le
  · intro omega a b ha hb
    obtain ⟨he,hs⟩ := signedExactMark_unique hL ha hb
    exact Prod.ext (Fin.ext he) hs
  · intro a omega ha
    exact exactLengthEvent_start ha.1

/-- The pair bound removes both labels before estimating the base two-start event. -/
theorem sum_signed_joint_probability_le_base {Ω : Type*} [Fintype Ω]
    (μ : FinitePMF Ω) (g : Ω → ℕ → F₂) (x y L E : ℕ) (hL : 1 ≤ L) :
    (∑ a : Fin (E+1) × F₂, ∑ b : Fin (E+1) × F₂, eventProbability μ
      (fun omega => SignedExactMark (g omega) x L a.1.val a.2 ∧
        SignedExactMark (g omega) y L b.1.val b.2)) ≤
        eventProbability μ (fun omega => StartEvent (g omega) x L ∧ StartEvent (g omega) y L) := by
  rw [← Fintype.sum_prod_type (fun ab : (Fin (E+1) × F₂) × (Fin (E+1) × F₂) =>
    eventProbability μ (fun omega => SignedExactMark (g omega) x L ab.1.1.val ab.1.2 ∧
      SignedExactMark (g omega) y L ab.2.1.val ab.2.2))]
  apply sum_exclusive_probability_le
  · intro omega a b ha hb
    obtain ⟨hex,hsx⟩ := signedExactMark_unique hL ha.1 hb.1
    obtain ⟨hey,hsy⟩ := signedExactMark_unique hL ha.2 hb.2
    exact Prod.ext (Prod.ext (Fin.ext hex) hsx) (Prod.ext (Fin.ext hey) hsy)
  · intro a omega ha
    exact ⟨exactLengthEvent_start ha.1.1,exactLengthEvent_start ha.2.1⟩

/-- The same probability bound applies to any conditional cylinder. -/
theorem sum_conditioned_signed_probability_le_base (C L E Y x : ℕ)
    (sigma : SmallSample C Y) (hL : 1 ≤ L) :
    (∑ a : Fin (E+1) × F₂, eventProbability (largeUniformPMF C Y)
      (fun eta => conditionedSignedAt C L E Y sigma x a eta = true)) ≤
        eventProbability (largeUniformPMF C Y)
          (fun eta => StartEvent (valueBit (assemble C Y sigma eta)) x L) := by
  simp only [conditionedSignedAt,signedAt,decide_eq_true_eq]
  exact sum_signed_probability_le_base _ _ x L E hL

theorem sum_conditioned_signed_joint_probability_le_base (C L E Y x y : ℕ)
    (sigma : SmallSample C Y) (hL : 1 ≤ L) :
    (∑ a : Fin (E+1) × F₂, ∑ b : Fin (E+1) × F₂, eventProbability (largeUniformPMF C Y)
      (fun eta => conditionedSignedAt C L E Y sigma x a eta = true ∧
        conditionedSignedAt C L E Y sigma y b eta = true)) ≤
        eventProbability (largeUniformPMF C Y)
          (fun eta => StartEvent (valueBit (assemble C Y sigma eta)) x L ∧
            StartEvent (valueBit (assemble C Y sigma eta)) y L) := by
  simp only [conditionedSignedAt,signedAt,decide_eq_true_eq]
  exact sum_signed_joint_probability_le_base _ _ x y L E hL

end
end PaperC.V282.ExactMarkedAggregation
