import PaperCV282.SignedMarkedSeparatedRelations
import PaperCV282.SignedDirectionalFactors

/-!
# Relative exact-mark probabilities after summing signs at fixed excesses

The mixed relative rows inject into the Q-row start system. Signs are summed
only at fixed excesses; no sum over excesses is folded into a base event.
-/
namespace PaperC.V282.UnsignedMarkedRelations

open Affine MixedLengthAffine ExactLengthDecomposition ExactMarkedModel ExactMarkedDependency
open ConditionalStartProbability ArratiaGoldsteinGordonInput ConditionalAGGInstantiation
open ConditionalAGGAverage SectionThirteenCouplings DictionaryMarginalCap
open SectionThirteenFiniteBound
open SignedDirectionalFactors DirectionalHessian
open scoped BigOperators NNReal

noncomputable section

local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- The two sign sums recover exactly the actual unsigned joint event. -/
theorem sum_signed_joint_eq_exact {Ω : Type*} [Fintype Ω]
    (mu : FinitePMF Ω) (g : Ω → ℕ → F₂) (x y L e f : ℕ) :
    (∑ s : F₂, ∑ t : F₂, eventProbability mu (fun omega =>
      SignedExactMark (g omega) x L e s ∧ SignedExactMark (g omega) y L f t)) =
    eventProbability mu (fun omega =>
      ExactLengthEvent (g omega) x (excessRowCount L e) ∧
      ExactLengthEvent (g omega) y (excessRowCount L f)) := by
  rw [← Fintype.sum_prod_type (fun a : F₂ × F₂ => eventProbability mu (fun omega =>
    SignedExactMark (g omega) x L e a.1 ∧ SignedExactMark (g omega) y L f a.2))]
  unfold eventProbability
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro omega _
  rw [Finset.sum_eq_single (g omega x,g omega y)]
  · simp [SignedExactMark]
  · intro a _ ha
    have hn : ¬(g omega x=a.1 ∧ g omega y=a.2) := by
      intro h
      exact ha (Prod.ext h.1.symm h.2.symm)
    simp only [SignedExactMark]
    split_ifs with h
    · exact (hn ⟨h.1.2,h.2.2⟩).elim
    · exact if_neg h
  · simp

theorem exact_joint_probability_le_relative_weight {C x y L E e f : ℕ}
    (hL : 1≤L) (he : e≤E) (hf : f≤E) :
    eventProbability (fullUniformPMF C) (fun omega =>
      ExactLengthEvent (valueBit omega) x (excessRowCount L e) ∧
      ExactLengthEvent (valueBit omega) y (excessRowCount L f)) ≤
      (exactMarkRate L e : ℝ)*(exactMarkRate L f : ℝ)*
        (2 : ℝ)^relationRho (twoStartSystem C x y (L+E+1)) := by
  have heq : eventProbability (fullUniformPMF C) (fun omega =>
      ExactLengthEvent (valueBit omega) x (excessRowCount L e) ∧
      ExactLengthEvent (valueBit omega) y (excessRowCount L f)) =
      (uniformSolutionProbability
        (mixedLengthSystem C x y (excessRowCount L e) (excessRowCount L f))
        (mixedLengthRhs (excessRowCount L e) (excessRowCount L f)) : ℝ) := by
    rw [← mixedExactLengthProbability_eq_uniformSolutionProbability C x y _ _
      (by unfold excessRowCount;omega) (by unfold excessRowCount;omega)]
    rw [eventProbability_fullUniformPMF_eq,finiteUniformProbability_eq_uniformEventProbability]
    rfl
  rw [heq]
  have hp := affine_probability_le_relation_weight
    (mixedLengthSystem C x y (excessRowCount L e) (excessRowCount L f))
    (mixedLengthRhs (excessRowCount L e) (excessRowCount L f))
  have hr := mixedExcess_relationRho_le_common (M := C) (x := x) (y := y) (L := L) he hf
  have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤2) hr
  apply hp.trans
  simp only [Fintype.card_sum,Fintype.card_fin]
  apply (div_le_div_of_nonneg_right hpow (by positivity)).trans_eq
  simp only [excessRowCount,exactMarkRate_coe,pow_add]
  ring_nf
  rfl

/-- The estimate is averaged over actual prime atoms before any relative-rank bound. -/
theorem average_exact_joint_probability_le_relative_weight {C x y L E Y e f : ℕ}
    (hL : 1≤L) (he : e≤E) (hf : f≤E) :
    finiteUniformAverage (fun sigma : SmallSample C Y =>
      eventProbability (largeUniformPMF C Y) (fun eta =>
        ExactLengthEvent (valueBit (assemble C Y sigma eta)) x (excessRowCount L e) ∧
        ExactLengthEvent (valueBit (assemble C Y sigma eta)) y (excessRowCount L f))) ≤
      (exactMarkRate L e : ℝ)*(exactMarkRate L f : ℝ)*
        (2 : ℝ)^relationRho (twoStartSystem C x y (L+E+1)) := by
  rw [finiteUniformAverage_largeEventProbability_eq_full C Y (fun omega =>
    ExactLengthEvent (valueBit omega) x (excessRowCount L e) ∧
    ExactLengthEvent (valueBit omega) y (excessRowCount L f))]
  convert exact_joint_probability_le_relative_weight (C := C) (x := x) (y := y) hL he hf using 1
  rw [eventProbability_fullUniformPMF_eq,finiteUniformProbability_eq_uniformEventProbability]

/-- Equal signed target rates make the genuine Hessian envelope independent of the signs. -/
theorem entryFactor_independent_signs (lambda : ℝ≥0) (E : ℕ)
    (e f : Fin (E+1)) (s t : F₂) :
    entryFactor (signedAggregateRates lambda E) (e,s) (f,t)=
      entryFactor (signedAggregateRates lambda E) (e,0) (f,0) := rfl

end
end PaperC.V282.UnsignedMarkedRelations
