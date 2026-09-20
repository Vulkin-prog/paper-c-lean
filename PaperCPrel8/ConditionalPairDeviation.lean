import PaperCPrel8.TwoRankPair

/-! # The absolute conditional pair layer pays only one conditioning mass -/
namespace PaperC.Prel8.ConditionalPairDeviation
open Finset IndependentThinning ArratiaGoldsteinGordonInput V282.SteinFiniteExpectation
open _root_.PaperC.Affine TwoRankPair FiniteConditioning
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Conditioning a centered statistic is controlled by its unconditional absolute deviation. -/
theorem conditioned_deviation {Ω : Type*} [Fintype Ω] (mu : FinitePMF Ω)
    (P : Ω → Prop) (hP : 0<eventProbability mu P) (f : Ω → ℝ) (r : ℝ) :
    |finitePMFExpectation (conditional mu P hP) f-r|≤
      finitePMFExpectation mu (fun w ↦ |f w-r|)/eventProbability mu P := by
  have he : finitePMFExpectation (conditional mu P hP) f-r=
      finitePMFExpectation (conditional mu P hP) (fun w ↦ f w-r) := by
    rw [expectation_sub,expectation_const]
  rw [he]
  exact (abs_expectation_le _ _).trans (expectation_conditional_le mu P hP _ (fun _ ↦ abs_nonneg _))

variable {U V β : Type*}
  [AddCommGroup U] [Module F₂ U] [Fintype U] [DecidableEq U]
  [AddCommGroup V] [Module F₂ V] [Fintype V] [DecidableEq V]
  [Fintype β] [DecidableEq β]

/-- G.7's conditional estimate for any prescribed word pair and positive environment event. -/
theorem conditional_pair_bound (A : U →ₗ[F₂] (β → F₂))
    (B : V →ₗ[F₂] (β → F₂)) (b : β → F₂)
    (P : U → Prop) (hP : 0<eventProbability (FinitePMF.uniform U) P) :
    |finitePMFExpectation (conditional (FinitePMF.uniform U) P hP) (conditionalMass A B b)-reference β|≤
      reference β*((2:ℝ)^relationRho (combined A B)-1+
        2*(if relationRho (combined A B)<relationRho B then 1 else 0))/
          eventProbability (FinitePMF.uniform U) P :=
  (conditioned_deviation _ P hP _ _).trans
    (div_le_div_of_nonneg_right (absolute_mean_le A B b) hP.le)

/-- Exact zero in the absence of either a full-value or a rough relation. -/
theorem zero_deviation_of_full_rough_rank (A : U →ₗ[F₂] (β → F₂))
    (B : V →ₗ[F₂] (β → F₂)) (b : β → F₂)
    (P : U → Prop) (hP : 0<eventProbability (FinitePMF.uniform U) P)
    (hB : relationRho B=0) :
    finitePMFExpectation (conditional (FinitePMF.uniform U) P hP) (conditionalMass A B b)=reference β := by
  have hAB : relationRho (combined A B)=0 := Nat.eq_zero_of_le_zero (hB ▸ full_nullity_le A B)
  have hh := conditional_pair_bound A B b P hP
  simp only [hAB,hB,pow_zero,sub_self,lt_self_iff_false,ite_false,mul_zero,add_zero,zero_div] at hh
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hh)

/-- Replacing the rank gap by nonzero rough nullity gives the host-count majorant. -/
theorem conditional_pair_host_bound (A : U →ₗ[F₂] (β → F₂))
    (B : V →ₗ[F₂] (β → F₂)) (b : β → F₂)
    (P : U → Prop) (hP : 0<eventProbability (FinitePMF.uniform U) P) :
    |finitePMFExpectation (conditional (FinitePMF.uniform U) P hP) (conditionalMass A B b)-reference β|≤
      reference β*((2:ℝ)^relationRho (combined A B)-1+
        2*(if 0<relationRho B then 1 else 0))/eventProbability (FinitePMF.uniform U) P := by
  apply (conditional_pair_bound A B b P hP).trans
  apply div_le_div_of_nonneg_right _ hP.le
  apply mul_le_mul_of_nonneg_left _ (by unfold reference; positivity)
  by_cases hB : 0<relationRho B
  · rw [if_pos hB]
    split_ifs <;> linarith
  · have hz := Nat.eq_zero_of_not_pos hB
    simp [hz]

end
end PaperC.Prel8.ConditionalPairDeviation
