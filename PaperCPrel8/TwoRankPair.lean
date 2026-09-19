import PaperCPrel8.AffinePalmEnvironment
import PaperCV282.DictionaryMarginalCap

/-! # The exact two-rank absolute conditional deviation in G.7 -/
namespace PaperC.Prel8.TwoRankPair
open Finset IndependentThinning ArratiaGoldsteinGordonInput V282.SteinFiniteExpectation
open _root_.PaperC.Affine V282.PrescribedValues V282.DictionaryMarginalCap
open AffinePalmEnvironment FiniteConditioning
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P
variable {U V β : Type*}
  [AddCommGroup U] [Module F₂ U] [Fintype U] [DecidableEq U]
  [AddCommGroup V] [Module F₂ V] [Fintype V] [DecidableEq V]
  [Fintype β] [DecidableEq β]

def combined (A : U →ₗ[F₂] (β → F₂)) (B : V →ₗ[F₂] (β → F₂)) :
    U×V →ₗ[F₂] (β → F₂) := A.comp (LinearMap.fst F₂ U V)+B.comp (LinearMap.snd F₂ U V)

def reference (β : Type*) [Fintype β] : ℝ := 1/(2:ℝ)^Fintype.card β

def conditionalMass (A : U →ₗ[F₂] (β → F₂)) (B : V →ₗ[F₂] (β → F₂))
    (b : β → F₂) (e : U) : ℝ :=
  eventProbability (FinitePMF.uniform V) (fun x ↦ B x=b-A e)

theorem affine_mass (B : V →ₗ[F₂] (β → F₂)) (b : β → F₂) :
    eventProbability (FinitePMF.uniform V) (fun x ↦ B x=b)=
      (relationEta B b:ℝ)*reference β*(2:ℝ)^relationRho B := by
  rw [eventProbability_affine_eq,probability_eq_eta_weight]
  push_cast
  unfold reference
  ring

theorem conditional_mass_dichotomy (A : U →ₗ[F₂] (β → F₂))
    (B : V →ₗ[F₂] (β → F₂)) (b : β → F₂) (e : U) :
    conditionalMass A B b e=0 ∨ conditionalMass A B b e=reference β*(2:ℝ)^relationRho B := by
  unfold conditionalMass
  rw [affine_mass]
  rcases relationEta_eq_zero_or_one B (b-A e) with h|h <;> simp [h]

theorem mean_conditional_mass (A : U →ₗ[F₂] (β → F₂))
    (B : V →ₗ[F₂] (β → F₂)) (b : β → F₂) :
    finitePMFExpectation (FinitePMF.uniform U) (conditionalMass A B b)=
      eventProbability (FinitePMF.uniform (U×V)) (fun z ↦ combined A B z=b) := by
  unfold conditionalMass finitePMFExpectation eventProbability
  simp only [FinitePMF.uniform,Fintype.card_prod,Nat.cast_mul,Fintype.sum_prod_type,mul_sum]
  apply sum_congr rfl
  intro e he
  apply sum_congr rfl
  intro x hx
  have hi : B x=b-A e ↔ combined A B (e,x)=b := by
    change B x=b-A e ↔ A e+B x=b
    exact eq_sub_iff_add_eq.trans (by rw [add_comm])
  by_cases h : B x=b-A e
  · simp only [if_pos h,if_pos (hi.mp h)]
    field_simp
  · simp only [if_neg h,if_neg (mt hi.mpr h),mul_zero]

theorem full_nullity_le (A : U →ₗ[F₂] (β → F₂)) (B : V →ₗ[F₂] (β → F₂)) :
    relationRho (combined A B)≤relationRho B := by
  apply Submodule.finrank_mono
  intro u hu
  apply LinearMap.ext
  intro x
  have h := DFunLike.congr_fun hu (0,x)
  simpa [combined,relationMap_apply,relationFunctional_apply] using h

theorem absolute_two_point {x r c : ℝ} (hr : 0≤r) (hc : r≤c) (hc0 : c≠0)
    (hx : x=0 ∨ x=c) : |x-r|=r+x-2*r/c*x := by
  rcases hx with rfl|rfl
  · simp [abs_of_nonneg hr]
  · rw [abs_of_nonneg (sub_nonneg.mpr hc)]
    field_simp
    ring

/-- Exact absolute deviation, including the compatibility indicator. -/
theorem absolute_mean (A : U →ₗ[F₂] (β → F₂))
    (B : V →ₗ[F₂] (β → F₂)) (b : β → F₂) :
    finitePMFExpectation (FinitePMF.uniform U) (fun e ↦ |conditionalMass A B b e-reference β|)=
      reference β*(1+(relationEta (combined A B) b:ℝ)*(2:ℝ)^relationRho (combined A B)*
        (1-2/(2:ℝ)^relationRho B)) := by
  have hr : 0<reference β := by unfold reference; positivity
  have hc : reference β≤reference β*(2:ℝ)^relationRho B :=
    le_mul_of_one_le_right hr.le (one_le_pow₀ (by norm_num))
  have hc0 : reference β*(2:ℝ)^relationRho B≠0 := by positivity
  simp_rw [absolute_two_point hr.le hc hc0 (conditional_mass_dichotomy A B b _)]
  rw [expectation_sub,expectation_add,expectation_const,expectation_const_mul,
    mean_conditional_mass,affine_mass]
  field_simp
  <;> ring

/-- Equation (G.7): the two ranks remain separate even when the full word law is uniform. -/
theorem compatible_absolute_mean (A : U →ₗ[F₂] (β → F₂))
    (B : V →ₗ[F₂] (β → F₂)) (b : β → F₂) (hb : Compatible (combined A B) b) :
    finitePMFExpectation (FinitePMF.uniform U) (fun e ↦ |conditionalMass A B b e-reference β|)=
      reference β*((2:ℝ)^relationRho (combined A B)-1+
        2*(1-(2:ℝ)^relationRho (combined A B)/(2:ℝ)^relationRho B)) := by
  rw [absolute_mean,(relationEta_eq_one_iff_compatible _ _).mpr hb]
  push_cast
  ring

theorem incompatible_absolute_mean (A : U →ₗ[F₂] (β → F₂))
    (B : V →ₗ[F₂] (β → F₂)) (b : β → F₂) (hb : ¬Compatible (combined A B) b) :
    finitePMFExpectation (FinitePMF.uniform U) (fun e ↦ |conditionalMass A B b e-reference β|)=
      reference β ∧ 1≤relationRho (combined A B) := by
  constructor
  · rw [absolute_mean,(relationEta_eq_zero_iff_not_compatible _ _).mpr hb]
    simp
  · exact relationRho_pos_of_character_ne_zero _ _
      (mt (relationCharacter_eq_zero_iff_compatible _ _).mp hb)

theorem absolute_mean_le (A : U →ₗ[F₂] (β → F₂))
    (B : V →ₗ[F₂] (β → F₂)) (b : β → F₂) :
    finitePMFExpectation (FinitePMF.uniform U) (fun e ↦ |conditionalMass A B b e-reference β|)≤
      reference β*((2:ℝ)^relationRho (combined A B)-1+
        2*(if relationRho (combined A B)<relationRho B then 1 else 0)) := by
  have hr : 0≤reference β := by unfold reference; positivity
  by_cases hb : Compatible (combined A B) b
  · rw [compatible_absolute_mean A B b hb]
    apply mul_le_mul_of_nonneg_left _ hr
    by_cases hlt : relationRho (combined A B)<relationRho B
    · rw [if_pos hlt]
      have hd : 0≤(2:ℝ)^relationRho (combined A B)/(2:ℝ)^relationRho B := by positivity
      linarith
    · have he := Nat.le_antisymm (full_nullity_le A B) (Nat.le_of_not_gt hlt)
      rw [if_neg hlt,he,div_self (by positivity)]
      ring_nf
      rfl
  · obtain ⟨he,hρ⟩ := incompatible_absolute_mean A B b hb
    rw [he]
    have hp : (2:ℝ)≤(2:ℝ)^relationRho (combined A B) := by
      simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hρ
    have hi : (0:ℝ) ≤ if relationRho (combined A B)<relationRho B then 1 else 0 := by positivity
    nlinarith

end
end PaperC.Prel8.TwoRankPair
