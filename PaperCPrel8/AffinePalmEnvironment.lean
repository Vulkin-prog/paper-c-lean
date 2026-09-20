import PaperCPrel8.AffinePalmCharacters

/-! # The small-prime environment survives planting and remains in Fourier coefficients -/
namespace PaperC.Prel8.AffinePalmEnvironment
open Finset IndependentThinning ArratiaGoldsteinGordonInput V282.SteinFiniteExpectation
open _root_.PaperC.Affine AffinePalmCharacters FiniteConditioning
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P
variable {U V β : Type*}
  [AddCommGroup U] [Module F₂ U] [Fintype U] [DecidableEq U]
  [AddCommGroup V] [Module F₂ V] [Fintype V] [DecidableEq V]
  [Fintype β] [DecidableEq β]

def environmentFourier (mu : FinitePMF U) (s : U →ₗ[F₂] F₂) : ℝ :=
  finitePMFExpectation mu (sign s)

def plant (A : U →ₗ[F₂] (β → F₂)) (B : V →ₗ[F₂] (β → F₂))
    (b : β → F₂) (z : U×V) : Prop := B z.2=b-A z.1

theorem expectation_product (mu : FinitePMF U) (nu : FinitePMF V) (f : U×V → ℝ) :
    finitePMFExpectation (productPMF mu nu) f=
      finitePMFExpectation mu (fun e ↦ finitePMFExpectation nu (fun x ↦ f (e,x))) := by
  simp only [finitePMFExpectation,productPMF,Fintype.sum_prod_type,mul_sum]
  apply sum_congr rfl
  intro e he
  apply sum_congr rfl
  intro x hx
  ring

/-- Planting does not alter any statistic of the environment, even under an arbitrary environment law. -/
theorem environment_joint (mu : FinitePMF U) (A : U →ₗ[F₂] (β → F₂))
    (B : V →ₗ[F₂] (β → F₂)) (hB : Function.Surjective B) (b : β → F₂) (f : U → ℝ) :
    finitePMFExpectation (productPMF mu (FinitePMF.uniform V))
      (fun z ↦ if plant A B b z then f z.1 else 0)=
      (Fintype.card (β → F₂):ℝ)⁻¹*finitePMFExpectation mu f := by
  rw [expectation_product]
  have he (e : U) : finitePMFExpectation (FinitePMF.uniform V)
      (fun x ↦ if plant A B b (e,x) then f e else 0)=
        f e*(Fintype.card (β → F₂):ℝ)⁻¹ := by
    have hh (x : V) : (if plant A B b (e,x) then f e else 0)=
        f e*(if B x=b-A e then (1:ℝ) else 0) := by by_cases h : B x=b-A e <;> simp [plant,h]
    simp_rw [hh]
    rw [expectation_const_mul]
    congr 1
    calc
      _ = eventProbability (FinitePMF.uniform V) (fun x ↦ B x=b-A e) := by
        unfold finitePMFExpectation eventProbability
        apply sum_congr rfl
        intro x hx
        by_cases h : B x=b-A e <;> simp [h]
      _ = _ := affine_presence B hB (b-A e)
  simp_rw [he]
  rw [expectation_mul_const,mul_comm]

theorem plant_probability (mu : FinitePMF U) (A : U →ₗ[F₂] (β → F₂))
    (B : V →ₗ[F₂] (β → F₂)) (hB : Function.Surjective B) (b : β → F₂) :
    eventProbability (productPMF mu (FinitePMF.uniform V)) (plant A B b)=
      (Fintype.card (β → F₂):ℝ)⁻¹ := by
  rw [← finitePMFExpectation_indicator]
  simpa only [expectation_const,mul_one] using environment_joint mu A B hB b (fun _ ↦ 1)

theorem environment_unchanged (mu : FinitePMF U) (A : U →ₗ[F₂] (β → F₂))
    (B : V →ₗ[F₂] (β → F₂)) (hB : Function.Surjective B) (b : β → F₂) (f : U → ℝ)
    (hp : 0<eventProbability (productPMF mu (FinitePMF.uniform V)) (plant A B b)) :
    finitePMFExpectation (conditional (productPMF mu (FinitePMF.uniform V)) (plant A B b) hp)
      (fun z ↦ f z.1)=finitePMFExpectation mu f := by
  rw [expectation_conditional,environment_joint mu A B hB b,plant_probability mu A B hB b]
  exact mul_div_cancel_left₀ _ (inv_ne_zero (by exact_mod_cast Fintype.card_ne_zero))

/-- The full signed coefficient before division by the plant probability. -/
theorem joint_fourier (mu : FinitePMF U) (A : U →ₗ[F₂] (β → F₂))
    (B : V →ₗ[F₂] (β → F₂)) (b : β → F₂) (s : U →ₗ[F₂] F₂) (w : V →ₗ[F₂] F₂) :
    finitePMFExpectation (productPMF mu (FinitePMF.uniform V))
      (fun z ↦ if plant A B b z then sign s z.1*sign w z.2 else 0)=
      (Fintype.card (β → F₂):ℝ)⁻¹*
        ∑ v : β → F₂, if relationMap B v=w then
          (binarySign (dotProduct v b):ℝ)*environmentFourier mu (s-relationMap A v) else 0 := by
  rw [expectation_product]
  have he (e : U) : finitePMFExpectation (FinitePMF.uniform V)
      (fun x ↦ if plant A B b (e,x) then sign s e*sign w x else 0)=
      (Fintype.card (β → F₂):ℝ)⁻¹*∑ v : β → F₂, if relationMap B v=w then
        (binarySign (dotProduct v b):ℝ)*sign (s-relationMap A v) e else 0 := by
    have hi (x : V) : (if plant A B b (e,x) then sign s e*sign w x else 0)=
        sign s e*(if B x=b-A e then sign w x else 0) := by
      by_cases h : B x=b-A e <;> simp [plant,h]
    simp_rw [hi]
    rw [expectation_const_mul,affine_joint_character,mul_left_comm,mul_sum]
    congr 1
    apply sum_congr rfl
    intro v hv
    by_cases h : relationMap B v=w
    · simp only [h,ite_true,sign_sub,sign,relationMap_apply,relationFunctional_apply,
        dotProduct_sub,LinearMap.sub_apply,binarySign_sub,Int.cast_mul]
      ring
    · simp only [h,ite_false,mul_zero]
  simp_rw [he]
  rw [expectation_const_mul,expectation_finset_sum]
  congr 1
  apply sum_congr rfl
  intro v hv
  by_cases h : relationMap B v=w
  · simp only [h,ite_true,expectation_const_mul,environmentFourier]
  · simp only [h,ite_false,expectation_const]

/-- G.6 retains the environment Fourier transform, rather than replacing it by an orthogonality indicator. -/
theorem conditional_fourier (mu : FinitePMF U) (A : U →ₗ[F₂] (β → F₂))
    (B : V →ₗ[F₂] (β → F₂)) (hB : Function.Surjective B)
    (b : β → F₂) (s : U →ₗ[F₂] F₂) (w : V →ₗ[F₂] F₂)
    (hp : 0<eventProbability (productPMF mu (FinitePMF.uniform V)) (plant A B b)) :
    finitePMFExpectation (conditional (productPMF mu (FinitePMF.uniform V)) (plant A B b) hp)
      (fun z ↦ sign s z.1*sign w z.2)=
      ∑ v : β → F₂, if relationMap B v=w then
        (binarySign (dotProduct v b):ℝ)*environmentFourier mu (s-relationMap A v) else 0 := by
  rw [expectation_conditional,joint_fourier,plant_probability mu A B hB b]
  exact mul_div_cancel_left₀ _ (inv_ne_zero (by exact_mod_cast Fintype.card_ne_zero))

end
end PaperC.Prel8.AffinePalmEnvironment
