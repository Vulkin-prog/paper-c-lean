import PaperCPrel8.PalmWalsh
import PaperCPrel8.FiniteConditioning

/-! # Signed characters on an actual finite affine Palm fibre -/
namespace PaperC.Prel8.AffinePalmCharacters
open Finset IndependentThinning ArratiaGoldsteinGordonInput V282.SteinFiniteExpectation
open _root_.PaperC.Affine
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P
variable {V β : Type*} [AddCommGroup V] [Module F₂ V] [Fintype V] [DecidableEq V]
  [Fintype β] [DecidableEq β]

/-- Real sign of a linear character, with its phase retained. -/
def sign (f : V →ₗ[F₂] F₂) (x : V) : ℝ := (binarySign (f x):ℝ)

theorem sign_sub (f g : V →ₗ[F₂] F₂) (x : V) : sign (f-g) x=sign f x*sign g x := by
  simp [sign,binarySign_sub]

theorem sign_mean (f : V →ₗ[F₂] F₂) :
    finitePMFExpectation (FinitePMF.uniform V) (sign f)=if f=0 then 1 else 0 := by
  have hs := sum_binarySign_linear f
  have hr : (∑ x, sign f x)=if f=0 then (Fintype.card V:ℝ) else 0 := by
    unfold sign
    by_cases hf : f=0
    · simp only [hf,ite_true] at hs ⊢; exact_mod_cast hs
    · simp only [hf,ite_false] at hs ⊢; exact_mod_cast hs
  simp only [finitePMFExpectation,FinitePMF.uniform_prob,← mul_sum]
  rw [hr]
  by_cases hf : f=0 <;> simp [hf,Fintype.card_ne_zero]

/-- Exact affine indicator expansion, prior to taking any absolute value. -/
theorem affine_indicator (B : V →ₗ[F₂] (β → F₂)) (b : β → F₂) (x : V) :
    (if B x=b then (1:ℝ) else 0)=(Fintype.card (β → F₂):ℝ)⁻¹*
      ∑ v : β → F₂, (binarySign (dotProduct v b):ℝ)*sign (relationMap B v) x := by
  have hs := sum_binarySign_dotProduct (B x-b)
  have he (v : β → F₂) : (binarySign (dotProduct v b):ℝ)*sign (relationMap B v) x=
      (binarySign (dotProduct v (B x-b)):ℝ) := by
    simp [sign,relationMap_apply,relationFunctional_apply,dotProduct_sub,binarySign_sub,mul_comm]
  simp_rw [he]
  have hr : (∑ v : β → F₂, (binarySign (dotProduct v (B x-b)):ℝ))=
      if B x=b then (Fintype.card (β → F₂):ℝ) else 0 := by
    simp only [sub_eq_zero] at hs
    by_cases hx : B x=b
    · simp only [hx,ite_true] at hs ⊢; exact_mod_cast hs
    · simp only [hx,ite_false] at hs ⊢; exact_mod_cast hs
  rw [hr]
  by_cases hx : B x=b <;> simp [hx,Fintype.card_ne_zero]

/-- Orthogonality on the actual unnormalized affine fibre. -/
theorem affine_joint_character (B : V →ₗ[F₂] (β → F₂)) (b : β → F₂) (w : V →ₗ[F₂] F₂) :
    finitePMFExpectation (FinitePMF.uniform V) (fun x ↦ if B x=b then sign w x else 0)=
      (Fintype.card (β → F₂):ℝ)⁻¹*
        ∑ v : β → F₂, if relationMap B v=w then (binarySign (dotProduct v b):ℝ) else 0 := by
  have he (x : V) : (if B x=b then sign w x else 0)=
      (Fintype.card (β → F₂):ℝ)⁻¹*
        ∑ v : β → F₂, (binarySign (dotProduct v b):ℝ)*sign (relationMap B v-w) x := by
    rw [show (if B x=b then sign w x else 0)=(if B x=b then (1:ℝ) else 0)*sign w x by split_ifs <;> ring,
      affine_indicator B b x,mul_assoc,sum_mul]
    congr 1
    apply sum_congr rfl
    intro v hv
    rw [sign_sub]
    ring
  simp_rw [he]
  rw [expectation_const_mul,expectation_finset_sum]
  simp_rw [expectation_const_mul,sign_mean]
  congr 1
  apply sum_congr rfl
  intro v hv
  by_cases h : relationMap B v=w <;> simp only [sub_eq_zero,h,ite_true,ite_false,mul_one,mul_zero]

/-- Full row rank gives uniqueness of the planted multiplier in G.6. -/
theorem relationMap_injective (B : V →ₗ[F₂] (β → F₂)) (hB : Function.Surjective B) :
    Function.Injective (relationMap B) := by
  intro u v huv
  have hzero : dotLinear (u-v)=0 := by
    apply LinearMap.ext
    intro b
    obtain ⟨x,rfl⟩ := hB b
    have hh := DFunLike.congr_fun huv x
    simp only [relationMap_apply,relationFunctional_apply] at hh
    simpa [dotLinear_apply,sub_dotProduct,hh]
  exact sub_eq_zero.mp ((dotLinear_eq_zero_iff _).mp hzero)

/-- Every affine plant has exactly the same probability on every environment. -/
theorem affine_presence (B : V →ₗ[F₂] (β → F₂)) (hB : Function.Surjective B) (b : β → F₂) :
    eventProbability (FinitePMF.uniform V) (fun x ↦ B x=b)=(Fintype.card (β → F₂):ℝ)⁻¹ := by
  rw [← finitePMFExpectation_indicator]
  have h := affine_joint_character B b 0
  have hrel (v : β → F₂) : relationMap B v=0 ↔ v=0 := by
    rw [← map_zero (relationMap B)]
    exact (relationMap_injective B hB).eq_iff
  simp only [hrel,sign,LinearMap.zero_apply,binarySign_zero,Int.cast_one,
    sum_ite_eq',mem_univ,ite_true,zero_dotProduct,mul_one] at h
  convert h using 1
  apply expectation_congr
  intro x
  by_cases hx : B x=b <;> simp [hx]

/-- The conditional fibre character has exactly the signed row-space sum. -/
theorem conditional_character (B : V →ₗ[F₂] (β → F₂)) (hB : Function.Surjective B)
    (b : β → F₂) (w : V →ₗ[F₂] F₂)
    (hp : 0<eventProbability (FinitePMF.uniform V) (fun x ↦ B x=b)) :
    finitePMFExpectation (FiniteConditioning.conditional (FinitePMF.uniform V) (fun x ↦ B x=b) hp)
      (sign w)=∑ v : β → F₂, if relationMap B v=w then (binarySign (dotProduct v b):ℝ) else 0 := by
  rw [FiniteConditioning.expectation_conditional,affine_presence B hB b]
  have hj : (finitePMFExpectation (FinitePMF.uniform V) (fun x ↦ if B x=b then sign w x else 0))=
      (Fintype.card (β → F₂):ℝ)⁻¹*∑ v : β → F₂,
        if relationMap B v=w then (binarySign (dotProduct v b):ℝ) else 0 := affine_joint_character B b w
  convert (congrArg (fun r : ℝ ↦ r/(Fintype.card (β → F₂):ℝ)⁻¹) hj).trans
    (mul_div_cancel_left₀ _ (inv_ne_zero (by exact_mod_cast Fintype.card_ne_zero))) using 1
  congr 1
  apply expectation_congr
  intro x
  by_cases hx : B x=b <;> simp [hx]

end
end PaperC.Prel8.AffinePalmCharacters
