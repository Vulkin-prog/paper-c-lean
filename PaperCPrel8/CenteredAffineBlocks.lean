import PaperCPrel8.AffinePalmEnvironment

/-! # Exact centered character expansion for overlapping affine blocks -/
namespace PaperC.Prel8.CenteredAffineBlocks
open Finset IndependentThinning ArratiaGoldsteinGordonInput V282.SteinFiniteExpectation
open _root_.PaperC.Affine AffinePalmCharacters AffinePalmEnvironment
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P
variable {U V α ι : Type*}
  [AddCommGroup U] [Module F₂ U] [Fintype U] [DecidableEq U]
  [AddCommGroup V] [Module F₂ V] [Fintype V] [DecidableEq V]
  [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]

def block (A : U →ₗ[F₂] (α → F₂)) (B : V →ₗ[F₂] (α → F₂))
    (b : α → F₂) (z : U×V) : ℝ := if A z.1+B z.2=b then 1 else 0

def referenceRate (α : Type*) [Fintype α] : ℝ := ((2:ℝ)^Fintype.card α)⁻¹

def blockCharacter (A : U →ₗ[F₂] (α → F₂)) (B : V →ₗ[F₂] (α → F₂))
    (b : α → F₂) (u : α → F₂) (z : U×V) : ℝ :=
  if u=0 then 0 else (binarySign (dotProduct u b):ℝ)*sign (relationMap A u) z.1*sign (relationMap B u) z.2

/-- Centering removes only the zero frequency; all singleton and overlap terms remain. -/
theorem centered_block (A : U →ₗ[F₂] (α → F₂)) (B : V →ₗ[F₂] (α → F₂))
    (b : α → F₂) (z : U×V) :
    block A B b z-referenceRate α=referenceRate α*∑ u : α → F₂, blockCharacter A B b u z := by
  let C : U×V →ₗ[F₂] (α → F₂) := A.comp (LinearMap.fst F₂ U V)+B.comp (LinearMap.snd F₂ U V)
  have hi := affine_indicator C b z
  have he (u : α → F₂) : sign (relationMap C u) z=
      sign (relationMap A u) z.1*sign (relationMap B u) z.2 := by
    simp [sign,relationMap_apply,relationFunctional_apply,C,dotProduct_add,binarySign_add]
  simp_rw [he] at hi
  change block A B b z=_ at hi
  let f : (α → F₂) → ℝ := fun u ↦ (binarySign (dotProduct u b):ℝ)*
    (sign (relationMap A u) z.1*sign (relationMap B u) z.2)
  have hzero : f 0=1 := by simp [f,sign]
  have hsum : (∑ u, f u)=1+∑ u, blockCharacter A B b u z := by
    calc
      _ = ∑ u, ((if u=0 then f u else 0)+(if u=0 then 0 else f u)) := by
        apply sum_congr rfl
        intro u hu
        by_cases h : u=0 <;> simp [h]
      _ = _ := by
        rw [sum_add_distrib]
        simp only [sum_ite_eq',mem_univ,ite_true,hzero]
        congr 1
        apply sum_congr rfl
        intro u hu
        by_cases h : u=0 <;> simp [blockCharacter,h,f,mul_assoc]
  dsimp only [f] at hsum
  rw [hsum] at hi
  simp only [Fintype.card_fun,ZMod.card,Nat.cast_pow,Nat.cast_ofNat] at hi
  rw [hi]
  unfold referenceRate
  ring

/-- Exact finite product expansion, valid for every collection of overlapping blocks. -/
theorem centered_product (A : ι → U →ₗ[F₂] (α → F₂)) (B : ι → V →ₗ[F₂] (α → F₂))
    (b : ι → α → F₂) (z : U×V) :
    (∏ j, (block (A j) (B j) (b j) z-referenceRate α))=
      (referenceRate α)^Fintype.card ι*
        ∑ u : ι → α → F₂, ∏ j, blockCharacter (A j) (B j) (b j) (u j) z := by
  simp_rw [centered_block]
  rw [prod_mul_distrib,prod_const,card_univ,Fintype.prod_sum]

/-- Multiplication of characters combines the actual row functionals before averaging. -/
theorem sign_sum {W : Type*} [AddCommGroup W] [Module F₂ W]
    (f : ι → W →ₗ[F₂] F₂) (x : W) : (∏ j, sign (f j) x)=sign (∑ j, f j) x := by
  have hg (S : Finset ι) : (∏ j∈S, sign (f j) x)=sign (∑ j∈S, f j) x := by
    induction S using Finset.induction_on with
    | empty => simp [sign]
    | @insert j S hj ih =>
      rw [prod_insert hj,sum_insert hj,ih]
      simp [sign,binarySign_add]
  exact hg univ

/-- Each frequency tuple is either excluded by a zero block or gives one signed character pair. -/
theorem block_product (A : ι → U →ₗ[F₂] (α → F₂)) (B : ι → V →ₗ[F₂] (α → F₂))
    (b : ι → α → F₂) (u : ι → α → F₂) (z : U×V) :
    (∏ j, blockCharacter (A j) (B j) (b j) (u j) z)=
      if ∀ j, u j≠0 then (∏ j, (binarySign (dotProduct (u j) (b j)):ℝ))*
        sign (∑ j, relationMap (A j) (u j)) z.1*sign (∑ j, relationMap (B j) (u j)) z.2 else 0 := by
  by_cases hu : ∀ j, u j≠0
  · rw [if_pos hu]
    simp only [blockCharacter,hu,ite_false,prod_mul_distrib,sign_sum]
  · rw [if_neg hu]
    push Not at hu
    obtain ⟨j,hj⟩ := hu
    exact prod_eq_zero (mem_univ j) (by simp [blockCharacter,hj])

end
end PaperC.Prel8.CenteredAffineBlocks
