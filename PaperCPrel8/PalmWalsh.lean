import PaperCPrel8.PalmTargetSignBound
import PaperC.Affine.Fourier

/-! # Exact Walsh energy under the independent fair target signs

Binary vectors index subsets of the planted blocks. The zero vector indexes
the empty subset. All coefficients, including the constant, are retained.
-/
namespace PaperC.Prel8.PalmWalsh
open Finset IndependentThinning ArratiaGoldsteinGordonInput V282.SteinFiniteExpectation
open _root_.PaperC.Affine
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Product of target signs selected by the binary subset vector. -/
def character (u x : ι → F₂) : ℝ := (binarySign (dotProduct x u):ℝ)

def expansion (a : (ι → F₂) → ℝ) (x : ι → F₂) : ℝ := ∑ u, a u*character u x

def energy (a : (ι → F₂) → ℝ) : ℝ := ∑ u, if u=0 then 0 else (a u)^2

theorem character_zero (x : ι → F₂) : character 0 x=1 := by simp [character]

theorem character_mul (u v x : ι → F₂) : character u x*character v x=character (u-v) x := by
  simp [character,dotProduct_sub,binarySign_sub]

/-- The actual uniform target average is exact character orthogonality. -/
theorem character_mean (u : ι → F₂) :
    finitePMFExpectation (FinitePMF.uniform (ι → F₂)) (character u)=if u=0 then 1 else 0 := by
  have hs := sum_binarySign_dotProduct u
  have hr : (∑ x : ι → F₂, character u x)=if u=0 then (Fintype.card (ι → F₂):ℝ) else 0 := by
    unfold character
    exact_mod_cast hs
  simp only [finitePMFExpectation,FinitePMF.uniform_prob,← mul_sum]
  rw [hr]
  by_cases hu : u=0 <;> simp [hu,Fintype.card_ne_zero]

theorem character_orthogonal (u v : ι → F₂) :
    finitePMFExpectation (FinitePMF.uniform (ι → F₂)) (fun x ↦ character u x*character v x)=
      if u=v then 1 else 0 := by
  simp_rw [character_mul]
  rw [character_mean]
  simp only [sub_eq_zero]

theorem expansion_mean (a : (ι → F₂) → ℝ) :
    finitePMFExpectation (FinitePMF.uniform (ι → F₂)) (expansion a)=a 0 := by
  unfold expansion
  rw [expectation_finset_sum]
  simp_rw [expectation_const_mul,character_mean]
  simp

theorem expansion_second_moment (a : (ι → F₂) → ℝ) :
    finitePMFExpectation (FinitePMF.uniform (ι → F₂)) (fun x ↦ (expansion a x)^2)=∑ u, (a u)^2 := by
  have he (x : ι → F₂) : (expansion a x)^2=
      ∑ u, ∑ v, (a u*a v)*(character u x*character v x) := by
    unfold expansion
    rw [sq,sum_mul_sum]
    apply sum_congr rfl
    intro u hu
    apply sum_congr rfl
    intro v hv
    ring
  simp_rw [he]
  rw [expectation_finset_sum]
  simp_rw [expectation_finset_sum,expectation_const_mul,character_orthogonal]
  simp [sq]

/-- Parseval for the centered expansion: the variance is precisely the nonconstant energy. -/
theorem expansion_variance (a : (ι → F₂) → ℝ) :
    finitePMFExpectation (FinitePMF.uniform (ι → F₂)) (fun x ↦ (expansion a x-a 0)^2)=energy a := by
  have he (x : ι → F₂) : (expansion a x-a 0)^2=
      (expansion a x)^2-2*a 0*expansion a x+(a 0)^2 := by ring
  simp_rw [he]
  rw [expectation_add,expectation_sub,expectation_const_mul,expectation_const,
    expansion_second_moment,expansion_mean]
  have hs : (∑ u, (a u)^2)=(a 0)^2+energy a := by
    unfold energy
    calc
      _ = ∑ u, ((if u=0 then (a u)^2 else 0)+(if u=0 then 0 else (a u)^2)) := by
        apply sum_congr rfl
        intro u hu
        by_cases h : u=0 <;> simp [h]
      _ = _ := by rw [sum_add_distrib]; simp
  rw [hs]
  ring

/-- G.6's target-sign bound with its exact Walsh coefficients and no variance premise. -/
theorem target_sign_bound (a : (ι → F₂) → ℝ) (hR : ∀ x, 0≤expansion a x) :
    finitePMFExpectation (FinitePMF.uniform (ι → F₂)) (fun x ↦ max (1-expansion a x) 0)≤
      min 1 (max (1-a 0) 0+(1/2:ℝ)*Real.sqrt (energy a)) := by
  have h := PalmTargetSignBound.deficit_mean_variance_bound (FinitePMF.uniform (ι → F₂))
    (expansion a) hR
  rwa [expansion_mean,expansion_variance] at h

/-- Walsh coefficients are computed from the actual observable. -/
def coefficients (R : (ι → F₂) → ℝ) (u : ι → F₂) : ℝ :=
  finitePMFExpectation (FinitePMF.uniform (ι → F₂)) (fun x ↦ R x*character u x)

theorem character_symm (u x : ι → F₂) : character u x=character x u := by
  simp only [character,dotProduct_comm]

/-- Finite inversion: no existence or expansion hypothesis is required. -/
theorem inversion (R : (ι → F₂) → ℝ) (x : ι → F₂) : expansion (coefficients R) x=R x := by
  have hkernel (y : ι → F₂) : (∑ u, character u y*character u x)=
      if y=x then (Fintype.card (ι → F₂):ℝ) else 0 := by
    simp_rw [character_symm (x := y),character_symm (x := x),character_mul]
    have hh := sum_binarySign_dotProduct (y-x)
    unfold character
    simp only [sub_eq_zero] at hh
    by_cases h : y=x
    · simp only [h,ite_true] at hh ⊢
      exact_mod_cast hh
    · simp only [h,ite_false] at hh ⊢
      exact_mod_cast hh
  unfold expansion coefficients finitePMFExpectation
  simp only [FinitePMF.uniform_prob,sum_mul]
  rw [sum_comm]
  have he (y : ι → F₂) :
      (∑ u, ((Fintype.card (ι → F₂):ℝ))⁻¹*(R y*character u y)*character u x)=
      ((Fintype.card (ι → F₂):ℝ))⁻¹*R y*(∑ u, character u y*character u x) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro u hu
    ring
  simp_rw [he,hkernel]
  simp only [mul_ite,mul_zero,sum_ite_eq',mem_univ,ite_true]
  field_simp

/-- The G.6 bound now applies to every actual nonnegative sign-dependent void. -/
theorem observable_target_sign_bound (R : (ι → F₂) → ℝ) (hR : ∀ x, 0≤R x) :
    finitePMFExpectation (FinitePMF.uniform (ι → F₂)) (fun x ↦ max (1-R x) 0)≤
      min 1 (max (1-coefficients R 0) 0+(1/2:ℝ)*Real.sqrt (energy (coefficients R))) := by
  have h := target_sign_bound (coefficients R) (by simpa only [inversion] using hR)
  simpa only [inversion] using h

end
end PaperC.Prel8.PalmWalsh
