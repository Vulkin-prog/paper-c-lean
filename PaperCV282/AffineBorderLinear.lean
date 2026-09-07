import PaperC.Affine.Probability
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Exact affine intersection cost in the prime-coordinate dual

The overlap is the dimension of the intersection of row spaces, not the
number of equations that mention a border coordinate. Compatibility of the
stacked affine system is explicit.
-/
namespace PaperC.V282.AffineBorderLinear

open Affine LinearMap Module

noncomputable section

local instance instPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {V W Z : Type*}
variable [AddCommGroup V] [Module 𝔽₂ V]
variable [AddCommGroup W] [Module 𝔽₂ W]
variable [AddCommGroup Z] [Module 𝔽₂ Z]

/-- The actual row space as linear forms on the sample coordinates. -/
def rowSpace (A : V →ₗ[𝔽₂] W) : Submodule 𝔽₂ (Module.Dual 𝔽₂ V) :=
  LinearMap.range A.dualMap

/-- The number of independent consequences shared by two systems. -/
def rowOverlap (A : V →ₗ[𝔽₂] W) (B : V →ₗ[𝔽₂] Z) : ℕ :=
  Module.finrank 𝔽₂ (rowSpace A ⊓ rowSpace B : Submodule 𝔽₂ (Module.Dual 𝔽₂ V))

theorem rowSpace_finrank (A : V →ₗ[𝔽₂] W) :
    Module.finrank 𝔽₂ (rowSpace A)=Module.finrank 𝔽₂ (LinearMap.range A) :=
  LinearMap.finrank_range_dualMap_eq_finrank_range A

/-- Stacking equations forms the sum of their actual dual row spaces. -/
theorem rowSpace_prod (A : V →ₗ[𝔽₂] W) (B : V →ₗ[𝔽₂] Z) :
    rowSpace (A.prod B)=rowSpace A ⊔ rowSpace B := by
  simp only [rowSpace,LinearMap.range_dualMap_eq_dualAnnihilator_ker,
    LinearMap.ker_prod,Subspace.dualAnnihilator_inf_eq]

variable [Fintype V]

/-- Exact rank identity for the stacked system, with its true intersection dimension. -/
theorem stacked_rank_add_overlap (A : V →ₗ[𝔽₂] W) (B : V →ₗ[𝔽₂] Z) :
    Module.finrank 𝔽₂ (LinearMap.range (A.prod B))+rowOverlap A B =
      Module.finrank 𝔽₂ (LinearMap.range A)+Module.finrank 𝔽₂ (LinearMap.range B) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (rowSpace A) (rowSpace B)
  rw [← rowSpace_prod,rowSpace_finrank,rowSpace_finrank,rowSpace_finrank] at h
  exact h

theorem rowOverlap_le_right_rank (A : V →ₗ[𝔽₂] W) (B : V →ₗ[𝔽₂] Z) :
    rowOverlap A B≤Module.finrank 𝔽₂ (LinearMap.range B) := by
  have h := Submodule.finrank_mono (inf_le_right : rowSpace A ⊓ rowSpace B≤rowSpace B)
  rw [rowSpace_finrank] at h
  exact h

/-- A compatible finite affine fiber has mass precisely two to minus its rank. -/
theorem compatible_probability_inverse_rank (A : V →ₗ[𝔽₂] W) (b : W)
    (h : Compatible A b) :
    uniformSolutionProbability A b = 1/(2 : ℚ)^Module.finrank 𝔽₂ (LinearMap.range A) := by
  rw [uniformSolutionProbability_of_compatible A b h]
  have hr := LinearMap.finrank_range_add_finrank_ker A
  rw [← hr,pow_add]
  field_simp

/-- Exact finite conditional mass of one compatible affine system given the other. -/
theorem conditional_affine_probability (A : V →ₗ[𝔽₂] W) (B : V →ₗ[𝔽₂] Z)
    (b : W) (c : Z) (h : Compatible (A.prod B) (b,c)) :
    uniformSolutionProbability (A.prod B) (b,c)/uniformSolutionProbability A b =
      1/(2 : ℚ)^(Module.finrank 𝔽₂ (LinearMap.range B)-rowOverlap A B) := by
  have hA : Compatible A b := by
    obtain ⟨v,hv⟩ := h
    exact ⟨v,congrArg Prod.fst hv⟩
  rw [compatible_probability_inverse_rank _ _ h,compatible_probability_inverse_rank _ _ hA]
  have hs := stacked_rank_add_overlap A B
  have hi := rowOverlap_le_right_rank A B
  have heq : Module.finrank 𝔽₂ (LinearMap.range (A.prod B)) =
      Module.finrank 𝔽₂ (LinearMap.range A)+
        (Module.finrank 𝔽₂ (LinearMap.range B)-rowOverlap A B) := by omega
  rw [heq,pow_add]
  field_simp

/-- With disjoint row spaces every pair of separately compatible constraints is compatible. -/
theorem compatible_prod_of_rowOverlap_zero (A : V →ₗ[𝔽₂] W) (B : V →ₗ[𝔽₂] Z)
    (b : W) (c : Z) (hA : Compatible A b) (hB : Compatible B c)
    (hover : rowOverlap A B=0) : Compatible (A.prod B) (b,c) := by
  have hi : rowSpace A ⊓ rowSpace B=⊥ := Submodule.finrank_eq_zero.mp hover
  have hk : LinearMap.ker A ⊔ LinearMap.ker B=⊤ := by
    apply Submodule.dualAnnihilator_eq_bot_iff.mp
    rw [Submodule.dualAnnihilator_sup_eq,
      ← LinearMap.range_dualMap_eq_dualAnnihilator_ker,
      ← LinearMap.range_dualMap_eq_dualAnnihilator_ker]
    exact hi
  rw [Compatible,LinearMap.range_prod_eq hk]
  exact ⟨hA,hB⟩

end
end PaperC.V282.AffineBorderLinear
