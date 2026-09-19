import PaperCV282.DictionaryMarginalCap
import PaperCPrel8.DictionarySamplingBounds

/-! # Collision relations inject into the full two-word relation space

The right hand side of a word equality is zero. Hence compatibility is
a theorem, not an assumption, and its probability uses the full prime
system after the environment average.
-/
namespace PaperC.Prel8.DictionaryCollision
open PaperC.Affine PaperC.V282.PrescribedValues
open PaperC.V282.DictionaryMarginalCap PaperC.V282.WindowValues
open scoped BigOperators
noncomputable section
local instance : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {V β : Type*} [AddCommGroup V] [Module PaperC.F₂ V] [Fintype β]

/-- Stack both actual value systems without deleting a row. -/
def stacked (A C : V →ₗ[PaperC.F₂] (β → PaperC.F₂)) :
    V →ₗ[PaperC.F₂] (Sum β β → PaperC.F₂) where
  toFun x := Sum.elim (A x) (C x)
  map_add' x y := by ext i; cases i <;> simp [add_comm]
  map_smul' c x := by ext i; cases i <;> simp

/-- Duplicate the collision coefficients into the two full blocks. -/
def relationEmbedding (A C : V →ₗ[PaperC.F₂] (β → PaperC.F₂)) :
    RelationSpace (A-C) →ₗ[PaperC.F₂] RelationSpace (stacked A C) where
  toFun u := ⟨Sum.elim u.val (-u.val), by
    ext x
    have h := DFunLike.congr_fun u.property x
    simp only [relationMap_apply,relationFunctional_apply,LinearMap.zero_apply] at h ⊢
    change dotProduct (Sum.elim u.val (-u.val)) (Sum.elim (A x) (C x)) = 0
    simp only [dotProduct,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Pi.neg_apply,neg_mul]
    change dotProduct u.val ((A-C) x)=0 at h
    have hh : dotProduct u.val (A x-C x)=0 := h
    simp only [dotProduct,Pi.sub_apply,mul_sub,Finset.sum_sub_distrib] at hh
    simpa only [sub_eq_add_neg,Finset.sum_neg_distrib] using hh⟩
  map_add' u v := by
    apply Subtype.ext
    funext i
    cases i with
    | inl i => rfl
    | inr i => exact neg_add (u.val i) (v.val i)
  map_smul' c u := by
    apply Subtype.ext
    funext i
    cases i with
    | inl i => rfl
    | inr i => exact (smul_neg c (u.val i)).symm

/-- Reading the first block recovers the original relation. -/
theorem relationEmbedding_injective (A C : V →ₗ[PaperC.F₂] (β → PaperC.F₂)) :
    Function.Injective (relationEmbedding A C) := by
  intro u v h
  apply Subtype.ext
  funext i
  exact congrArg (fun z : RelationSpace (stacked A C) => z.val (Sum.inl i)) h

/-- The collision nullity is no larger than the full two-window nullity. -/
theorem collision_nullity_le (A C : V →ₗ[PaperC.F₂] (β → PaperC.F₂)) :
    relationRho (A-C) ≤ relationRho (stacked A C) :=
  LinearMap.finrank_le_finrank_of_injective (relationEmbedding_injective A C)

/-- Collision systems are homogeneous, so their exact probability has no compatibility loss. -/
theorem collision_probability_eq [Fintype V] [DecidableEq V] [DecidableEq β]
    (A C : V →ₗ[PaperC.F₂] (β → PaperC.F₂)) :
    uniformSolutionProbability (A-C) 0 =
      (2:ℚ)^relationRho (A-C)/(2:ℚ)^Fintype.card β := by
  rw [probability_eq_eta_weight]
  have h : relationEta (A-C) 0=1 := (relationEta_eq_one_iff_compatible (A-C) 0).mpr ⟨0,map_zero _⟩
  simp [h]

/-- Finite collision bound by the full, untruncated relation profile. -/
theorem collision_probability_le [Fintype V] [DecidableEq V] [DecidableEq β]
    (A C : V →ₗ[PaperC.F₂] (β → PaperC.F₂)) :
    uniformSolutionProbability (A-C) 0 ≤
      (2:ℚ)^relationRho (stacked A C)/(2:ℚ)^Fintype.card β := by
  rw [collision_probability_eq]
  exact div_le_div_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num) (collision_nullity_le A C)) (by positivity)

end
end PaperC.Prel8.DictionaryCollision
