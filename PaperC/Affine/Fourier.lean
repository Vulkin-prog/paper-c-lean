import PaperC.Affine.System
import Mathlib.LinearAlgebra.Matrix.DotProduct

set_option maxHeartbeats 800000

/-!
# Fourier expansion of finite affine systems over `𝔽₂`

This file proves the finite Fourier identity behind Lemma 2.1 of Paper C.
The equation is stated without division, over `ℤ`, so that it remains exact:

`|W| · #{x | A x = b} = |V| · ∑_{relations u} (-1)^(u ⬝ b)`.

Here `W = β → 𝔽₂`, and a row vector `u : β → 𝔽₂` is a relation when
`x ↦ u ⬝ A x` is the zero linear form.  The right-hand sum is represented as
a sum over every `u`, with zero contribution away from the relation kernel.

The proof is the standard double character sum.  It is completely finite and
uses no analytic input.
-/

namespace PaperC.Affine

open scoped BigOperators Classical

local instance : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

/-- The real-valued sign character of `𝔽₂`, represented exactly in `ℤ`. -/
def binarySign (t : 𝔽₂) : ℤ :=
  if t = 0 then 1 else -1

@[simp]
theorem binarySign_zero : binarySign 0 = 1 := by
  simp [binarySign]

@[simp]
theorem binarySign_eq_one_iff (t : 𝔽₂) :
    binarySign t = 1 ↔ t = 0 := by
  by_cases ht : t = 0 <;> simp [binarySign, ht]

theorem binarySign_add (a b : 𝔽₂) :
    binarySign (a + b) = binarySign a * binarySign b := by
  revert a b
  decide

@[simp]
theorem binarySign_neg (a : 𝔽₂) :
    binarySign (-a) = binarySign a := by
  rw [ZMod.neg_eq_self_mod_two]

theorem binarySign_sub (a b : 𝔽₂) :
    binarySign (a - b) = binarySign a * binarySign b := by
  rw [sub_eq_add_neg, binarySign_add, binarySign_neg]

section CharacterSum

variable {U : Type*} [AddCommGroup U] [Module 𝔽₂ U]

private theorem sum_binarySign_linear_of_ne_zero
    [Fintype U] [DecidableEq U]
    (f : U →ₗ[𝔽₂] 𝔽₂) (hf : f ≠ 0) :
    ∑ x : U, binarySign (f x) = 0 := by
  classical
  obtain ⟨a, ha⟩ : ∃ a : U, f a ≠ 0 := by
    by_contra h
    apply hf
    apply LinearMap.ext
    intro x
    simp only [LinearMap.zero_apply]
    by_contra hx
    exact h ⟨x, hx⟩
  have hshift :
      ∑ x : U, binarySign (f (a + x)) =
        ∑ x : U, binarySign (f x) :=
    Fintype.sum_bijective _ (AddGroup.addLeft_bijective a) _ _ fun _ => rfl
  simp_rw [map_add, binarySign_add] at hshift
  rw [← Finset.mul_sum] at hshift
  exact eq_zero_of_mul_eq_self_left
    ((binarySign_eq_one_iff (f a)).not.mpr ha) hshift

/--
Orthogonality of a binary character pulled back along a linear form.
The sum is the size of the source for the zero form and vanishes otherwise.
-/
theorem sum_binarySign_linear [Fintype U] [DecidableEq U]
    (f : U →ₗ[𝔽₂] 𝔽₂) :
    ∑ x : U, binarySign (f x) =
      if f = 0 then (Fintype.card U : ℤ) else 0 := by
  classical
  by_cases hf : f = 0
  · simp [hf]
  · rw [if_neg hf]
    exact sum_binarySign_linear_of_ne_zero f hf

end CharacterSum

section DotProduct

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- Dot product with a fixed vector, as a linear form in the second input. -/
def dotLinear (w : β → 𝔽₂) : (β → 𝔽₂) →ₗ[𝔽₂] 𝔽₂ where
  toFun y := dotProduct w y
  map_add' y z := dotProduct_add w y z
  map_smul' c y := dotProduct_smul c w y

omit [DecidableEq β] in
@[simp]
theorem dotLinear_apply (w y : β → 𝔽₂) :
    dotLinear w y = dotProduct w y :=
  rfl

/-- Nondegeneracy of the standard dot product on a finite coordinate space. -/
theorem dotLinear_eq_zero_iff (w : β → 𝔽₂) :
    dotLinear w = 0 ↔ w = 0 := by
  constructor
  · intro h
    apply dotProduct_eq_zero w
    intro y
    have hy := DFunLike.congr_fun h y
    simpa using hy
  · rintro rfl
    ext y
    simp

/-- Character orthogonality for the standard dot product on `β → 𝔽₂`. -/
theorem sum_binarySign_dotProduct (w : β → 𝔽₂) :
    ∑ y : β → 𝔽₂, binarySign (dotProduct y w) =
      if w = 0 then (Fintype.card (β → 𝔽₂) : ℤ) else 0 := by
  classical
  have h := sum_binarySign_linear (dotLinear w)
  simpa [dotProduct_comm, dotLinear_eq_zero_iff] using h

end DotProduct

section AffineFourier

variable {V β : Type*}
variable [AddCommGroup V] [Module 𝔽₂ V]
variable [Fintype V] [DecidableEq V] [Fintype β] [DecidableEq β]

/--
The linear form induced on `V` by a row vector `u` and a row map
`A : V → β → 𝔽₂`.
-/
def relationFunctional (A : V →ₗ[𝔽₂] (β → 𝔽₂)) (u : β → 𝔽₂) :
    V →ₗ[𝔽₂] 𝔽₂ :=
  (dotLinear u).comp A

omit [Fintype V] [DecidableEq V] [DecidableEq β] in
@[simp]
theorem relationFunctional_apply
    (A : V →ₗ[𝔽₂] (β → 𝔽₂)) (u : β → 𝔽₂) (x : V) :
    relationFunctional A u x = dotProduct u (A x) :=
  rfl

/-- The transpose map whose kernel is the space of relations among the rows of `A`. -/
def relationMap (A : V →ₗ[𝔽₂] (β → 𝔽₂)) :
    (β → 𝔽₂) →ₗ[𝔽₂] (V →ₗ[𝔽₂] 𝔽₂) where
  toFun := relationFunctional A
  map_add' u v := by
    ext x
    simp [relationFunctional, dotLinear, add_dotProduct]
  map_smul' c u := by
    ext x
    simp [relationFunctional, dotLinear, smul_dotProduct]

omit [Fintype V] [DecidableEq V] [DecidableEq β] in
@[simp]
theorem relationMap_apply
    (A : V →ₗ[𝔽₂] (β → 𝔽₂)) (u : β → 𝔽₂) :
    relationMap A u = relationFunctional A u :=
  rfl

/-- The relation space occurring in the Fourier expansion. -/
abbrev RelationSpace (A : V →ₗ[𝔽₂] (β → 𝔽₂)) :=
  LinearMap.ker (relationMap A)

/--
The signed sum over the relation kernel.  Writing it as an indicator sum over
the ambient finite coordinate space makes the exact Fourier proof especially
robust.
-/
noncomputable def relationSignedSum
    (A : V →ₗ[𝔽₂] (β → 𝔽₂)) (b : β → 𝔽₂) : ℤ :=
  ∑ u : β → 𝔽₂,
    if relationMap A u = 0 then binarySign (dotProduct u b) else 0

/--
The exact finite Fourier identity for an affine system over `𝔽₂`.

This is the division-free form of Lemma 2.1.  The left side is the codomain
size times the number of solutions; the right side is the source size times
the signed sum over all row relations.
-/
theorem affineFiber_fourier_identity
    (A : V →ₗ[𝔽₂] (β → 𝔽₂)) (b : β → 𝔽₂) :
    (Fintype.card (β → 𝔽₂) : ℤ) *
        ((Finset.univ.filter fun x : V => A x = b).card : ℤ) =
      (Fintype.card V : ℤ) * relationSignedSum A b := by
  classical
  let total : ℤ :=
    ∑ x : V, ∑ u : β → 𝔽₂,
      binarySign (dotProduct u (A x - b))
  have h_by_x :
      total =
        (Fintype.card (β → 𝔽₂) : ℤ) *
          ((Finset.univ.filter fun x : V => A x = b).card : ℤ) := by
    dsimp [total]
    calc
      (∑ x : V, ∑ u : β → 𝔽₂,
          binarySign (dotProduct u (A x - b))) =
          ∑ x : V,
            if A x - b = 0 then
              (Fintype.card (β → 𝔽₂) : ℤ)
            else 0 := by
              apply Finset.sum_congr rfl
              intro x _
              exact sum_binarySign_dotProduct (A x - b)
      _ = ∑ x : V,
            if A x = b then
              (Fintype.card (β → 𝔽₂) : ℤ)
            else 0 := by
              apply Finset.sum_congr rfl
              intro x _
              simp only [sub_eq_zero]
      _ = (Fintype.card (β → 𝔽₂) : ℤ) *
            ((Finset.univ.filter fun x : V => A x = b).card : ℤ) := by
              rw [← Finset.sum_filter]
              simp [mul_comm]
  have h_by_relation :
      total = (Fintype.card V : ℤ) * relationSignedSum A b := by
    dsimp [total, relationSignedSum]
    rw [Finset.sum_comm]
    calc
      (∑ u : β → 𝔽₂, ∑ x : V,
          binarySign (dotProduct u (A x - b))) =
          ∑ u : β → 𝔽₂,
            binarySign (dotProduct u b) *
              (∑ x : V, binarySign (relationFunctional A u x)) := by
                apply Finset.sum_congr rfl
                intro u _
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro x _
                rw [dotProduct_sub, binarySign_sub]
                rw [mul_comm]
                rfl
      _ = ∑ u : β → 𝔽₂,
            binarySign (dotProduct u b) *
              (if relationFunctional A u = 0 then
                (Fintype.card V : ℤ) else 0) := by
                  apply Finset.sum_congr rfl
                  intro u _
                  rw [sum_binarySign_linear]
      _ = (Fintype.card V : ℤ) *
            ∑ u : β → 𝔽₂,
              if relationMap A u = 0 then
                binarySign (dotProduct u b) else 0 := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro u _
                  by_cases hu : relationMap A u = 0
                  · have huf : relationFunctional A u = 0 := by
                      simpa only [relationMap_apply] using hu
                    simp [hu, huf, mul_comm]
                  · have huf : relationFunctional A u ≠ 0 := by
                      simpa only [relationMap_apply] using hu
                    simp [hu, huf]
  rw [← h_by_x, h_by_relation]

end AffineFourier

end PaperC.Affine
