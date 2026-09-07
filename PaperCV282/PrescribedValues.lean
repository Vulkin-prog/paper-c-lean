import PaperC.Affine.Normalization
import PaperC.Affine.Probability
import PaperC.Model.FiniteRademacher
import PaperC.Probability.ConditionalStartProbability
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Prescribed absolute values in a finite prime cylinder

The words in Corollary 2.6 of Paper C v2.8.2 prescribe absolute values, not
only the relative signs used for start events. Words are encoded by binary
bits using the retained `valueBit` and `phase` model.

This module proves the finite affine error bound, the private-coordinate
rank bound, and its specialization to actual valuation rows. `WindowValues`
supplies the arithmetic pivots from nondefective short-window vertices.
The asymptotic summed estimate remains a separate obligation.
-/

namespace PaperC.V282.PrescribedValues

open Affine
open ConditionalStartProbability
open scoped BigOperators

local instance : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

noncomputable section

section Generic

variable {V β : Type*} [AddCommGroup V] [Module F₂ V]
variable [Fintype V] [DecidableEq V] [Fintype β] [DecidableEq β]

/-- The retained Fourier normalization applied to an arbitrary word system. -/
theorem probability_eq_eta_weight
    (A : V →ₗ[F₂] (β → F₂)) (b : β → F₂) :
    uniformSolutionProbability A b =
      ((relationEta A b : ℚ) * (2 : ℚ) ^ relationRho A) /
        (2 : ℚ) ^ Fintype.card β := by
  classical
  unfold uniformSolutionProbability
  rw [Fintype.card_subtype]
  have h :
      (2 : ℚ) ^ Fintype.card β *
        ((Finset.univ.filter fun x : V => A x = b).card : ℚ) =
      (Fintype.card V : ℚ) *
        ((relationEta A b : ℚ) * (2 : ℚ) ^ relationRho A) := by
    exact_mod_cast affineFiber_normalized_card_identity A b
  have hc : (Fintype.card V : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card V ≠ 0)
  apply (div_eq_div_iff hc (pow_ne_zero _ (by norm_num))).2
  simpa [mul_assoc, mul_left_comm, mul_comm] using h

/-- The finite error bound is uniform in every prescribed right-hand side. -/
theorem abs_probability_sub_baseline_le
    (A : V →ₗ[F₂] (β → F₂)) (b : β → F₂) {m : ℕ}
    (hrho : relationRho A ≤ m) :
    |uniformSolutionProbability A b - 1 / (2 : ℚ) ^ Fintype.card β| ≤
      ((2 : ℚ) ^ m - 1) / (2 : ℚ) ^ Fintype.card β := by
  rw [probability_eq_eta_weight]
  have habs :
      |(relationEta A b : ℚ) * (2 : ℚ) ^ relationRho A - 1| ≤
        (2 : ℚ) ^ relationRho A - 1 := by
    exact_mod_cast abs_eta_mul_two_pow_rho_sub_one_le A b
  have hpow : (2 : ℚ) ^ relationRho A ≤ (2 : ℚ) ^ m :=
    pow_le_pow_right₀ (by norm_num) hrho
  have hdenom : 0 < (2 : ℚ) ^ Fintype.card β := by positivity
  rw [← sub_div, abs_div, abs_of_pos hdenom]
  exact div_le_div_of_nonneg_right (habs.trans (by linarith)) (by positivity)

omit [Fintype V] [DecidableEq V] in
/-- Every relation vanishes at a row with a private coordinate. -/
theorem relation_coefficient_eq_zero_of_private_coordinate
    (A : V →ₗ[F₂] (β → F₂)) (u : RelationSpace A)
    (i : β) (z : V) (hz : A z = Pi.single i 1) :
    (u : β → F₂) i = 0 := by
  have hrel : dotProduct (u : β → F₂) (A z) = 0 := by
    have h := DFunLike.congr_fun u.property z
    simpa only [relationMap_apply, relationFunctional_apply,
      LinearMap.zero_apply] using h
  simpa [hz, dotProduct_single] using hrel

/-- Relations are read on the rows that lack a private coordinate. -/
def defectRestriction (A : V →ₗ[F₂] (β → F₂)) (D : Finset β) :
    RelationSpace A →ₗ[F₂] (D → F₂) where
  toFun u i := u.val i.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype V] [DecidableEq V] in
theorem defectRestriction_injective
    (A : V →ₗ[F₂] (β → F₂)) (D : Finset β)
    (hprivate : ∀ i, i ∉ D → ∃ z : V, A z = Pi.single i 1) :
    Function.Injective (defectRestriction A D) := by
  intro u v huv
  apply Subtype.ext
  funext i
  by_cases hi : i ∈ D
  · exact congrFun huv ⟨i, hi⟩
  · obtain ⟨z, hz⟩ := hprivate i hi
    rw [relation_coefficient_eq_zero_of_private_coordinate A u i z hz,
      relation_coefficient_eq_zero_of_private_coordinate A v i z hz]

omit [Fintype V] [DecidableEq V] in
/-- Private rows bound full-value nullity without an even-subset condition. -/
theorem relationRho_le_card_of_private_coordinates
    (A : V →ₗ[F₂] (β → F₂)) (D : Finset β)
    (hprivate : ∀ i, i ∉ D → ∃ z : V, A z = Pi.single i 1) :
    relationRho A ≤ D.card := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (defectRestriction_injective A D hprivate)
  simpa [relationRho, Module.finrank_fintype_fun_eq_card] using h

/-- Finite Corollary 2.6 bound under explicit private-coordinate witnesses. -/
theorem probability_error_le_defect_weight
    (A : V →ₗ[F₂] (β → F₂)) (b : β → F₂) (D : Finset β)
    (hprivate : ∀ i, i ∉ D → ∃ z : V, A z = Pi.single i 1) :
    |uniformSolutionProbability A b - 1 / (2 : ℚ) ^ Fintype.card β| ≤
      ((2 : ℚ) ^ D.card - 1) / (2 : ℚ) ^ Fintype.card β :=
  abs_probability_sub_baseline_le A b
    (relationRho_le_card_of_private_coordinates A D hprivate)

/-- If every row has a private coordinate, every word is exactly uniform. -/
theorem probability_eq_baseline_of_private_coordinates
    (A : V →ₗ[F₂] (β → F₂)) (b : β → F₂)
    (hprivate : ∀ i, ∃ z : V, A z = Pi.single i 1) :
    uniformSolutionProbability A b = 1 / (2 : ℚ) ^ Fintype.card β := by
  have h := probability_error_le_defect_weight A b ∅ (fun i _ => hprivate i)
  have hz : |uniformSolutionProbability A b -
      1 / (2 : ℚ) ^ Fintype.card β| ≤ 0 := by simpa using h
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hz (abs_nonneg _)))

end Generic

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- Absolute valuation rows for any finite family of integer arguments. -/
def valueSystem (M : ℕ) (v : β → ℕ) :
    SampleSpace M →ₗ[F₂] (β → F₂) :=
  LinearMap.pi fun i => valueLinear M (v i)

omit [Fintype β] [DecidableEq β] in
@[simp]
theorem valueSystem_apply (M : ℕ) (v : β → ℕ) (ω : SampleSpace M) (i : β) :
    valueSystem M v ω i = valueBit ω (v i) := rfl

omit [Fintype β] [DecidableEq β] in
/-- Words are equalities of actual bits in the retained multiplicative model. -/
theorem valueSystem_eq_iff (M : ℕ) (v : β → ℕ)
    (b : β → F₂) (ω : SampleSpace M) :
    valueSystem M v ω = b ↔ ∀ i, valueBit ω (v i) = b i :=
  funext_iff

omit [DecidableEq β] in
/-- Its affine probability is exactly the retained finite-cylinder event law. -/
theorem probability_eq_uniform_event (M : ℕ) (v : β → ℕ) (b : β → F₂) :
    uniformSolutionProbability (valueSystem M v) b =
      uniformEventProbability (fun ω : SampleSpace M =>
        ∀ i, valueBit ω (v i) = b i) := by
  classical
  unfold uniformSolutionProbability uniformEventProbability
  rw [Fintype.card_subtype]
  congr 2
  apply congrArg Finset.card
  ext ω
  simp [solutionSet, valueSystem_eq_iff]

/-- A prime basis assignment reads the actual parity valuation at that prime. -/
theorem valueBit_prime_basis (M n : ℕ) (p : PrimeUpTo M) :
    valueBit (Pi.single p 1 : SampleSpace M) n = parityVec n p.val.val := by
  classical
  rw [valueBit, Fintype.sum_eq_single p]
  · simp
  · intro q hq
    simp [hq]

omit [Fintype β] in
/-- A prime private to a displayed value gives a private system coordinate. -/
theorem valueSystem_prime_basis (M : ℕ) (v : β → ℕ) (i : β)
    (p : PrimeUpTo M) (hdiag : parityVec (v i) p.val.val = 1)
    (hoff : ∀ j, j ≠ i → parityVec (v j) p.val.val = 0) :
    valueSystem M v (Pi.single p 1) = Pi.single i 1 := by
  funext j
  rw [valueSystem_apply, valueBit_prime_basis]
  by_cases hji : j = i
  · subst j
    simpa using hdiag
  · simp [hji, hoff j hji]

/-- Word probability bound with actual odd-valuation prime pivots. -/
theorem value_probability_error_le_of_private_primes
    (M : ℕ) (v : β → ℕ) (b : β → F₂) (D : Finset β)
    (hpivots : ∀ i, i ∉ D → ∃ p : PrimeUpTo M,
      parityVec (v i) p.val.val = 1 ∧
        ∀ j, j ≠ i → parityVec (v j) p.val.val = 0) :
    |uniformSolutionProbability (valueSystem M v) b -
      1 / (2 : ℚ) ^ Fintype.card β| ≤
        ((2 : ℚ) ^ D.card - 1) / (2 : ℚ) ^ Fintype.card β := by
  apply probability_error_le_defect_weight
  intro i hi
  obtain ⟨p, hp, hother⟩ := hpivots i hi
  exact ⟨Pi.single p 1, valueSystem_prime_basis M v i p hp hother⟩

/-- Word equations on the still-random primes above the conditioning cutoff. -/
def largeValueSystem (M Y : ℕ) (v : β → ℕ) :
    LargeSample M Y →ₗ[F₂] (β → F₂) :=
  (valueSystem M v).comp (extendLarge M Y)

/-- Fixing the small primes translates the word's right-hand side. -/
def conditionedValueRhs (M Y : ℕ) (v : β → ℕ) (b : β → F₂)
    (σ : SmallSample M Y) : β → F₂ :=
  b - valueSystem M v (extendSmall M Y σ)

omit [Fintype β] [DecidableEq β] in
theorem assemble_solves_values_iff (M Y : ℕ) (v : β → ℕ)
    (b : β → F₂) (σ : SmallSample M Y) (η : LargeSample M Y) :
    valueSystem M v (assemble M Y σ η) = b ↔
      largeValueSystem M Y v η = conditionedValueRhs M Y v b σ := by
  simp only [assemble, map_add, largeValueSystem, LinearMap.comp_apply,
    conditionedValueRhs]
  constructor <;> intro h
  · rw [← h]
    simp
  · rw [h]
    simp

/-- Every fixed small-prime assignment has the same exact word marginal. -/
theorem conditioned_value_probability_eq_baseline
    (M Y : ℕ) (v : β → ℕ) (b : β → F₂) (σ : SmallSample M Y)
    (hprivate : ∀ i, ∃ η : LargeSample M Y,
      largeValueSystem M Y v η = Pi.single i 1) :
    uniformSolutionProbability (largeValueSystem M Y v)
      (conditionedValueRhs M Y v b σ) =
        1 / (2 : ℚ) ^ Fintype.card β :=
  probability_eq_baseline_of_private_coordinates _ _ hprivate

end
end PaperC.V282.PrescribedValues
