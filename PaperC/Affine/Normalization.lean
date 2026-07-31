import PaperC.Affine.Fourier

set_option maxHeartbeats 800000

/-!
# Normalized affine Fourier identity

This file completes the finite linear-algebraic normalization in Lemma 2.1 of
Paper C.  The restriction of the right-hand side to the relation space is a
linear character.  Its signed sum is either the cardinality of the relation
space or zero, according as that character is trivial or nontrivial.

Writing `relationEta` for this zero-one alternative and `relationRho` for the
dimension of the relation space gives the exact identity

`relationSignedSum A b = η * 2 ^ ρ`

and, unconditionally,

`|η * 2 ^ ρ - 1| ≤ 2 ^ ρ - 1`.
-/

namespace PaperC.Affine

open scoped BigOperators Classical

local instance : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

noncomputable section

variable {V β : Type*}
variable [AddCommGroup V] [Module 𝔽₂ V]
variable [Fintype β]

local instance relationSpaceFintype
    (A : V →ₗ[𝔽₂] (β → 𝔽₂)) :
    Fintype (RelationSpace A) :=
  Fintype.ofFinite _

/--
The restriction to the relation space of the linear form defined by the
right-hand side `b`.  This is the form denoted `q_x` in the manuscript.
-/
def relationCharacter
    (A : V →ₗ[𝔽₂] (β → 𝔽₂)) (b : β → 𝔽₂) :
    RelationSpace A →ₗ[𝔽₂] 𝔽₂ :=
  (dotLinear b).comp (RelationSpace A).subtype

@[simp]
theorem relationCharacter_apply
    (A : V →ₗ[𝔽₂] (β → 𝔽₂)) (b : β → 𝔽₂)
    (u : RelationSpace A) :
    relationCharacter A b u = dotProduct (u : β → 𝔽₂) b := by
  simp [relationCharacter, dotProduct_comm]

/-- The relation defect `ρ = dim R` from Lemma 2.1. -/
def relationRho (A : V →ₗ[𝔽₂] (β → 𝔽₂)) : ℕ :=
  Module.finrank 𝔽₂ (RelationSpace A)

/--
The compatibility indicator from Lemma 2.1, defined in the manuscript's
Fourier form: it is one exactly when `q` is trivial on the relation space.
-/
def relationEta
    (A : V →ₗ[𝔽₂] (β → 𝔽₂)) (b : β → 𝔽₂) : ℕ :=
  if relationCharacter A b = 0 then 1 else 0

@[simp]
theorem relationEta_eq_one_iff
    (A : V →ₗ[𝔽₂] (β → 𝔽₂)) (b : β → 𝔽₂) :
    relationEta A b = 1 ↔ relationCharacter A b = 0 := by
  simp [relationEta]

@[simp]
theorem relationEta_eq_zero_iff
    (A : V →ₗ[𝔽₂] (β → 𝔽₂)) (b : β → 𝔽₂) :
    relationEta A b = 0 ↔ relationCharacter A b ≠ 0 := by
  simp [relationEta]

/-- In particular, the Fourier compatibility factor belongs to `{0,1}`. -/
theorem relationEta_eq_zero_or_one
    (A : V →ₗ[𝔽₂] (β → 𝔽₂)) (b : β → 𝔽₂) :
    relationEta A b = 0 ∨ relationEta A b = 1 := by
  classical
  by_cases hq : relationCharacter A b = 0
  · exact Or.inr (by simp [relationEta, hq])
  · exact Or.inl (by simp [relationEta, hq])

/--
Compatibility makes the right-hand side character vanish on every relation.
This is the direct implication in the finite-dimensional Fredholm
alternative underlying Lemma 2.1.
-/
theorem relationCharacter_eq_zero_of_compatible
    (A : V →ₗ[𝔽₂] (β → 𝔽₂)) (b : β → 𝔽₂)
    (hcompat : Compatible A b) :
    relationCharacter A b = 0 := by
  obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hcompat
  apply LinearMap.ext
  intro u
  have hu :
      relationFunctional A (u : β → 𝔽₂) x = 0 :=
    DFunLike.congr_fun u.property x
  simpa only [relationCharacter_apply, relationFunctional_apply, hx,
    LinearMap.zero_apply] using hu

section SignedSum

variable [DecidableEq β]

/--
The indicator sum used in `relationSignedSum` is exactly the character sum
over the relation subtype.
-/
theorem relationSignedSum_eq_sum_relationCharacter
    (A : V →ₗ[𝔽₂] (β → 𝔽₂)) (b : β → 𝔽₂) :
    relationSignedSum A b =
      ∑ u : RelationSpace A, binarySign (relationCharacter A b u) := by
  classical
  unfold relationSignedSum
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype
    (s := Finset.univ.filter fun u => relationMap A u = 0)
    (p := fun u => u ∈ RelationSpace A)
    (F := relationSpaceFintype A)]
  · simp only [relationCharacter_apply]
  · intro u
    simp [RelationSpace]

/--
A relation-character sum is the full power of two for the trivial character
and zero for a nontrivial character.
-/
theorem relationSignedSum_eq_ite
    (A : V →ₗ[𝔽₂] (β → 𝔽₂)) (b : β → 𝔽₂) :
    relationSignedSum A b =
      if relationCharacter A b = 0 then
        (2 : ℤ) ^ relationRho A
      else
        0 := by
  classical
  rw [relationSignedSum_eq_sum_relationCharacter,
    sum_binarySign_linear]
  by_cases hq : relationCharacter A b = 0
  · simp only [if_pos hq]
    norm_cast
    simpa [relationRho, ZMod.card] using
      (Module.card_eq_pow_finrank
        (K := 𝔽₂) (V := RelationSpace A))
  · simp [hq]

/-- Exact evaluation of the signed relation sum as `η 2^ρ`. -/
theorem relationSignedSum_eq_eta_mul_two_pow_rho
    (A : V →ₗ[𝔽₂] (β → 𝔽₂)) (b : β → 𝔽₂) :
    relationSignedSum A b =
      (relationEta A b : ℤ) * (2 : ℤ) ^ relationRho A := by
  classical
  rw [relationSignedSum_eq_ite]
  by_cases hq : relationCharacter A b = 0
  · simp [relationEta, hq]
  · simp [relationEta, hq]

section Compatibility

variable [Fintype V] [DecidableEq V]

/--
Conversely, if the right-hand side character vanishes on every relation, the
affine system is compatible.  The proof uses the already established finite
Fourier identity: an incompatible system would give a zero left-hand side,
whereas a trivial relation character contributes the nonzero quantity
`2^ρ`.
-/
theorem compatible_of_relationCharacter_eq_zero
    (A : V →ₗ[𝔽₂] (β → 𝔽₂)) (b : β → 𝔽₂)
    (hq : relationCharacter A b = 0) :
    Compatible A b := by
  by_contra hcompat
  have hnone : ∀ x : V, A x ≠ b := by
    intro x hx
    exact hcompat (LinearMap.mem_range.mpr ⟨x, hx⟩)
  have hfilter :
      (Finset.univ.filter fun x : V => A x = b).card = 0 := by
    simp [hnone]
  have hfourier := affineFiber_fourier_identity A b
  rw [hfilter, relationSignedSum_eq_ite, if_pos hq] at hfourier
  simp only [Nat.cast_zero, mul_zero] at hfourier
  have hcardV : (Fintype.card V : ℤ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card V ≠ 0)
  have hpow : (2 : ℤ) ^ relationRho A ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  exact (mul_ne_zero hcardV hpow) hfourier.symm

/--
The manuscript's criterion: the relation character is trivial exactly when
the affine system is compatible.
-/
theorem relationCharacter_eq_zero_iff_compatible
    (A : V →ₗ[𝔽₂] (β → 𝔽₂)) (b : β → 𝔽₂) :
    relationCharacter A b = 0 ↔ Compatible A b :=
  ⟨compatible_of_relationCharacter_eq_zero A b,
    relationCharacter_eq_zero_of_compatible A b⟩

@[simp]
theorem relationEta_eq_one_iff_compatible
    (A : V →ₗ[𝔽₂] (β → 𝔽₂)) (b : β → 𝔽₂) :
    relationEta A b = 1 ↔ Compatible A b := by
  rw [relationEta_eq_one_iff,
    relationCharacter_eq_zero_iff_compatible]

@[simp]
theorem relationEta_eq_zero_iff_not_compatible
    (A : V →ₗ[𝔽₂] (β → 𝔽₂)) (b : β → 𝔽₂) :
    relationEta A b = 0 ↔ ¬Compatible A b := by
  rw [relationEta_eq_zero_iff, ne_eq,
    relationCharacter_eq_zero_iff_compatible]

/-- A coordinate space with `m` binary coordinates has cardinality `2^m`. -/
theorem card_pi_f2 :
    Fintype.card (β → 𝔽₂) = 2 ^ Fintype.card β := by
  rw [Fintype.card_fun, ZMod.card]

/--
The division-free affine identity with both manuscript normalization factors
made explicit.
-/
theorem affineFiber_normalized_card_identity
    (A : V →ₗ[𝔽₂] (β → 𝔽₂)) (b : β → 𝔽₂) :
    (2 : ℤ) ^ Fintype.card β *
        ((Finset.univ.filter fun x : V => A x = b).card : ℤ) =
      (Fintype.card V : ℤ) *
        ((relationEta A b : ℤ) * (2 : ℤ) ^ relationRho A) := by
  calc
    (2 : ℤ) ^ Fintype.card β *
        ((Finset.univ.filter fun x : V => A x = b).card : ℤ) =
        (Fintype.card (β → 𝔽₂) : ℤ) *
          ((Finset.univ.filter fun x : V => A x = b).card : ℤ) := by
            rw [card_pi_f2]
            norm_cast
    _ = (Fintype.card V : ℤ) * relationSignedSum A b :=
      affineFiber_fourier_identity A b
    _ = (Fintype.card V : ℤ) *
        ((relationEta A b : ℤ) * (2 : ℤ) ^ relationRho A) := by
      rw [relationSignedSum_eq_eta_mul_two_pow_rho]

end Compatibility

end SignedSum

/--
A nontrivial relation character forces the relation space to have positive
dimension.  This is the precise fact used in the incompatible case of (2.1).
-/
theorem relationRho_pos_of_character_ne_zero
    (A : V →ₗ[𝔽₂] (β → 𝔽₂)) (b : β → 𝔽₂)
    (hq : relationCharacter A b ≠ 0) :
    0 < relationRho A := by
  rw [relationRho, Module.finrank_pos_iff_exists_ne_zero]
  obtain ⟨u, hu⟩ := DFunLike.ne_iff.mp hq
  exact ⟨u, fun hzero => hu (by simp [hzero])⟩

/--
The unconditional absolute estimate in (2.1):

`|η 2^ρ - 1| ≤ 2^ρ - 1`.
-/
theorem abs_eta_mul_two_pow_rho_sub_one_le
    (A : V →ₗ[𝔽₂] (β → 𝔽₂)) (b : β → 𝔽₂) :
    |(relationEta A b : ℤ) * (2 : ℤ) ^ relationRho A - 1| ≤
      (2 : ℤ) ^ relationRho A - 1 := by
  classical
  by_cases hq : relationCharacter A b = 0
  · rw [show relationEta A b = 1 by simp [relationEta, hq]]
    simp only [Int.natCast_one, one_mul]
    have hpow : (1 : ℤ) ≤ (2 : ℤ) ^ relationRho A :=
      one_le_pow₀ (by norm_num)
    rw [abs_of_nonneg (sub_nonneg.mpr hpow)]
  · rw [show relationEta A b = 0 by simp [relationEta, hq]]
    simp only [Int.natCast_zero, zero_mul, zero_sub, abs_neg, abs_one]
    have hrho : 0 < relationRho A :=
      relationRho_pos_of_character_ne_zero A b hq
    obtain ⟨r, hr⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hrho)
    rw [hr, pow_succ]
    have hpow : (1 : ℤ) ≤ (2 : ℤ) ^ r :=
      one_le_pow₀ (by norm_num)
    nlinarith

end

end PaperC.Affine
