import PaperCV282.PrescribedValues

/-!
# Full-value relations and square products

A nonzero relation among the absolute valuation rows is exactly a nonempty
indexed subset whose product is a square. The inclusive prime cutoff must
contain every displayed positive value. No parity restriction is imposed on
the number of selected indices: these are full-value relations, before the
two block-parity constraints used for start events.
-/

namespace PaperC.V282.ValueSquareRelations

open Affine PrescribedValues
open scoped BigOperators

local instance : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

noncomputable section

variable {β : Type*} [Fintype β]

/-- The selected indices of a binary coefficient vector. -/
def relationSupport (u : β → F₂) : Finset β :=
  Finset.univ.filter fun i => u i ≠ 0

/-- Binary coefficients are the indicator of their support. -/
theorem sum_relationSupport_eq_dotProduct (u f : β → F₂) :
    ∑ i ∈ relationSupport u, f i = dotProduct u f := by
  rw [relationSupport, Finset.sum_filter, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  have hbinary : u i = 0 ∨ u i = 1 := by
    exact (by decide : ∀ a : F₂, a = 0 ∨ a = 1) (u i)
  rcases hbinary with h | h <;> simp [h]

/-- A binary vector is nonzero precisely when it selects an index. -/
theorem relationSupport_nonempty_iff (u : β → F₂) :
    (relationSupport u).Nonempty ↔ u ≠ 0 := by
  constructor
  · rintro ⟨i, hi⟩ hu
    have hi' : u i ≠ 0 := (Finset.mem_filter.mp hi).2
    exact hi' (by rw [hu]; rfl)
  · intro hu
    by_contra h
    apply hu
    funext i
    by_contra hi
    exact h ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩

/-- Evaluating at all prime basis vectors characterizes a full-value relation. -/
theorem mem_value_relation_iff_prime_equations
    (M : ℕ) (v : β → ℕ) (u : β → F₂) :
    u ∈ RelationSpace (valueSystem M v) ↔
      ∀ p : PrimeUpTo M, ∑ i, u i * parityVec (v i) p.val.val = 0 := by
  constructor
  · intro hu p
    have h := DFunLike.congr_fun hu (Pi.single p 1)
    simpa only [relationMap_apply, relationFunctional_apply,
      dotProduct, valueSystem_apply, valueBit_prime_basis,
      LinearMap.zero_apply] using h
  · intro h
    rw [LinearMap.mem_ker]
    apply LinearMap.ext
    intro ω
    rw [relationMap_apply, relationFunctional_apply]
    simp only [dotProduct, valueSystem_apply, valueBit, Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      (∑ p : PrimeUpTo M, ∑ i, u i * (ω p * parityVec (v i) p.val.val)) =
          ∑ p : PrimeUpTo M, ω p * (∑ i, u i * parityVec (v i) p.val.val) := by
        apply Finset.sum_congr rfl
        intro p _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by simp only [h, mul_zero, Finset.sum_const_zero]

/-- Once the cutoff contains the values, the prime equations are a square product. -/
theorem mem_value_relation_iff_square_product
    (M : ℕ) (v : β → ℕ) (hvpos : ∀ i, 0 < v i)
    (hvle : ∀ i, v i ≤ M) (u : β → F₂) :
    u ∈ RelationSpace (valueSystem M v) ↔
      ∃ r : ℕ, ∏ i ∈ relationSupport u, v i = r ^ 2 := by
  rw [← sum_parityVec_eq_zero_iff_prod_eq_sq (relationSupport u) v
    (fun i _ => (hvpos i).ne')]
  rw [mem_value_relation_iff_prime_equations]
  constructor
  · intro h
    ext p
    simp only [Finsupp.finsetSum_apply, Finsupp.zero_apply]
    by_cases hp : Nat.Prime p
    · by_cases hpM : p ≤ M
      · let q : PrimeUpTo M := ⟨⟨p, Nat.lt_succ_of_le hpM⟩, hp⟩
        rw [sum_relationSupport_eq_dotProduct]
        exact h q
      · have hzero : ∀ i, parityVec (v i) p = 0 := by
          intro i
          rw [parityVec_apply, Nat.factorization_eq_zero_of_not_dvd]
          · simp
          · intro hdvd
            exact hpM ((Nat.le_of_dvd (hvpos i) hdvd).trans (hvle i))
        simp [hzero]
    · simp [parityVec_apply, Nat.factorization_eq_zero_of_not_prime _ hp]
  · intro h p
    have hp := DFunLike.congr_fun h p.val.val
    simpa only [Finsupp.finsetSum_apply, Finsupp.zero_apply,
      sum_relationSupport_eq_dotProduct, dotProduct] using hp

/-- Positive full-value nullity is exactly a nonempty square-product subset. -/
theorem relationRho_ne_zero_iff_exists_nonempty_square_product
    (M : ℕ) (v : β → ℕ) (hvpos : ∀ i, 0 < v i)
    (hvle : ∀ i, v i ≤ M) :
    relationRho (valueSystem M v) ≠ 0 ↔
      ∃ s : Finset β, s.Nonempty ∧ ∃ r : ℕ, ∏ i ∈ s, v i = r ^ 2 := by
  classical
  rw [← Nat.pos_iff_ne_zero, relationRho,
    Module.finrank_pos_iff_exists_ne_zero]
  constructor
  · rintro ⟨u, hu⟩
    have hval : (u : β → F₂) ≠ 0 := by
      intro h
      apply hu
      exact Subtype.ext h
    exact ⟨relationSupport (u : β → F₂),
      (relationSupport_nonempty_iff (u : β → F₂)).2 hval,
      (mem_value_relation_iff_square_product M v hvpos hvle (u : β → F₂)).1
        u.property⟩
  · rintro ⟨s, hs, r, hr⟩
    let u : β → F₂ := fun i => if i ∈ s then 1 else 0
    have hsupport : relationSupport u = s := by
      ext i
      simp [relationSupport, u]
    have hmem : u ∈ RelationSpace (valueSystem M v) :=
      (mem_value_relation_iff_square_product M v hvpos hvle u).2
        ⟨r, by simpa [hsupport] using hr⟩
    refine ⟨⟨u, hmem⟩, ?_⟩
    intro hzero
    have hu : u = 0 := congrArg Subtype.val hzero
    have hnonempty : (relationSupport u).Nonempty := by simpa [hsupport] using hs
    exact (relationSupport_nonempty_iff u).1 hnonempty hu

end
end PaperC.V282.ValueSquareRelations
