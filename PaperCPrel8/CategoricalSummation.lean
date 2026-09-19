import PaperCPrel8.CategoricalPalm

/-! # Summing categorical labels before estimating directed site costs -/
namespace PaperC.Prel8.CategoricalSummation
open scoped BigOperators
noncomputable section
variable {J A : Type*} [Fintype J] [Fintype A] [DecidableEq J]
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

omit [DecidableEq J] in
/-- Regroup a double sum over labelled sites by its two sites first. -/
theorem sum_labelled_pairs (f : (J × A) → (J × A) → ℝ) :
    (∑ i, ∑ k, f i k) = ∑ j, ∑ k, ∑ a, ∑ b, f (j,a) (k,b) := by
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  exact Finset.sum_comm

/-- The same-site contribution is the square of the total rate, with no label count. -/
theorem same_site_sum (r : A → ℝ) :
    (∑ i : J × A, ∑ k : J × A, if k.1 = i.1 then r i.2 * r k.2 else 0) =
      (Fintype.card J : ℝ) * (∑ a, r a)^2 := by
  rw [sum_labelled_pairs]
  have hh (j k : J) : (∑ a, ∑ b, if k=j then r a*r b else 0) =
      if k=j then (∑ a, r a)^2 else 0 := by
    by_cases he : k=j <;> simp [he, ← Finset.mul_sum, ← Finset.sum_mul, sq]
  simp_rw [hh]
  simp

omit [DecidableEq J] in
/-- An arbitrary directed relation contributes one squared rate per ordered site pair. -/
theorem directed_product_sum (r : A → ℝ) (D : J → J → Prop) :
    (∑ i : J × A, ∑ k : J × A, if D i.1 k.1 then r i.2 * r k.2 else 0) =
      (∑ j, ∑ k, if D j k then (1 : ℝ) else 0) * (∑ a, r a)^2 := by
  rw [sum_labelled_pairs]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  by_cases hd : D j k <;> simp [hd, ← Finset.mul_sum, ← Finset.sum_mul, sq]

/-- The full categorical ledger splits into same-site, directed product, and joint costs. -/
theorem ledger_decomposition (r : A → ℝ) (D : J → J → Prop)
    (joint : (J × A) → (J × A) → ℝ) :
    (∑ i : J × A, ∑ k : J × A, if k.1 = i.1 then r i.2*r k.2 else
      if D i.1 k.1 then r i.2*r k.2 + joint i k else 0) =
      (Fintype.card J : ℝ) * (∑ a, r a)^2 +
      (∑ j, ∑ k, if k ≠ j ∧ D j k then (1 : ℝ) else 0) * (∑ a, r a)^2 +
      ∑ j, ∑ k, if k ≠ j ∧ D j k then ∑ a, ∑ b, joint (j,a) (k,b) else 0 := by
  have hp (i k : J × A) :
      (if k.1 = i.1 then r i.2*r k.2 else if D i.1 k.1 then r i.2*r k.2 + joint i k else 0) =
      (if k.1 = i.1 then r i.2*r k.2 else 0) +
      (if k.1 ≠ i.1 ∧ D i.1 k.1 then r i.2*r k.2 else 0) +
      (if k.1 ≠ i.1 ∧ D i.1 k.1 then joint i k else 0) := by
    split_ifs <;> simp_all
  simp_rw [hp, Finset.sum_add_distrib]
  rw [same_site_sum]
  have hprod : (∑ i : J × A, ∑ k : J × A,
      if k.1 ≠ i.1 ∧ D i.1 k.1 then r i.2*r k.2 else 0) =
      (∑ j, ∑ k, if k ≠ j ∧ D j k then (1 : ℝ) else 0) * (∑ a, r a)^2 := by
    convert directed_product_sum r (fun j k => k ≠ j ∧ D j k) using 1 <;> congr!
  rw [hprod, sum_labelled_pairs]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  by_cases hh : k ≠ j ∧ D j k <;> simp [hh]

end
end PaperC.Prel8.CategoricalSummation
