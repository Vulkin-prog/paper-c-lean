import PaperCV282.FiniteFieldPoissonCoupling

/-! # Countable one-sided mass deficits and regular configuration restriction

All probability masses are genuine summable functions. The target space may
be countably infinite; no finite-state replacement is used.
-/
namespace PaperC.Prel8.PalmDeficit
open PaperC.V282.FiniteFieldTotalVariation
open scoped BigOperators
noncomputable section
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

variable {Ω : Type*}

def deficit (p q : Ω → ℝ) (regular : Ω → Prop) : ℝ :=
  ∑' z, if regular z then max (q z-p z) 0 else 0

def exceptionalMass (q : Ω → ℝ) (regular : Ω → Prop) : ℝ :=
  ∑' z, if regular z then 0 else q z

theorem positive_part_identity (x : ℝ) : max x 0=(|x|+x)/2 := by
  by_cases h : 0 ≤ x
  · rw [max_eq_left h,abs_of_nonneg h]; ring
  · rw [max_eq_right (le_of_not_ge h),abs_of_nonpos (le_of_not_ge h)]; ring

theorem deficit_term_le {p q : Ω → ℝ} (hp : ∀ z, 0 ≤ p z) (hq : ∀ z, 0 ≤ q z) (z : Ω) :
    max (q z-p z) 0 ≤ q z := max_le (by linarith [hp z]) (hq z)

theorem summable_positive_deficit {p q : Ω → ℝ} (hqsum : Summable q)
    (hp : ∀ z, 0 ≤ p z) (hq : ∀ z, 0 ≤ q z) : Summable (fun z => max (q z-p z) 0) :=
  hqsum.of_nonneg_of_le (fun _ => le_max_right _ _) (deficit_term_le hp hq)

/-- Half-L1 variation equals the target-side positive mass deficit. -/
theorem massTotalVariation_eq_deficit {p q : Ω → ℝ} (hpsum : HasSum p 1) (hqsum : HasSum q 1)
    (hp : ∀ z, 0 ≤ p z) (hq : ∀ z, 0 ≤ q z) :
    massTotalVariation p q=∑' z, max (q z-p z) 0 := by
  have ha := summable_abs_sub_of_nonneg hqsum.summable hpsum.summable hq hp
  simp_rw [positive_part_identity]
  rw [tsum_div_const,ha.tsum_add (hqsum.summable.sub hpsum.summable),
    (hqsum.summable.tsum_sub hpsum.summable),hpsum.tsum_eq,hqsum.tsum_eq]
  simp only [sub_self,add_zero]
  rw [massTotalVariation_comm]
  unfold massTotalVariation
  ring

theorem summable_restricted_deficit {p q : Ω → ℝ} (hqsum : Summable q)
    (hp : ∀ z, 0 ≤ p z) (hq : ∀ z, 0 ≤ q z) (regular : Ω → Prop) :
    Summable (fun z => if regular z then max (q z-p z) 0 else 0) :=
  (summable_positive_deficit hqsum hp hq).of_nonneg_of_le
    (fun z => by split_ifs <;> positivity) (fun z => by split_ifs <;> simp)

theorem summable_exceptional {q : Ω → ℝ} (hqsum : Summable q)
    (hq : ∀ z, 0 ≤ q z) (regular : Ω → Prop) :
    Summable (fun z => if regular z then 0 else q z) :=
  hqsum.of_nonneg_of_le (fun z => by split_ifs; exact le_refl 0; exact hq z)
    (fun z => by split_ifs <;> simp [hq])

theorem deficit_nonneg (p q : Ω → ℝ) (regular : Ω → Prop) : 0 ≤ deficit p q regular := by
  apply tsum_nonneg
  intro z
  split_ifs <;> positivity

/-- Restriction loses at most the target probability of irregular configurations. -/
theorem deficit_restriction {p q : Ω → ℝ} (hpsum : HasSum p 1) (hqsum : HasSum q 1)
    (hp : ∀ z, 0 ≤ p z) (hq : ∀ z, 0 ≤ q z) (regular : Ω → Prop) :
    0 ≤ massTotalVariation p q-deficit p q regular ∧
      massTotalVariation p q-deficit p q regular ≤ exceptionalMass q regular := by
  have hin := summable_restricted_deficit hqsum.summable hp hq regular
  have hout := summable_restricted_deficit hqsum.summable hp hq (fun z => ¬regular z)
  have hsplit : massTotalVariation p q=deficit p q regular+deficit p q (fun z => ¬regular z) := by
    rw [massTotalVariation_eq_deficit hpsum hqsum hp hq]
    unfold deficit
    rw [← hin.tsum_add hout]
    apply tsum_congr
    intro z
    by_cases hz : regular z <;> simp [hz]
  rw [hsplit,add_sub_cancel_left]
  refine ⟨deficit_nonneg _ _ _,?_⟩
  apply hout.tsum_le_tsum _ (summable_exceptional hqsum.summable hq regular)
  intro z
  by_cases hz : regular z
  · simp [hz]
  · simpa [hz] using deficit_term_le hp hq z

/-- Exact regular configuration masses turn the deficit into a Palm void average. -/
theorem deficit_eq_void_average {p q v : Ω → ℝ} (regular : Ω → Prop) (mu : ℝ)
    (hq : ∀ z, 0 ≤ q z) (hmass : ∀ z, regular z → p z=q z*(Real.exp mu*v z)) :
    deficit p q regular=∑' z, if regular z then q z*max (1-Real.exp mu*v z) 0 else 0 := by
  apply tsum_congr
  intro z
  by_cases hz : regular z
  · simp only [hz,ite_true,hmass z hz]
    rw [mul_max_of_nonneg _ _ (hq z)]
    congr 1 <;> ring
  · simp [hz]

/-- Multiplication by target mass cancels the exponentially large Palm normalization. -/
theorem averaged_deletion_identity {q vG v : Ω → ℝ} (regular : Ω → Prop) (mu : ℝ) :
    (∑' z, if regular z then q z*Real.exp mu*(vG z-v z) else 0)=
      ∑' z, if regular z then q z*(Real.exp mu*vG z)-q z*(Real.exp mu*v z) else 0 := by
  apply tsum_congr
  intro z
  split_ifs <;> ring

end
end PaperC.Prel8.PalmDeficit
