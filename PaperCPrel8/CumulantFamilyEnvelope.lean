import PaperCPrel8.FiniteCumulantEnvelope

/-! # Cumulant envelopes restricted to a downward-closed family of subsets

This allows only distinct-site choices in the categorical application;
within-site cumulants are never introduced into its activity.
-/
namespace PaperC.Prel8.CumulantFamilyEnvelope
open Finset FiniteCumulantPartitions
noncomputable section
variable {ι : Type*} [DecidableEq ι]
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def Downward (F : Finset (Finset ι)) : Prop := ∀ S∈F, ∀ B⊆S, B∈F

theorem families_disjoint (F : Finset (Finset ι)) :
    (F:Set (Finset ι)).PairwiseDisjoint partitions := by
  intro S hS T hT hne
  apply disjoint_left.mpr
  intro p hp hq
  exact hne ((mem_filter.mp hp).2.2.2.symm.trans (mem_filter.mp hq).2.2.2)

theorem family_subset (F : Finset (Finset ι)) (hF : Downward F) :
    F.biUnion partitions ⊆ (F.filter (fun B ↦ B.Nonempty)).powerset := by
  intro p hp
  obtain ⟨S,hS,hp⟩ := mem_biUnion.mp hp
  apply mem_powerset.mpr
  intro B hB
  exact mem_filter.mpr ⟨hF S hS B (block_subset hp hB),block_nonempty hp hB⟩

theorem product_bound (m : Finset ι → ℝ) (hm : m ∅=1)
    (F : Finset (Finset ι)) (hF : Downward F) {t : ℝ} (ht : 0≤t) :
    (∑ S∈F, t^S.card*|m S|)≤
      ∏ B∈F.filter (fun B ↦ B.Nonempty), (1+t^B.card*|cumulant m B|) := by
  calc
    _ ≤ ∑ S∈F, ∑ p∈partitions S, ∏ B∈p, (t^B.card*|cumulant m B|) := by
      apply sum_le_sum
      intro S hS
      rw [moment_partition_expansion m hm S]
      apply (mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (pow_nonneg ht _)).trans_eq
      rw [mul_sum]
      apply sum_congr rfl
      intro p hp
      rw [partition_power hp,abs_prod,prod_mul_distrib]
    _ = ∑ p∈F.biUnion partitions, ∏ B∈p, (t^B.card*|cumulant m B|) :=
      (sum_biUnion (families_disjoint F)).symm
    _ ≤ ∑ p∈(F.filter (fun B ↦ B.Nonempty)).powerset,
        ∏ B∈p, (t^B.card*|cumulant m B|) :=
      sum_le_sum_of_subset_of_nonneg (family_subset F hF) (fun p _ _ ↦ prod_nonneg (fun B _ ↦ by positivity))
    _ = _ := (prod_one_add _).symm

theorem exponential_bound (m : Finset ι → ℝ) (hm : m ∅=1)
    (hcenter : ∀ i, m {i}=0) (F : Finset (Finset ι)) (hF : Downward F)
    {t : ℝ} (ht : 0≤t) :
    (∑ S∈F, t^S.card*|m S|)≤
      Real.exp (∑ B∈F.filter (fun B ↦ 2≤B.card), t^B.card*|cumulant m B|) := by
  apply (product_bound m hm F hF ht).trans
  have hp : (∏ B∈F.filter (fun B ↦ B.Nonempty), (1+t^B.card*|cumulant m B|))≤
      ∏ B∈F.filter (fun B ↦ B.Nonempty), Real.exp (t^B.card*|cumulant m B|) := by
    apply prod_le_prod₀ (fun B _ ↦ by positivity)
    intro B hB
    linarith [Real.add_one_le_exp (t^B.card*|cumulant m B|)]
  apply hp.trans_eq
  rw [← Real.exp_sum]
  congr 1
  symm
  apply sum_subset
  · intro B hB
    obtain ⟨hB,hcard⟩ := mem_filter.mp hB
    exact mem_filter.mpr ⟨hB,card_pos.mp (by omega)⟩
  · intro B hB hn
    have hc : B.card=1 := by
      have hpos := card_pos.mpr (mem_filter.mp hB).2
      have hn' : ¬2≤B.card := fun h ↦ hn (mem_filter.mpr ⟨(mem_filter.mp hB).1,h⟩)
      omega
    obtain ⟨i,rfl⟩ := card_eq_one.mp hc
    simp [cumulant_singleton,hcenter]

/-- Removing the empty partition gives the e^activity-1 quantity used in total variation. -/
theorem nonempty_exponential_bound (m : Finset ι → ℝ) (hm : m ∅=1)
    (hcenter : ∀ i, m {i}=0) (F : Finset (Finset ι)) (hF : Downward F) (hempty : ∅∈F)
    {t : ℝ} (ht : 0≤t) :
    (∑ S∈F.erase ∅, t^S.card*|m S|)≤
      Real.exp (∑ B∈F.filter (fun B ↦ 2≤B.card), t^B.card*|cumulant m B|)-1 := by
  have h := exponential_bound m hm hcenter F hF ht
  rw [← sum_erase_add _ _ hempty] at h
  simp only [card_empty,pow_zero,hm,abs_one,mul_one] at h
  linarith

end
end PaperC.Prel8.CumulantFamilyEnvelope
