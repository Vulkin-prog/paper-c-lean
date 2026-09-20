import PaperCPrel8.CumulantSingletonPartitions

/-! # Translation of one variable changes only the singleton cumulant -/
namespace PaperC.Prel8.CumulantTranslationTable
open Finset FiniteCumulantPartitions CumulantSingletonPartitions
noncomputable section
variable {ι : Type*} [DecidableEq ι]
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem prod_single_shift {β : Type*} [DecidableEq β] (p : Finset β) (f : β → ℝ) (b : β) (c : ℝ) :
    (∏ x∈p, (f x+if x=b then c else 0))=
      (∏ x∈p, f x)+(if b∈p then c*∏ x∈p.erase b, f x else 0) := by
  by_cases hb : b∈p
  · have he : (∏ x∈p.erase b, (f x+if x=b then c else 0))=∏ x∈p.erase b, f x := by
      apply prod_congr rfl
      intro x hx
      simp [(mem_erase.mp hx).1]
    rw [← mul_prod_erase _ _ hb,he,← mul_prod_erase _ _ hb]
    simp only [if_pos hb,ite_true]
    ring
  · have he : (∏ x∈p, (f x+if x=b then c else 0))=∏ x∈p, f x := by
      apply prod_congr rfl
      intro x hx
      have hn : x≠b := fun he ↦ hb (he ▸ hx)
      simp [hn]
    rw [he,if_neg hb,add_zero]

/-- A moment table determines its finite recursive cumulants uniquely. -/
theorem cumulant_unique (m K : Finset ι → ℝ) (hK : K ∅=0)
    (hexp : ∀ S, m S=∑ p∈partitions S, ∏ B∈p, K B) (S : Finset ι) : cumulant m S=K S := by
  induction S using Finset.strongInductionOn
  rename_i S ih
  by_cases hS : S=∅
  · subst S; rw [cumulant_empty,hK]
  · have hp := singleton_partition (nonempty_iff_ne_empty.mpr hS)
    have hs := hexp S
    rw [← sum_erase_add _ _ hp,prod_singleton] at hs
    have he : (∑ p : properPartitions S, ∏ B : p.val, cumulant m B.val)=
        ∑ p∈properPartitions S, ∏ B∈p, K B := by
      calc
        _ = ∑ p : properPartitions S, ∏ B : p.val, K B.val := by
          apply sum_congr rfl
          intro p hp'
          apply prod_congr rfl
          intro B hB
          exact ih B.val (proper_block_ssubset p.property B.property)
        _ = _ := by
          simp only [prod_coe_sort]
          exact sum_coe_sort (properPartitions S) (fun p ↦ ∏ B∈p, K B)
    rw [cumulant,if_neg hS,he]
    change m S-(∑ p∈(partitions S).erase {S},∏ B∈p,K B)=K S
    linarith

def shiftMoment (m : Finset ι → ℝ) (i : ι) (c : ℝ) (S : Finset ι) : ℝ :=
  m S+if i∈S then c*m (S.erase i) else 0

def shiftCumulant (K : Finset ι → ℝ) (i : ι) (c : ℝ) (S : Finset ι) : ℝ :=
  K S+if S={i} then c else 0

theorem shifted_partition_expansion (m : Finset ι → ℝ) (hm : m ∅=1) (i : ι) (c : ℝ) (S : Finset ι) :
    shiftMoment m i c S=∑ p∈partitions S, ∏ B∈p, shiftCumulant (cumulant m) i c B := by
  simp only [shiftCumulant,prod_single_shift,sum_add_distrib]
  rw [← moment_partition_expansion m hm]
  unfold shiftMoment
  congr 1
  by_cases hi : i∈S
  · rw [if_pos hi]
    rw [← sum_filter]
    rw [← mul_sum,singleton_partition_sum S hi]
    rw [← moment_partition_expansion m hm]
  · rw [if_neg hi]
    symm
    apply sum_eq_zero
    intro p hp
    have hn : {i}∉p := fun h ↦ hi (block_subset hp h (mem_singleton_self i))
    simp [hn]

/-- This is a finite partition identity, independent of analytic generating series. -/
theorem cumulant_shift (m : Finset ι → ℝ) (hm : m ∅=1) (i : ι) (c : ℝ) (S : Finset ι) :
    cumulant (shiftMoment m i c) S=shiftCumulant (cumulant m) i c S := by
  apply cumulant_unique
  · simp [shiftCumulant,cumulant_empty]
  · exact shifted_partition_expansion m hm i c

end
end PaperC.Prel8.CumulantTranslationTable
