import PaperCPrel8.PalmVoidPolynomial
import Mathlib.Data.Finset.Powerset

/-! # Finite moment/cumulant partitions, with no analytic series -/
namespace PaperC.Prel8.FiniteCumulantPartitions
open Finset
noncomputable section
variable {ι : Type*} [DecidableEq ι]
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def partitions (S : Finset ι) : Finset (Finset (Finset ι)) :=
  S.powerset.powerset.filter (fun p ↦ (p:Set (Finset ι)).PairwiseDisjoint id ∧
    ∅∉p ∧ p.biUnion id=S)

def properPartitions (S : Finset ι) : Finset (Finset (Finset ι)) :=
  (partitions S).erase {S}

theorem block_subset {S B : Finset ι} {p : Finset (Finset ι)}
    (hp : p∈partitions S) (hB : B∈p) : B⊆S :=
  mem_powerset.mp (mem_powerset.mp (mem_filter.mp hp).1 hB)

theorem block_nonempty {S B : Finset ι} {p : Finset (Finset ι)}
    (hp : p∈partitions S) (hB : B∈p) : B.Nonempty := by
  apply nonempty_iff_ne_empty.mpr
  intro he
  exact (mem_filter.mp hp).2.2.1 (he ▸ hB)

theorem partition_with_full_block {S : Finset ι} {p : Finset (Finset ι)}
    (hp : p∈partitions S) (hS : S∈p) : p={S} := by
  apply eq_singleton_iff_unique_mem.mpr
  refine ⟨hS,?_⟩
  intro B hB
  by_contra hne
  have hd := (mem_filter.mp hp).2.1 hB hS hne
  obtain ⟨x,hx⟩ := block_nonempty hp hB
  exact disjoint_left.mp hd hx (block_subset hp hB hx)

theorem proper_block_ssubset {S B : Finset ι} {p : Finset (Finset ι)}
    (hp : p∈properPartitions S) (hB : B∈p) : B⊂S := by
  obtain ⟨hne,hp⟩ := mem_erase.mp hp
  apply ssubset_iff_subset_ne.mpr
  refine ⟨block_subset hp hB,?_⟩
  intro he
  exact hne (partition_with_full_block hp (he ▸ hB))

theorem singleton_partition {S : Finset ι} (hS : S.Nonempty) : {S}∈partitions S := by
  simp [partitions,Ne.symm hS.ne_empty]

theorem partitions_empty : partitions (∅:Finset ι)={∅} := by
  ext p
  simp only [partitions,mem_filter,mem_powerset,powerset_empty,subset_singleton_iff,mem_singleton]
  constructor
  · rintro ⟨h,hd,he,hu⟩
    rcases h with h|h
    · exact h
    · simp [h] at he
  · rintro rfl
    simp

/-- Triangular finite definition of joint cumulants from a prescribed moment table. -/
def cumulant (moment : Finset ι → ℝ) (S : Finset ι) : ℝ :=
  if S=∅ then 0 else moment S-
    ∑ p : properPartitions S, ∏ B : p.val, cumulant moment B.val
termination_by S.card
decreasing_by exact card_lt_card (proper_block_ssubset p.property B.property)

theorem cumulant_empty (m : Finset ι → ℝ) : cumulant m ∅=0 := by
  rw [cumulant]
  simp

theorem moment_partition_expansion (m : Finset ι → ℝ) (hm : m ∅=1) (S : Finset ι) :
    m S=∑ p∈partitions S, ∏ B∈p, cumulant m B := by
  by_cases hS : S=∅
  · subst S
    simp [partitions_empty,hm]
  · have hs := singleton_partition (nonempty_iff_ne_empty.mpr hS)
    have he : (∑ p : properPartitions S, ∏ B : p.val, cumulant m B)=
        ∑ p∈properPartitions S, ∏ B∈p, cumulant m B := by
      simp only [prod_coe_sort]
      exact sum_coe_sort (properPartitions S) (fun p ↦ ∏ B∈p, cumulant m B)
    have hc : cumulant m S=m S-∑ p∈properPartitions S, ∏ B∈p, cumulant m B := by
      rw [cumulant,if_neg hS,he]
    rw [← sum_erase_add _ _ hs]
    simp only [prod_singleton]
    change m S=(∑ p∈properPartitions S, ∏ B∈p, cumulant m B)+cumulant m S
    linarith

theorem partitions_singleton (i : ι) : partitions {i}={{{i}}} := by
  apply eq_singleton_iff_unique_mem.mpr
  refine ⟨singleton_partition (singleton_nonempty _),?_⟩
  intro p hp
  have hu := (mem_filter.mp hp).2.2.2
  have hi : i∈p.biUnion id := by rw [hu]; simp
  obtain ⟨B,hB,hiB⟩ := mem_biUnion.mp hi
  have hBs : B={i} := eq_singleton_iff_unique_mem.mpr
    ⟨hiB,fun x hx ↦ mem_singleton.mp (block_subset hp hB hx)⟩
  exact partition_with_full_block hp (hBs ▸ hB)

theorem cumulant_singleton (m : Finset ι → ℝ) (i : ι) : cumulant m {i}=m {i} := by
  have hp : properPartitions ({i}:Finset ι)=∅ := by rw [properPartitions,partitions_singleton]; simp
  haveI : IsEmpty (properPartitions ({i}:Finset ι)) := ⟨fun p ↦ by
    exact notMem_empty p.val (by simpa only [hp] using p.property)⟩
  rw [cumulant]
  simp only [singleton_ne_empty,ite_false,Finset.univ_eq_empty,Finset.sum_empty,sub_zero]

/-- Disjoint blocks preserve the total power weight exactly. -/
theorem partition_power {S : Finset ι} {p : Finset (Finset ι)}
    (hp : p∈partitions S) (t : ℝ) : t^S.card=∏ B∈p, t^B.card := by
  rw [← (mem_filter.mp hp).2.2.2,card_biUnion (mem_filter.mp hp).2.1,prod_pow_eq_pow_sum]
  rfl

end
end PaperC.Prel8.FiniteCumulantPartitions
