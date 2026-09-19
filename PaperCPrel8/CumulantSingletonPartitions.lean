import PaperCPrel8.FiniteCumulantPartitions

/-! # Removing a singleton block from a finite cumulant partition -/
namespace PaperC.Prel8.CumulantSingletonPartitions
open Finset FiniteCumulantPartitions
noncomputable section
variable {ι : Type*} [DecidableEq ι]
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem mem_partitions_iff {S : Finset ι} {p : Finset (Finset ι)} :
    p∈partitions S ↔ (p:Set (Finset ι)).PairwiseDisjoint id ∧ ∅∉p ∧ p.biUnion id=S := by
  constructor
  · exact fun h ↦ (mem_filter.mp h).2
  · intro h
    refine mem_filter.mpr ⟨mem_powerset.mpr ?_,h⟩
    intro B hB
    apply mem_powerset.mpr
    intro x hx
    rw [← h.2.2]
    exact mem_biUnion.mpr ⟨B,hB,hx⟩

theorem insert_singleton {S : Finset ι} {p : Finset (Finset ι)} (hp : p∈partitions S)
    {i : ι} (hi : i∉S) : insert {i} p∈partitions (insert i S) := by
  apply mem_partitions_iff.mpr
  refine ⟨?_,?_,?_⟩
  · intro B hB D hD hne
    rcases mem_insert.mp hB with rfl|hB <;> rcases mem_insert.mp hD with rfl|hD
    · exact False.elim (hne rfl)
    · apply disjoint_left.mpr
      intro x hx hxD
      have hx' := mem_singleton.mp hx
      exact hi (hx' ▸ block_subset hp hD hxD)
    · apply disjoint_left.mpr
      intro x hxB hx
      have hx' := mem_singleton.mp hx
      exact hi (hx' ▸ block_subset hp hB hxB)
    · exact (mem_partitions_iff.mp hp).1 hB hD hne
  · simp only [mem_insert,not_or]
    exact ⟨(singleton_ne_empty i).symm,(mem_partitions_iff.mp hp).2.1⟩
  · rw [biUnion_insert,(mem_partitions_iff.mp hp).2.2]
    simp

theorem erase_singleton {S : Finset ι} {p : Finset (Finset ι)} (hp : p∈partitions S)
    {i : ι} (hi : {i}∈p) : p.erase {i}∈partitions (S.erase i) := by
  apply mem_partitions_iff.mpr
  refine ⟨?_,?_,?_⟩
  · intro B hB D hD hne
    exact (mem_partitions_iff.mp hp).1 (mem_of_mem_erase hB) (mem_of_mem_erase hD) hne
  · exact fun he ↦ (mem_partitions_iff.mp hp).2.1 (mem_of_mem_erase he)
  · ext x
    constructor
    · intro hx
      obtain ⟨B,hB,hxB⟩ := mem_biUnion.mp hx
      have hd := (mem_partitions_iff.mp hp).1 (mem_of_mem_erase hB) hi (mem_erase.mp hB).1
      apply mem_erase.mpr
      refine ⟨?_,block_subset hp (mem_of_mem_erase hB) hxB⟩
      intro he
      exact disjoint_left.mp hd hxB (by simp [he])
    · intro hx
      have hxs : x∈p.biUnion id := by rw [(mem_partitions_iff.mp hp).2.2]; exact (mem_erase.mp hx).2
      obtain ⟨B,hB,hxB⟩ := mem_biUnion.mp hxs
      apply mem_biUnion.mpr
      refine ⟨B,mem_erase.mpr ⟨?_,hB⟩,hxB⟩
      intro he
      exact (mem_erase.mp hx).1 (mem_singleton.mp (he ▸ hxB))

theorem singleton_not_mem_erased_partition {S : Finset ι} {p : Finset (Finset ι)} {i : ι}
    (hp : p∈partitions (S.erase i)) : {i}∉p := by
  intro hi
  exact (notMem_erase i S) (block_subset hp hi (mem_singleton_self i))

/-- The partition sum with a specified singleton block reduces to the erased-site moment. -/
theorem singleton_partition_sum (S : Finset ι) {i : ι} (hi : i∈S) (f : Finset ι → ℝ) :
    (∑ p∈(partitions S).filter (fun p ↦ {i}∈p), ∏ B∈p.erase {i}, f B)=
      ∑ p∈partitions (S.erase i), ∏ B∈p, f B := by
  apply sum_bij (fun p _ ↦ p.erase {i})
  · intro p hp
    exact erase_singleton (mem_filter.mp hp).1 (mem_filter.mp hp).2
  · intro p hp q hq he
    have hp' := insert_erase (mem_filter.mp hp).2
    have hq' := insert_erase (mem_filter.mp hq).2
    rw [← hp',← hq',he]
  · intro p hp
    refine ⟨insert {i} p,mem_filter.mpr ⟨?_,mem_insert_self _ _⟩,?_⟩
    · simpa only [insert_erase hi] using insert_singleton hp (notMem_erase i S)
    · exact erase_insert (singleton_not_mem_erased_partition hp)
  · intro p hp
    rfl

end
end PaperC.Prel8.CumulantSingletonPartitions
