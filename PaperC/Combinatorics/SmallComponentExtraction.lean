import PaperC.Combinatorics.PinnedGraphResolution

set_option maxHeartbeats 800000

/-!
# Extraction of uniformly small graph components

This file isolates the elementary counting step at the start of the proof
of Theorem 8.1.  If a finite family has bounded total mass, only few members
can have size strictly larger than a prescribed cutoff.  Consequently, a
large enough family contains a prescribed number of members of uniformly
bounded size.

The final statements specialize the generic estimate to connected
components.  Their supports are disjoint, so the total support size of any
subfamily is bounded by the number of vertices of the ambient graph.
-/

namespace PaperC
namespace SmallComponentExtraction

open SimpleGraph
open PinnedGraphResolution

section FiniteFamilies

variable {ι : Type*}

/-- Members of `family` whose assigned size is at most `K`. -/
def smallMembers
    (family : Finset ι) (size : ι → ℕ) (K : ℕ) : Finset ι :=
  family.filter fun i ↦ size i ≤ K

/-- Members of `family` whose assigned size is strictly larger than `K`. -/
def largeMembers
    (family : Finset ι) (size : ι → ℕ) (K : ℕ) : Finset ι :=
  family.filter fun i ↦ K < size i

@[simp]
theorem mem_smallMembers
    {family : Finset ι} {size : ι → ℕ} {K : ℕ} {i : ι} :
    i ∈ smallMembers family size K ↔ i ∈ family ∧ size i ≤ K := by
  simp [smallMembers]

@[simp]
theorem mem_largeMembers
    {family : Finset ι} {size : ι → ℕ} {K : ℕ} {i : ι} :
    i ∈ largeMembers family size K ↔ i ∈ family ∧ K < size i := by
  simp [largeMembers]

/-- The small and large members give an exact partition of the family. -/
theorem smallMembers_union_largeMembers
    [DecidableEq ι]
    (family : Finset ι) (size : ι → ℕ) (K : ℕ) :
    smallMembers family size K ∪ largeMembers family size K = family := by
  ext i
  simp only [Finset.mem_union, mem_smallMembers, mem_largeMembers]
  constructor
  · rintro (⟨hi, _⟩ | ⟨hi, _⟩) <;> exact hi
  · intro hi
    by_cases hsmall : size i ≤ K
    · exact Or.inl ⟨hi, hsmall⟩
    · exact Or.inr ⟨hi, Nat.lt_of_not_ge hsmall⟩

/-- No member can lie on both sides of the size cutoff. -/
theorem disjoint_smallMembers_largeMembers
    (family : Finset ι) (size : ι → ℕ) (K : ℕ) :
    Disjoint (smallMembers family size K) (largeMembers family size K) := by
  rw [Finset.disjoint_left]
  intro i hiSmall hiLarge
  have hsmall := (mem_smallMembers.mp hiSmall).2
  have hlarge := (mem_largeMembers.mp hiLarge).2
  omega

/-- Cardinality identity associated with the small/large partition. -/
theorem card_smallMembers_add_card_largeMembers
    (family : Finset ι) (size : ι → ℕ) (K : ℕ) :
    (smallMembers family size K).card +
        (largeMembers family size K).card =
      family.card := by
  simpa [smallMembers, largeMembers] using
    (Finset.filter_card_add_filter_neg_card_eq_card
      (s := family) (fun i ↦ size i ≤ K))

/--
Every large member contributes at least `K + 1` to the total mass.
This is the quantitative pigeonhole estimate used in Theorem 8.1.
-/
theorem card_largeMembers_mul_succ_le_sum
    (family : Finset ι) (size : ι → ℕ) (K : ℕ) :
    (largeMembers family size K).card * (K + 1) ≤
      ∑ i ∈ family, size i := by
  calc
    (largeMembers family size K).card * (K + 1) =
        ∑ i ∈ largeMembers family size K, (K + 1) := by
          simp
    _ ≤ ∑ i ∈ largeMembers family size K, size i := by
      apply Finset.sum_le_sum
      intro i hi
      have hlarge := (mem_largeMembers.mp hi).2
      omega
    _ ≤ ∑ i ∈ family, size i := by
      apply Finset.sum_le_sum_of_subset
      intro i hi
      exact (mem_largeMembers.mp hi).1

/-- With total mass at most `budget`, at most `budget / (K + 1)` members are large. -/
theorem card_largeMembers_le_budget_div
    (family : Finset ι) (size : ι → ℕ) (K budget : ℕ)
    (hsum : (∑ i ∈ family, size i) ≤ budget) :
    (largeMembers family size K).card ≤ budget / (K + 1) := by
  rw [Nat.le_div_iff_mul_le (by omega)]
  exact
    (card_largeMembers_mul_succ_le_sum family size K).trans hsum

/--
If the family is larger than the maximum possible large part by `target`,
then at least `target` of its members have size at most `K`.
-/
theorem target_le_card_smallMembers
    (family : Finset ι) (size : ι → ℕ) (K budget target : ℕ)
    (hsum : (∑ i ∈ family, size i) ≤ budget)
    (hfamily : target + budget / (K + 1) ≤ family.card) :
    target ≤ (smallMembers family size K).card := by
  have hlarge :
      (largeMembers family size K).card ≤ budget / (K + 1) :=
    card_largeMembers_le_budget_div family size K budget hsum
  have hpartition :=
    card_smallMembers_add_card_largeMembers family size K
  omega

end FiniteFamilies

section GraphComponents

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/--
The support sizes of any finite subfamily of connected components sum to
at most the cardinality of the ambient vertex set.
-/
theorem sum_component_support_sizes_le
    (family : Finset G.ConnectedComponent) :
    (∑ C ∈ family, Fintype.card C.supp) ≤ Fintype.card V := by
  calc
    (∑ C ∈ family, Fintype.card C.supp) ≤
        ∑ C : G.ConnectedComponent, Fintype.card C.supp := by
      apply Finset.sum_le_sum_of_subset
      exact Finset.subset_univ family
    _ = Fintype.card V :=
      sum_card_component_support G

/--
Paper-facing extraction lemma.  A component family with enough members
beyond the quotient bound contains `target` components supported on at most
`K` vertices each.
-/
theorem target_small_components
    (family : Finset G.ConnectedComponent) (K target : ℕ)
    (hfamily :
      target + Fintype.card V / (K + 1) ≤ family.card) :
    target ≤
      (smallMembers family (fun C ↦ Fintype.card C.supp) K).card := by
  classical
  apply
    target_le_card_smallMembers family
      (fun C ↦ Fintype.card C.supp) K (Fintype.card V) target
  · exact sum_component_support_sizes_le G family
  · exact hfamily

end GraphComponents

end SmallComponentExtraction
end PaperC
