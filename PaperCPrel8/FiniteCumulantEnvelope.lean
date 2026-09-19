import PaperCPrel8.FiniteCumulantPartitions

/-! # Finite product envelope for cumulant partitions

Dropping disjointness embeds the partition sum in a finite product of
(1+block weight). No infinite cumulant expansion is used.
-/
namespace PaperC.Prel8.FiniteCumulantEnvelope
open Finset FiniteCumulantPartitions
open IndependentThinning ArratiaGoldsteinGordonInput V282.SteinFiniteExpectation
noncomputable section
variable {ι Ω : Type*} [DecidableEq ι] [Fintype Ω]
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem partition_families_disjoint (I : Finset ι) :
    (I.powerset:Set (Finset ι)).PairwiseDisjoint partitions := by
  intro S hS T hT hne
  apply disjoint_left.mpr
  intro p hp hq
  exact hne ((mem_filter.mp hp).2.2.2.symm.trans (mem_filter.mp hq).2.2.2)

theorem partition_family_subset (I : Finset ι) :
    I.powerset.biUnion partitions ⊆ (I.powerset.filter (fun B ↦ B.Nonempty)).powerset := by
  intro p hp
  obtain ⟨S,hS,hp⟩ := mem_biUnion.mp hp
  apply mem_powerset.mpr
  intro B hB
  exact mem_filter.mpr ⟨mem_powerset.mpr ((block_subset hp hB).trans (mem_powerset.mp hS)),block_nonempty hp hB⟩

/-- All weighted centered moments are bounded by a finite product of cumulant weights. -/
theorem moment_product_bound (m : Finset ι → ℝ) (hm : m ∅=1)
    (I : Finset ι) {t : ℝ} (ht : 0≤t) :
    (∑ S∈I.powerset, t^S.card*|m S|)≤
      ∏ B∈I.powerset.filter (fun B ↦ B.Nonempty), (1+t^B.card*|cumulant m B|) := by
  calc
    _ ≤ ∑ S∈I.powerset, ∑ p∈partitions S, ∏ B∈p, (t^B.card*|cumulant m B|) := by
      apply sum_le_sum
      intro S hS
      rw [moment_partition_expansion m hm S]
      apply (mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (pow_nonneg ht _)).trans_eq
      rw [mul_sum]
      apply sum_congr rfl
      intro p hp
      rw [partition_power hp,abs_prod,prod_mul_distrib]
    _ = ∑ p∈I.powerset.biUnion partitions, ∏ B∈p, (t^B.card*|cumulant m B|) :=
      (sum_biUnion (partition_families_disjoint I)).symm
    _ ≤ ∑ p∈(I.powerset.filter (fun B ↦ B.Nonempty)).powerset,
        ∏ B∈p, (t^B.card*|cumulant m B|) :=
      sum_le_sum_of_subset_of_nonneg (partition_family_subset I) (fun p _ _ ↦ prod_nonneg (fun B _ ↦ by positivity))
    _ = _ := (prod_one_add _).symm

/-- The exponential envelope uses only blocks of size at least two when singletons are centered. -/
theorem moment_exponential_bound (m : Finset ι → ℝ) (hm : m ∅=1)
    (hcenter : ∀ i, m {i}=0) (I : Finset ι) {t : ℝ} (ht : 0≤t) :
    (∑ S∈I.powerset, t^S.card*|m S|)≤
      Real.exp (∑ B∈I.powerset.filter (fun B ↦ 2≤B.card), t^B.card*|cumulant m B|) := by
  apply (moment_product_bound m hm I ht).trans
  have hp : (∏ B∈I.powerset.filter (fun B ↦ B.Nonempty), (1+t^B.card*|cumulant m B|))≤
      ∏ B∈I.powerset.filter (fun B ↦ B.Nonempty), Real.exp (t^B.card*|cumulant m B|) := by
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

def centeredMoment (mu : FinitePMF Ω) (X : ι → Ω → ℝ) (S : Finset ι) : ℝ :=
  finitePMFExpectation mu (fun w ↦ ∏ i∈S, (X i w-finitePMFExpectation mu (X i)))

/-- Joint cumulants of order at least two, defined by the finite centered moment recursion. -/
def jointCumulant (mu : FinitePMF Ω) (X : ι → Ω → ℝ) (S : Finset ι) : ℝ :=
  cumulant (centeredMoment mu X) S

theorem centeredMoment_empty (mu : FinitePMF Ω) (X : ι → Ω → ℝ) : centeredMoment mu X ∅=1 := by
  simp [centeredMoment,expectation_const]

theorem centeredMoment_singleton (mu : FinitePMF Ω) (X : ι → Ω → ℝ) (i : ι) :
    centeredMoment mu X {i}=0 := by
  simp [centeredMoment,expectation_sub,expectation_const]

theorem polynomial_expansion (mu : FinitePMF Ω) (X : ι → Ω → ℝ) (I : Finset ι) (t : ℝ) :
    finitePMFExpectation mu (fun w ↦ ∏ i∈I, (1+t*(X i w-finitePMFExpectation mu (X i))))=
      ∑ S∈I.powerset, t^S.card*centeredMoment mu X S := by
  simp_rw [prod_one_add,prod_mul_distrib,prod_const]
  rw [expectation_finset_sum]
  apply sum_congr rfl
  intro S hS
  exact expectation_const_mul _ _ _

/-- G.8's polynomial inequality, for the actual law of arbitrary real random variables. -/
theorem polynomial_envelope (mu : FinitePMF Ω) (X : ι → Ω → ℝ) (I : Finset ι)
    {t : ℝ} (ht : 0≤t) :
    |finitePMFExpectation mu (fun w ↦ ∏ i∈I, (1+t*(X i w-finitePMFExpectation mu (X i))))|≤
      Real.exp (∑ S∈I.powerset.filter (fun S ↦ 2≤S.card), t^S.card*|jointCumulant mu X S|) := by
  rw [polynomial_expansion]
  apply (abs_sum_le_sum_abs _ _).trans
  simp only [abs_mul,abs_of_nonneg (pow_nonneg ht _)]
  exact moment_exponential_bound _ (centeredMoment_empty mu X) (centeredMoment_singleton mu X) I ht

end
end PaperC.Prel8.FiniteCumulantEnvelope
