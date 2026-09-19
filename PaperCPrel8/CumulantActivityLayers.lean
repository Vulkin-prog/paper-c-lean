import PaperCPrel8.CategoricalCumulantBound

/-! # The exact pair and higher-order layers of the categorical activity -/
namespace PaperC.Prel8.CumulantActivityLayers
open Finset Filter Topology CategoricalCumulantBound CategoricalTransversals
open CategoricalMomentExpansion FiniteCumulantEnvelope FiniteCumulantPartitions
open ArratiaGoldsteinGordonInput IndependentThinning V282.SteinFiniteExpectation
noncomputable section
variable {ι α Ω : Type*} [Fintype ι] [Fintype α] [Fintype Ω] [DecidableEq ι] [DecidableEq α]
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def pairActivity (mu : FinitePMF Ω) (Y : ι → Ω → Option α) : ℝ :=
  ∑ S∈transversals.filter (fun S ↦ S.card=2), (2:ℝ)^(S.card-1)*|jointCumulant mu (indicator Y) S|

def higherActivity (mu : FinitePMF Ω) (Y : ι → Ω → Option α) : ℝ :=
  ∑ S∈transversals.filter (fun S ↦ 3≤S.card), (2:ℝ)^(S.card-1)*|jointCumulant mu (indicator Y) S|

theorem activity_split (mu : FinitePMF Ω) (Y : ι → Ω → Option α) :
    activity mu Y=pairActivity mu Y+higherActivity mu Y := by
  unfold activity pairActivity higherActivity
  simp only [sum_filter]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro S hS
  split_ifs <;> first | omega | simp_all

theorem pair_nonneg (mu : FinitePMF Ω) (Y : ι → Ω → Option α) : 0≤pairActivity mu Y :=
  sum_nonneg (fun _ _ ↦ by positivity)

theorem higher_nonneg (mu : FinitePMF Ω) (Y : ι → Ω → Option α) : 0≤higherActivity mu Y :=
  sum_nonneg (fun _ _ ↦ by positivity)

/-- For two distinct sites the centered recursive cumulant is exactly their centered product moment. -/
theorem cumulant_card_two {β : Type*} [DecidableEq β] (m : Finset β → ℝ)
    (hc : ∀ i, m {i}=0) {S : Finset β} (hS : S.card=2) : cumulant m S=m S := by
  have hne : S≠∅ := by intro he; simp [he] at hS
  rw [cumulant,if_neg hne]
  suffices he : (∑ p : properPartitions S, ∏ B : p.val, cumulant m B.val)=0 by rw [he,sub_zero]
  apply sum_eq_zero
  intro p hp
  have hpart : p.val∈partitions S := mem_of_mem_erase p.property
  have hu := (mem_filter.mp hpart).2.2.2
  obtain ⟨i,hi⟩ := nonempty_iff_ne_empty.mpr hne
  have hi' : i∈p.val.biUnion id := by rwa [hu]
  obtain ⟨B,hB,hiB⟩ := mem_biUnion.mp hi'
  have hcard : B.card=1 := by
    have hlo := card_pos.mpr (block_nonempty hpart hB)
    have hhi := card_lt_card (proper_block_ssubset p.property hB)
    omega
  obtain ⟨j,hj⟩ := card_eq_one.mp hcard
  apply prod_eq_zero (mem_univ (⟨B,hB⟩ : p.val))
  simp only [hj,cumulant_singleton,hc]

/-- This identifies the pair layer with actual covariances, not a new family of coefficients. -/
theorem pair_cumulant {S : Finset (ι×α)} (hS : S.card=2) (mu : FinitePMF Ω)
    (Y : ι → Ω → Option α) :
    jointCumulant mu (indicator Y) S=centeredMoment mu (indicator Y) S :=
  cumulant_card_two _ (centeredMoment_singleton mu (indicator Y)) hS

/-- The two-point centered moment is the ordinary covariance under the actual law. -/
theorem centered_pair_moment {β : Type*} [DecidableEq β] (mu : FinitePMF Ω)
    (X : β → Ω → ℝ) {a b : β} (hab : a≠b) :
    centeredMoment mu X {a,b}=finitePMFExpectation mu (fun w ↦ X a w*X b w)-
      finitePMFExpectation mu (X a)*finitePMFExpectation mu (X b) := by
  unfold centeredMoment
  simp only [prod_insert (show a∉({b}:Finset β) by simpa using hab),prod_singleton]
  have he (w : Ω) : (X a w-finitePMFExpectation mu (X a))*(X b w-finitePMFExpectation mu (X b))=
      X a w*X b w-X a w*finitePMFExpectation mu (X b)-
        finitePMFExpectation mu (X a)*X b w+
          finitePMFExpectation mu (X a)*finitePMFExpectation mu (X b) := by ring
  simp_rw [he]
  rw [expectation_add,expectation_sub,expectation_sub,expectation_mul_const,expectation_const_mul,expectation_const]
  ring

/-- Once a vanishing pair estimate is available, all divergence lies at orders at least three. -/
theorem higher_diverges_of_pair_tendsto {K P H : ℕ → ℝ}
    (hK : Tendsto K atTop atTop) (hP : Tendsto P atTop (𝓝 0))
    (heq : ∀ n, K n=P n+H n) : Tendsto H atTop atTop := by
  have hh := hK.atTop_add hP.neg
  apply hh.congr
  intro n
  rw [heq n]
  ring

end
end PaperC.Prel8.CumulantActivityLayers
