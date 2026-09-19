import PaperCPrel8.CategoricalMomentExpansion

/-! # The finite categorical total-variation bound of G.8 -/
namespace PaperC.Prel8.CategoricalCumulantBound
open Finset CategoricalTransversals CategoricalMomentExpansion FiniteCumulantEnvelope
open IndependentThinning ArratiaGoldsteinGordonInput V282.SteinFiniteExpectation
open V282.FiniteFieldTotalVariation
noncomputable section
variable {ι α Ω : Type*} [Fintype ι] [Fintype α] [Fintype Ω] [DecidableEq ι] [DecidableEq α]
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def activity (mu : FinitePMF Ω) (Y : ι → Ω → Option α) : ℝ :=
  ∑ S∈transversals.filter (fun S ↦ 2≤S.card),
    (2:ℝ)^(S.card-1)*|jointCumulant mu (indicator Y) S|

theorem direction_l1 (a : α) : (∑ y : Option α, |direction a y|)=2 := by
  rw [Fintype.sum_option]
  simp only [direction,delta,reduceCtorEq,ite_true,ite_false,zero_sub,sub_zero,abs_neg,abs_one]
  have hh : (∑ y : α, |if a=y then (1:ℝ) else 0|)=1 := by
    rw [sum_eq_single a]
    · simp
    · intro y hy hn
      simp [Ne.symm hn]
    · simp
  simp only [Option.some.injEq]
  linarith

theorem tensor_l1 (mu : FinitePMF Ω) (Y : ι → Ω → Option α)
    {S : Finset (ι×α)} (hS : Transversal S) :
    (∑ y : ι → Option α, |tensor (marginal mu Y) S y|)=(2:ℝ)^S.card := by
  unfold tensor
  simp_rw [abs_prod]
  have he := (Fintype.prod_sum (fun (i:ι) (y:Option α) ↦ abs (match choice S i with | none => marginal mu Y i y | some a => direction a y))).symm
  convert he.trans ?_ using 1
  calc
    _ = ∏ i : ι, match choice S i with | none => (1:ℝ) | some _ => 2 := by
      apply prod_congr rfl
      intro i hi
      cases hc : choice S i with
      | none =>
        simp only [hc]
        have hn (y : Option α) : 0≤marginal mu Y i y := eventProbability_nonneg mu _
        simp_rw [abs_of_nonneg (hn _)]
        exact marginal_sum mu Y i
      | some a => exact direction_l1 a
    _ = ∏ a∈graph (choice S), (2:ℝ) := (prod_graph (choice S) (fun _ : ι×α ↦ (2:ℝ))).symm
    _ = _ := by rw [graph_choice hS]; simp

theorem total_variation_moment_bound (mu : FinitePMF Ω) (Y : ι → Ω → Option α) :
    massTotalVariation (fun y ↦ eventProbability mu (fun w ↦ (fun i ↦ Y i w)=y))
      (fun y ↦ ∏ i, marginal mu Y i (y i))≤
      (∑ S∈transversals.erase ∅, (2:ℝ)^S.card*|centeredMoment mu (indicator Y) S|)/2 := by
  unfold massTotalVariation
  rw [tsum_fintype]
  have hb (y : ι → Option α) :
      |eventProbability mu (fun w ↦ (fun i ↦ Y i w)=y)-(∏ i, marginal mu Y i (y i))|≤
        ∑ S∈transversals.erase ∅, |centeredMoment mu (indicator Y) S*tensor (marginal mu Y) S y| := by
    rw [centered_source_expansion]
    exact abs_sum_le_sum_abs _ _
  have hs := sum_le_sum (s:=univ) (fun y _ ↦ hb y)
  apply (mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ)≤2⁻¹)).trans_eq
  rw [sum_comm]
  simp_rw [abs_mul,← mul_sum]
  have hh : (∑ S∈transversals.erase ∅, |centeredMoment mu (indicator Y) S| *
      ∑ y : ι → Option α, |tensor (marginal mu Y) S y|)=
      ∑ S∈transversals.erase ∅, (2:ℝ)^S.card*|centeredMoment mu (indicator Y) S| := by
    apply sum_congr rfl
    intro S hS
    rw [tensor_l1 mu Y (mem_filter.mp (mem_of_mem_erase hS)).2,mul_comm]
  rw [hh]
  ring

theorem twice_activity (mu : FinitePMF Ω) (Y : ι → Ω → Option α) :
    2*activity mu Y=∑ S∈transversals.filter (fun S ↦ 2≤S.card),
      (2:ℝ)^S.card*|jointCumulant mu (indicator Y) S| := by
  unfold activity
  rw [mul_sum]
  apply sum_congr rfl
  intro S hS
  have hc := (mem_filter.mp hS).2
  have hp : (2:ℝ)^S.card=2*2^(S.card-1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hp]
  ring

theorem source_mass_one (mu : FinitePMF Ω) (Y : ι → Ω → Option α) :
    HasSum (fun y ↦ eventProbability mu (fun w ↦ (fun i ↦ Y i w)=y)) 1 := by
  have hh : (∑ y : ι → Option α, eventProbability mu (fun w ↦ (fun i ↦ Y i w)=y))=1 := by
    unfold eventProbability
    rw [sum_comm]
    apply Eq.trans _ mu.sum_prob
    apply sum_congr rfl
    intro w hw
    rw [sum_eq_single (fun i ↦ Y i w)]
    · simp
    · intro y hy hn
      simp [Ne.symm hn]
    · simp
  simpa only [hh] using hasSum_fintype (fun y : ι → Option α ↦ eventProbability mu (fun w ↦ (fun i ↦ Y i w)=y))

theorem product_mass_one (mu : FinitePMF Ω) (Y : ι → Ω → Option α) :
    HasSum (fun y : ι → Option α ↦ ∏ i, marginal mu Y i (y i)) 1 := by
  have hh : (∑ y : ι → Option α, ∏ i, marginal mu Y i (y i))=1 := by
    rw [← Fintype.prod_sum]
    simp only [marginal_sum,prod_const_one]
  simpa only [hh] using hasSum_fintype (fun y : ι → Option α ↦ ∏ i, marginal mu Y i (y i))

/-- G.8, on the original categorical law and its product of actual marginals. -/
theorem categorical_cumulant_tv (mu : FinitePMF Ω) (Y : ι → Ω → Option α) :
    massTotalVariation (fun y ↦ eventProbability mu (fun w ↦ (fun i ↦ Y i w)=y))
      (fun y ↦ ∏ i, marginal mu Y i (y i))≤min 1 ((Real.exp (2*activity mu Y)-1)/2) := by
  apply le_min
  · exact massTotalVariation_le_one (source_mass_one mu Y) (product_mass_one mu Y)
      (fun _ ↦ eventProbability_nonneg _ _) (fun _ ↦ prod_nonneg (fun _ _ ↦ eventProbability_nonneg _ _))
  · apply (total_variation_moment_bound mu Y).trans
    apply div_le_div_of_nonneg_right _ (by norm_num)
    have h := CumulantFamilyEnvelope.nonempty_exponential_bound _ (centeredMoment_empty mu (indicator Y))
      (centeredMoment_singleton mu (indicator Y)) transversals transversals_downward empty_mem (by norm_num : (0:ℝ)≤2)
    simpa only [twice_activity,jointCumulant] using h

end
end PaperC.Prel8.CategoricalCumulantBound
