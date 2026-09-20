import PaperCPrel8.CategoricalCumulantBound

/-! # The positive occupancy polynomial and the lower bound on categorical activity -/
namespace PaperC.Prel8.CategoricalOccupancyEnvelope
open Finset CategoricalTransversals CategoricalMomentExpansion FiniteCumulantEnvelope
open CategoricalCumulantBound IndependentThinning ArratiaGoldsteinGordonInput V282.SteinFiniteExpectation
noncomputable section
variable {ι α Ω : Type*} [Fintype ι] [Fintype α] [Fintype Ω] [DecidableEq ι] [DecidableEq α]
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def occupancy (Y : ι → Ω → Option α) (i : ι) (w : Ω) : ℝ :=
  if Y i w=none then 0 else 1

def polynomial (mu : FinitePMF Ω) (Y : ι → Ω → Option α) (t : ℝ) : ℝ :=
  finitePMFExpectation mu (fun w ↦ ∏ i,
    (1+t*(occupancy Y i w-finitePMFExpectation mu (occupancy Y i))))

theorem occupancy_sum (Y : ι → Ω → Option α) (i : ι) (w : Ω) :
    occupancy Y i w=∑ a, indicator Y (i,a) w := by
  cases h : Y i w <;> simp [occupancy,indicator,delta,h]

theorem centered_occupancy_sum (mu : FinitePMF Ω) (Y : ι → Ω → Option α) (i : ι) (w : Ω) :
    occupancy Y i w-finitePMFExpectation mu (occupancy Y i)=
      ∑ a, (indicator Y (i,a) w-finitePMFExpectation mu (indicator Y (i,a))) := by
  have he : occupancy Y i=(fun w ↦ ∑ a, indicator Y (i,a) w) := funext (occupancy_sum Y i)
  rw [he,expectation_finset_sum,sum_sub_distrib]

theorem polynomial_expansion (mu : FinitePMF Ω) (Y : ι → Ω → Option α) (t : ℝ) :
    polynomial mu Y t=∑ S∈transversals, t^S.card*centeredMoment mu (indicator Y) S := by
  have he (w : Ω) : (∏ i, (1+t*(occupancy Y i w-finitePMFExpectation mu (occupancy Y i))))=
      ∑ S∈transversals, t^S.card*∏ a∈S, (indicator Y a w-finitePMFExpectation mu (indicator Y a)) := by
    have hs (i : ι) : 1+t*(occupancy Y i w-finitePMFExpectation mu (occupancy Y i))=
        ∑ a : Option α, (match a with | none => 1 | some a => t*(indicator Y (i,a) w-finitePMFExpectation mu (indicator Y (i,a)))) := by
      rw [Fintype.sum_option,centered_occupancy_sum,mul_sum]
    simp_rw [hs]
    rw [Fintype.prod_sum,← sum_graph]
    apply sum_congr rfl
    intro f hf
    rw [← prod_const,← prod_mul_distrib,prod_graph]
    apply prod_congr rfl
    intro i hi
    cases f i <;> rfl
  unfold polynomial
  simp_rw [he]
  rw [expectation_finset_sum]
  apply sum_congr rfl
  intro S hS
  exact expectation_const_mul _ _ _

theorem polynomial_envelope (mu : FinitePMF Ω) (Y : ι → Ω → Option α) {t : ℝ} (ht : 0≤t) :
    |polynomial mu Y t|≤Real.exp (∑ S∈transversals.filter (fun S ↦ 2≤S.card),
      t^S.card*|jointCumulant mu (indicator Y) S|) := by
  rw [polynomial_expansion]
  apply (abs_sum_le_sum_abs _ _).trans
  simp only [abs_mul,abs_of_nonneg (pow_nonneg ht _)]
  exact CumulantFamilyEnvelope.exponential_bound _ (centeredMoment_empty mu (indicator Y))
    (centeredMoment_singleton mu (indicator Y)) transversals transversals_downward ht

theorem expectation_strictly_positive (mu : FinitePMF Ω) (f : Ω → ℝ) (hf : ∀ w, 0<f w) :
    0<finitePMFExpectation mu f := by
  have hex : ∃ w, 0<mu.prob w := by
    by_contra h
    push_neg at h
    have hh := sum_nonpos (s:=univ) (fun w _ ↦ h w)
    rw [mu.sum_prob] at hh
    norm_num at hh
  obtain ⟨w,hw⟩ := hex
  exact sum_pos' (fun z _ ↦ mul_nonneg (mu.nonneg z) (hf z).le)
    ⟨w,mem_univ _,mul_pos hw (hf w)⟩

theorem polynomial_two_pos (mu : FinitePMF Ω) (Y : ι → Ω → Option α)
    (hr : ∀ i, 2*finitePMFExpectation mu (occupancy Y i)<1) : 0<polynomial mu Y 2 := by
  apply expectation_strictly_positive
  intro w
  apply prod_pos
  intro i hi
  have hocc : 0≤occupancy Y i w := by unfold occupancy; positivity
  linarith [hr i]

/-- Last assertion of G.8, without introducing within-site cumulants. -/
theorem activity_ge_half_log_polynomial (mu : FinitePMF Ω) (Y : ι → Ω → Option α)
    (hr : ∀ i, 2*finitePMFExpectation mu (occupancy Y i)<1) :
    Real.log (polynomial mu Y 2)/2≤activity mu Y := by
  have hp := polynomial_two_pos mu Y hr
  have h := (le_abs_self (polynomial mu Y 2)).trans (polynomial_envelope mu Y (by norm_num : (0:ℝ)≤2))
  rw [← twice_activity] at h
  have hl := Real.log_le_log hp h
  rw [Real.log_exp] at hl
  linarith

end
end PaperC.Prel8.CategoricalOccupancyEnvelope
