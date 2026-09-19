import PaperCPrel8.CategoricalActivityWitness

/-! # The same arithmetic occupancy witness at every fixed nonnegative weight -/
namespace PaperC.Prel8.WeightedActivityWitness
open Finset CategoricalActivityWitness CategoricalOccupancyEnvelope CategoricalCumulantBound
open IndependentThinning ArratiaGoldsteinGordonInput V282.SteinFiniteExpectation
noncomputable section
variable {ι α Ω : Type*} [Fintype ι] [Fintype α] [Fintype Ω] [DecidableEq ι] [DecidableEq α]
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem integrand_eq (Y : ι → Ω → Option α) (w : Ω) (t : ℝ) {r : ℝ} (hr : 1-t*r≠0) :
    (∏ i, (1+t*(occupancy Y i w-r)))=
      (1-t*r)^Fintype.card ι*((1+t-t*r)/(1-t*r))^occupiedCount Y w := by
  have he (i : ι) : 1+t*(occupancy Y i w-r)=
      (1-t*r)*(if Y i w≠none then (1+t-t*r)/(1-t*r) else 1) := by
    by_cases hi : Y i w=none
    · simp [occupancy,hi]
      ring
    · simp only [occupancy,if_neg hi,if_pos hi]
      field_simp
      ring
  simp_rw [he]
  rw [prod_mul_distrib,prod_const]
  congr 1
  rw [prod_ite]
  simp [occupiedCount,div_pow]

/-- Positive baseline factors ensure that discarding the complement of the witness is legitimate. -/
theorem witness_polynomial_lower (mu : FinitePMF Ω) (Y : ι → Ω → Option α)
    {r t : ℝ} (ht : 0≤t) (hr : t*r<1) (hmean : ∀ i, finitePMFExpectation mu (occupancy Y i)=r)
    (P : Ω → Prop) (N : ℕ) (hN : ∀ w, P w → N≤occupiedCount Y w) :
    eventProbability mu P*(1-t*r)^Fintype.card ι*((1+t-t*r)/(1-t*r))^N≤polynomial mu Y t := by
  have ha : 0<1-t*r := by linarith
  have hb : 1≤(1+t-t*r)/(1-t*r) := (le_div_iff₀ ha).mpr (by linarith)
  have he : finitePMFExpectation mu (fun w ↦ if P w then
      (1-t*r)^Fintype.card ι*((1+t-t*r)/(1-t*r))^N else 0)=
      eventProbability mu P*(1-t*r)^Fintype.card ι*((1+t-t*r)/(1-t*r))^N := by
    have hh (w : Ω) : (if P w then (1-t*r)^Fintype.card ι*((1+t-t*r)/(1-t*r))^N else 0)=
        (if P w then (1:ℝ) else 0)*((1-t*r)^Fintype.card ι*((1+t-t*r)/(1-t*r))^N) := by split_ifs <;> ring
    simp_rw [hh]
    rw [expectation_mul_const,finitePMFExpectation_indicator]
    ring
  rw [← he]
  unfold polynomial
  simp_rw [hmean,integrand_eq Y _ t ha.ne']
  apply expectation_mono
  intro w
  by_cases hw : P w
  · simp only [if_pos hw]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb (hN w hw)) (pow_nonneg ha.le _)
  · simp only [if_neg hw]
    positivity


theorem witness_log_lower (mu : FinitePMF Ω) (Y : ι → Ω → Option α)
    {r t : ℝ} (ht : 0≤t) (hr : t*r<1) (hmean : ∀ i, finitePMFExpectation mu (occupancy Y i)=r)
    (P : Ω → Prop) (hP : 0<eventProbability mu P) (N : ℕ)
    (hN : ∀ w, P w → N≤occupiedCount Y w) :
    Real.log (eventProbability mu P)+(Fintype.card ι:ℝ)*Real.log (1-t*r)+
      (N:ℝ)*Real.log ((1+t-t*r)/(1-t*r))≤Real.log (polynomial mu Y t) := by
  have ha : 0<1-t*r := by linarith
  have hb : 0<(1+t-t*r)/(1-t*r) := div_pos (by linarith) ha
  have hh := Real.log_le_log (mul_pos (mul_pos hP (pow_pos ha _)) (pow_pos hb N))
    (witness_polynomial_lower mu Y ht hr hmean P N hN)
  rw [Real.log_mul (mul_ne_zero hP.ne' (pow_ne_zero _ ha.ne')) (pow_ne_zero _ hb.ne'),
    Real.log_mul hP.ne' (pow_ne_zero _ ha.ne'),Real.log_pow,Real.log_pow] at hh
  exact hh

theorem baseline_log_lower {t r : ℝ} (ht : 0≤t) (hr : 0≤r) (htr : t*r≤1/2) :
    -2*t*r≤Real.log (1-t*r) := by
  have ha : 0<1-t*r := by linarith
  have hh := Real.one_sub_inv_le_log_of_pos ha
  have hi : (1-t*r)⁻¹≤1+2*(t*r) := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ ha).mpr
    nlinarith [mul_nonneg ht hr]
  linarith

theorem occupied_log_lower {t r : ℝ} (ht : 0≤t) (hr : 0≤r) (htr : t*r<1) :
    Real.log (1+t)≤Real.log ((1+t-t*r)/(1-t*r)) := by
  apply Real.log_le_log (by linarith)
  apply (le_div_iff₀ (by linarith : 0<1-t*r)).mpr
  nlinarith [mul_nonneg ht (mul_nonneg ht hr)]

/-- The threshold is for this witness's leading exponent only. -/
theorem positive_leading_iff {t : ℝ} (ht : 0≤t) :
    0<Real.log (1+t)-1 ↔ Real.exp 1-1<t := by
  rw [sub_pos,← Real.exp_lt_exp,Real.exp_log (by linarith : 0<1+t)]
  constructor <;> intro h <;> linarith

end
end PaperC.Prel8.WeightedActivityWitness
