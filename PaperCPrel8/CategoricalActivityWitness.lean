import PaperCPrel8.CategoricalOccupancyEnvelope

/-! # A rare-event lower bound for the actual categorical cumulant activity -/
namespace PaperC.Prel8.CategoricalActivityWitness
open Finset CategoricalOccupancyEnvelope CategoricalCumulantBound
open IndependentThinning ArratiaGoldsteinGordonInput V282.SteinFiniteExpectation
noncomputable section
variable {ι α Ω : Type*} [Fintype ι] [Fintype α] [Fintype Ω] [DecidableEq ι] [DecidableEq α]
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def occupiedCount (Y : ι → Ω → Option α) (w : Ω) : ℕ :=
  (univ.filter (fun i ↦ Y i w≠none)).card

/-- Exact factorization of the occupancy polynomial integrand at a common mean. -/
theorem integrand_eq (Y : ι → Ω → Option α) (w : Ω) {r : ℝ} (hr : 1-2*r≠0) :
    (∏ i, (1+2*(occupancy Y i w-r)))=
      (1-2*r)^Fintype.card ι*((3-2*r)/(1-2*r))^occupiedCount Y w := by
  have he (i : ι) : 1+2*(occupancy Y i w-r)=
      (1-2*r)*(if Y i w≠none then (3-2*r)/(1-2*r) else 1) := by
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
    {r : ℝ} (hr : 2*r<1) (hmean : ∀ i, finitePMFExpectation mu (occupancy Y i)=r)
    (P : Ω → Prop) (N : ℕ) (hN : ∀ w, P w → N≤occupiedCount Y w) :
    eventProbability mu P*(1-2*r)^Fintype.card ι*((3-2*r)/(1-2*r))^N≤polynomial mu Y 2 := by
  have ha : 0<1-2*r := by linarith
  have hb : 1≤(3-2*r)/(1-2*r) := (le_div_iff₀ ha).mpr (by linarith)
  have he : finitePMFExpectation mu (fun w ↦ if P w then
      (1-2*r)^Fintype.card ι*((3-2*r)/(1-2*r))^N else 0)=
      eventProbability mu P*(1-2*r)^Fintype.card ι*((3-2*r)/(1-2*r))^N := by
    have hh (w : Ω) : (if P w then (1-2*r)^Fintype.card ι*((3-2*r)/(1-2*r))^N else 0)=
        (if P w then (1:ℝ) else 0)*((1-2*r)^Fintype.card ι*((3-2*r)/(1-2*r))^N) := by split_ifs <;> ring
    simp_rw [hh]
    rw [expectation_mul_const,finitePMFExpectation_indicator]
    ring
  rw [← he]
  unfold polynomial
  simp_rw [hmean,integrand_eq Y _ ha.ne']
  apply expectation_mono
  intro w
  by_cases hw : P w
  · simp only [if_pos hw]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb (hN w hw)) (pow_nonneg ha.le _)
  · simp only [if_neg hw]
    positivity

/-- Finite G.9 lower bound, before any prime-number or asymptotic estimate. -/
theorem witness_activity_lower (mu : FinitePMF Ω) (Y : ι → Ω → Option α)
    {r : ℝ} (hr : 2*r<1) (hmean : ∀ i, finitePMFExpectation mu (occupancy Y i)=r)
    (P : Ω → Prop) (hP : 0<eventProbability mu P)
    (N : ℕ) (hN : ∀ w, P w → N≤occupiedCount Y w) :
    (Real.log (eventProbability mu P)+(Fintype.card ι:ℝ)*Real.log (1-2*r)+
      (N:ℝ)*Real.log ((3-2*r)/(1-2*r)))/2≤activity mu Y := by
  have ha : 0<1-2*r := by linarith
  have hb : 0<(3-2*r)/(1-2*r) := div_pos (by linarith) ha
  have h := Real.log_le_log (mul_pos (mul_pos hP (pow_pos ha _)) (pow_pos hb N))
    (witness_polynomial_lower mu Y hr hmean P N hN)
  rw [Real.log_mul (mul_ne_zero hP.ne' (pow_ne_zero _ ha.ne')) (pow_ne_zero _ hb.ne'),
    Real.log_mul hP.ne' (pow_ne_zero _ ha.ne'),Real.log_pow,Real.log_pow] at h
  have hu := activity_ge_half_log_polynomial mu Y (fun i ↦ by rw [hmean]; exact hr)
  linarith

end
end PaperC.Prel8.CategoricalActivityWitness
