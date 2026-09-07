import PaperCV282.PoissonQuantitativeMoments

/-! # The actual upper Poisson tail controlled by successive mass ratios -/
namespace PaperC.V282.PoissonQuantitativeTailGeometric

open MeasureTheory ProbabilityTheory Real Set PoissonFillingIdentity PoissonFieldMeasure
open scoped NNReal

noncomputable section

theorem poisson_tail_eq_tsum (rate : ℝ≥0) (n : ℕ) :
    (poissonMeasure rate).real (Ici n)=∑' j : ℕ,(poissonMeasure rate).real {n+j} := by
  let e : ℕ≃Ici n := {
    toFun := fun j => ⟨n+j,Nat.le_add_right n j⟩
    invFun := fun k => k.val-n
    left_inv := fun j => by simp
    right_inv := fun k => by apply Subtype.ext;dsimp;have hk := k.property;change n≤k.val at hk;omega }
  have h : (∑' k : Ici n,(poissonMeasure rate).real {k.val})=(poissonMeasure rate).real (Ici n) :=
    real_tsum_singletons (poissonMeasure rate) (Ici n)
  rw [← h]
  exact (e.tsum_eq (fun k : Ici n => (poissonMeasure rate).real {k.val})).symm

theorem poisson_mass_successive_le (rate : ℝ≥0) (n j : ℕ) :
    (poissonMeasure rate).real {n+j+1}≤((rate : ℝ)/(n+1))*(poissonMeasure rate).real {n+j} := by
  have hrec := poisson_mass_recurrence rate (n+j)
  change ((n+j+1 : ℕ) : ℝ)*(poissonMeasure rate).real {n+j+1}=
    (rate : ℝ)*(poissonMeasure rate).real {n+j} at hrec
  have hd : (0 : ℝ)<n+j+1 := by positivity
  have hp : (0 : ℝ)<n+1 := by positivity
  have he : (poissonMeasure rate).real {n+j+1}=
      (rate : ℝ)/(n+j+1)*(poissonMeasure rate).real {n+j} := by
    simp only [Nat.cast_add,Nat.cast_one] at hrec
    field_simp
    nlinarith only [hrec]
  rw [he]
  apply mul_le_mul_of_nonneg_right _ measureReal_nonneg
  exact div_le_div_of_nonneg_left rate.coe_nonneg hp (by have h := (Nat.cast_nonneg j : (0 : ℝ)≤j);linarith)

theorem poisson_mass_geometric_le (rate : ℝ≥0) (n j : ℕ) :
    (poissonMeasure rate).real {n+j}≤((rate : ℝ)/(n+1))^j*(poissonMeasure rate).real {n} := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h := (poisson_mass_successive_le rate n j).trans
      (mul_le_mul_of_nonneg_left ih (by positivity))
    simpa only [Nat.succ_eq_add_one,Nat.add_assoc,pow_succ,mul_assoc,mul_comm,mul_left_comm] using h

/-- No tail probability is assumed: this is the sum of the true Poisson atoms. -/
theorem poisson_tail_le_geometric (rate : ℝ≥0) (n : ℕ) (hn : (rate : ℝ)<n+1) :
    (poissonMeasure rate).real (Ici n)≤
      (poissonMeasure rate).real {n}/(1-(rate : ℝ)/(n+1)) := by
  have hq0 : 0≤(rate : ℝ)/(n+1) := by positivity
  have hq1 : (rate : ℝ)/(n+1)<1 := (div_lt_one (by positivity)).mpr hn
  have hs := (summable_geometric_of_abs_lt_one (by rwa [abs_of_nonneg hq0])).mul_right
    ((poissonMeasure rate).real {n})
  have hleft : Summable (fun j : ℕ => (poissonMeasure rate).real {n+j}) :=
    hs.of_nonneg_of_le (fun _ => measureReal_nonneg) (poisson_mass_geometric_le rate n)
  rw [poisson_tail_eq_tsum]
  have h := hleft.tsum_le_tsum (poisson_mass_geometric_le rate n) hs
  rw [tsum_mul_right,tsum_geometric_of_lt_one hq0 hq1] at h
  simpa only [div_eq_mul_inv,mul_comm] using h

end
end PaperC.V282.PoissonQuantitativeTailGeometric
