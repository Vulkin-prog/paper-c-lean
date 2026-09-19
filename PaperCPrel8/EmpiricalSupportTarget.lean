import PaperCV282.PoissonFieldMeasure
import PaperCV282.SharpConditioningDiscrete

/-! # Poisson target masses used by the empirical support obstruction

Every configuration with total count at least two has mass at most p^2
when p<=1. The entire two-or-more event has an exact Poisson tail mass.
-/
namespace PaperC.Prel8.EmpiricalSupportTarget
open MeasureTheory ProbabilityTheory
open PaperC.V282.PoissonFieldMeasure PaperC.V282.FiniteFieldPoissonCoupling
open PaperC.V282.ScalarSteinInput
open scoped BigOperators NNReal
noncomputable section

/-- Dropping the exponential and factorial yields a simple singleton bound. -/
theorem poisson_mass_le_power (p : ℝ≥0) (n : ℕ) : poissonMass p n ≤ (p:ℝ)^n := by
  rw [poissonMass_formula]
  have he : Real.exp (-(p:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr p.coe_nonneg)
  have hf : (1:ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_pos n
  calc
    _ ≤ Real.exp (-(p:ℝ))*(p:ℝ)^n := div_le_self (by positivity) hf
    _ ≤ _ := by nlinarith [pow_nonneg p.coe_nonneg n]

/-- Any product-Poisson configuration with at least two points has mass <=p^2. -/
theorem multiple_point_mass_le {ι : Type*} [Fintype ι] (p : ℝ≥0) (hp : p ≤ 1)
    (z : ι → ℕ) (hz : 2 ≤ ∑ i, z i) :
    (fieldMeasure (fun _ : ι => p)).real {z} ≤ (p:ℝ)^2 := by
  rw [fieldMeasure_real_singleton,poissonFieldMass]
  calc
    _ ≤ ∏ i, (p:ℝ)^(z i) :=
      Finset.prod_le_prod₀ (fun i _ => poissonMass_nonneg _ _) (fun i _ => poisson_mass_le_power _ _)
    _ = (p:ℝ)^(∑ i, z i) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ _ := pow_le_pow_of_le_one p.coe_nonneg (by exact_mod_cast hp) hz

/-- Exact probability of at least two points in a scalar Poisson law. -/
theorem poisson_multiple_probability (p : ℝ≥0) :
    (poissonMeasure p).real {n : ℕ | 2 ≤ n} = 1-Real.exp (-(p:ℝ))*(1+(p:ℝ)) := by
  have he : {n : ℕ | 2 ≤ n} = ({0,1}:Set ℕ)ᶜ := by ext n; simp; omega
  rw [he,measureReal_compl (by measurability),probReal_univ]
  have hs := sum_measureReal_singleton (μ := poissonMeasure p) ({0,1}:Finset ℕ)
  norm_num [poissonMeasure_real_singleton] at hs
  rw [← hs]
  ring

/-- Exact mass of the two-or-more event for the genuine product target. -/
theorem field_multiple_probability {ι : Type*} [Fintype ι] (p : ℝ≥0) :
    (fieldMeasure (fun _ : ι => p)).real {z | 2 ≤ ∑ i, z i} =
      1-Real.exp (-(Fintype.card ι:ℝ)*(p:ℝ))*(1+(Fintype.card ι:ℝ)*(p:ℝ)) := by
  have hl := hasLaw_coordinate_sum (fun _ : ι => p) Finset.univ
  have hm := hl.measureReal_eq (p := fun n : ℕ => 2 ≤ n) (by measurability)
  rw [poisson_multiple_probability] at hm
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,NNReal.coe_mul,
    NNReal.coe_natCast,neg_mul] using hm

/-- The limiting obstruction is strictly positive at every positive mean. -/
theorem obstruction_positive {tau : ℝ} (ht : 0 < tau) :
    0 < 1-Real.exp (-tau)*(1+tau) := by
  have h := Real.add_one_lt_exp ht.ne'
  have hm := mul_lt_mul_of_pos_left h (Real.exp_pos (-tau))
  rw [← Real.exp_add] at hm
  norm_num at hm
  linarith

end
end PaperC.Prel8.EmpiricalSupportTarget
