import PaperCV282.PoissonFieldMeasure
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Exact cancellation of independent Poisson filling

All identities use the actual product Poisson measure, including zero rates.
The reindexing has a zero boundary term. Real Bochner integrals agree with
these unconditional sums; integrability of sums of Stein terms is established
separately before using linearity in the comparison argument.
-/
namespace PaperC.V282.PoissonFillingIdentity

open MeasureTheory ProbabilityTheory PoissonFieldMeasure FiniteFieldPoissonCoupling ScalarSteinInput
open scoped BigOperators NNReal

noncomputable section

def increment {ι : Type*} [DecidableEq ι] (i : ι) (z : ι → ℕ) : ι → ℕ :=
  Function.update z i (z i+1)

def decrement {ι : Type*} [DecidableEq ι] (i : ι) (z : ι → ℕ) : ι → ℕ :=
  Function.update z i (z i-1)

theorem decrement_increment {ι : Type*} [DecidableEq ι] (i : ι) (z : ι → ℕ) :
    decrement i (increment i z)=z := by
  funext j
  by_cases h : j=i <;> simp [increment,decrement,h]

theorem increment_decrement {ι : Type*} [DecidableEq ι] (i : ι) (z : ι → ℕ) (hz : 0<z i) :
    increment i (decrement i z)=z := by
  funext j
  by_cases h : j=i
  · subst j;simp [increment,decrement,Nat.sub_add_cancel hz]
  · simp [increment,decrement,h]

theorem increment_injective {ι : Type*} [DecidableEq ι] (i : ι) :
    Function.Injective (increment i) := by
  intro x y h
  have hh := congrArg (decrement i) h
  simpa only [decrement_increment] using hh

/-- The scalar identity does not divide by the rate, so a zero filling is included. -/
theorem poisson_mass_recurrence (rate : ℝ≥0) (k : ℕ) :
    ((k+1 : ℕ) : ℝ)*poissonMass rate (k+1)=(rate : ℝ)*poissonMass rate k := by
  rw [poissonMass_formula,poissonMass_formula,Nat.factorial_succ,pow_succ]
  push_cast
  field_simp

theorem poisson_field_mass_recurrence {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rate : ι → ℝ≥0) (i : ι) (z : ι → ℕ) :
    ((z i+1 : ℕ) : ℝ)*poissonFieldMass rate (increment i z)=
      (rate i : ℝ)*poissonFieldMass rate z := by
  unfold poissonFieldMass
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [increment,Function.update_self]
  have hprod : (∏ j ∈ Finset.univ.erase i, poissonMass (rate j) (Function.update z i (z i+1) j))=
      ∏ j ∈ Finset.univ.erase i, poissonMass (rate j) (z j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [hprod,← mul_assoc,poisson_mass_recurrence]
  ring

/-- Sum cancellation for an arbitrary real test, with its zero coordinate boundary retained. -/
theorem poisson_filling_tsum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rate : ι → ℝ≥0) (i : ι) (f : (ι → ℕ) → ℝ) :
    (∑' z, poissonFieldMass rate z*(z i : ℝ)*f (decrement i z))=
      (rate i : ℝ)*∑' z, poissonFieldMass rate z*f z := by
  have hreindex := (increment_injective i).tsum_eq
    (f := fun z => poissonFieldMass rate z*(z i : ℝ)*f (decrement i z))
    (fun z hz => by
      have hpos : 0<z i := by
        apply Nat.pos_of_ne_zero
        intro hzero
        simp [Function.mem_support,hzero] at hz
      exact ⟨decrement i z,increment_decrement i z hpos⟩)
  rw [← hreindex]
  simp only [decrement_increment]
  have hpoint (z : ι → ℕ) :
      poissonFieldMass rate (increment i z)*((increment i z) i : ℝ)*f z=
        (rate i : ℝ)*(poissonFieldMass rate z*f z) := by
    simp only [increment,Function.update_self]
    have h := poisson_field_mass_recurrence rate i z
    change _*poissonFieldMass rate (Function.update z i (z i+1))=_ at h
    calc
      _ = (((z i+1 : ℕ) : ℝ)*poissonFieldMass rate (Function.update z i (z i+1)))*f z := by ring
      _ = _ := by rw [h];ring
  simp_rw [hpoint]
  exact tsum_mul_left

/-- Real integration against the true product law is its singleton-weighted sum. -/
theorem integral_field_eq_tsum {ι : Type*} [Fintype ι]
    (rate : ι → ℝ≥0) (f : (ι → ℕ) → ℝ) :
    (∫ z, f z ∂fieldMeasure rate)=∑' z, poissonFieldMass rate z*f z := by
  conv_lhs => rw [← Measure.sum_smul_dirac (fieldMeasure rate)]
  rw [integral_sum_dirac (fun z => measure_ne_top _ _)]
  simp only [smul_eq_mul]
  change (∑' z, (fieldMeasure rate).real {z}*f z)=_
  simp only [fieldMeasure_real_singleton]

/-- Genuine Poisson integration by parts for a coordinate of the independent filling. -/
theorem poisson_filling_integral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rate : ι → ℝ≥0) (i : ι) (f : (ι → ℕ) → ℝ) :
    (∫ z, (z i : ℝ)*f (decrement i z) ∂fieldMeasure rate)=
      (rate i : ℝ)*∫ z, f z ∂fieldMeasure rate := by
  rw [integral_field_eq_tsum,integral_field_eq_tsum]
  simp only [← mul_assoc]
  exact poisson_filling_tsum rate i f

end
end PaperC.V282.PoissonFillingIdentity
