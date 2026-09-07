import PaperCV282.DirectionalSteinInput
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Fin.VecNotation

/-! # An exact counterexample to the former Euclidean Stein premise

For two means equal to one half and the test consisting of the two unit
vectors, the Stein equation forces the all-ones quadratic Hessian at zero
to equal 4(1-exp(-1)) > 2. This contradicts the former unweighted Euclidean
bound for every possible solution, without a uniqueness or growth argument.
-/
namespace PaperC.V282.DirectionalSteinCounterexample

open DirectionalSteinInput FiniteFieldPoissonCoupling ScalarSteinInput
open scoped BigOperators NNReal

noncomputable section

local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

def halfRates : Fin 2 → ℝ≥0 := fun _ => 1 / 2

def onePointTest : Set (Fin 2 → ℕ) := {![1, 0], ![0, 1]}

theorem addPoint_vec_zero (a b : ℕ) : addPoint ![a,b] 0 = ![a+1,b] := by
  ext i
  fin_cases i <;> simp [addPoint]

theorem addPoint_vec_one (a b : ℕ) : addPoint ![a,b] 1 = ![a,b+1] := by
  ext i
  fin_cases i <;> simp [addPoint]

theorem removePoint_vec_zero (a b : ℕ) : removePoint ![a,b] 0 = ![a-1,b] := by
  ext i
  fin_cases i <;> simp [removePoint]

theorem removePoint_vec_one (a b : ℕ) : removePoint ![a,b] 1 = ![a,b-1] := by
  ext i
  fin_cases i <;> simp [removePoint]

/-- A finite identity valid for every function on the count lattice. -/
theorem generator_hessian_identity (g : (Fin 2 → ℕ) → ℝ) :
    hessianQuadratic g ![0,0] (fun _ => 1) =
      2*(steinGenerator halfRates g ![1,0] + steinGenerator halfRates g ![0,1]) := by
  simp only [hessianQuadratic,steinGenerator,Fin.sum_univ_two,
    firstDifference,secondDifference,addPoint_vec_zero,addPoint_vec_one,
    removePoint_vec_zero,removePoint_vec_one,halfRates]
  norm_num
  ring

theorem halfRates_positive (i : Fin 2) : 0 < halfRates i := by
  norm_num [halfRates]

/-- The genuine product Poisson mass of the two unit vectors. -/
theorem onePointTest_mass : poissonTestMass halfRates onePointTest = Real.exp (-1) := by
  have hne : (![1,0] : Fin 2 → ℕ) ≠ ![0,1] := by
    intro h
    have h0 := congrFun h 0
    norm_num at h0
  unfold poissonTestMass
  rw [tsum_eq_sum (s := ({![1,0], ![0,1]} : Finset (Fin 2 → ℕ))) (by
    intro z hz
    have hz' : z ∉ onePointTest := by simpa [onePointTest] using hz
    simp [hz'])]
  simp [onePointTest,hne,Ne.symm hne,poissonFieldMass,Fin.prod_univ_two,
    poissonMass_formula,halfRates]
  have he : Real.exp (-(1/2 : ℝ))*Real.exp (-(1/2 : ℝ)) = Real.exp (-1) := by
    rw [← Real.exp_add]
    congr 1
    ring
  nlinarith

/-- No Stein solution at these actual rates can obey the old Euclidean bound. -/
theorem no_euclidean_solution (g : (Fin 2 → ℕ) → ℝ)
    (hEq : ∀ z, steinGenerator halfRates g z =
      (if z ∈ onePointTest then 1 else 0) - poissonTestMass halfRates onePointTest) :
    ¬ (∀ z alpha, |hessianQuadratic g z alpha| ≤ ∑ i, (alpha i)^2) := by
  intro hbound
  have h := hbound ![0,0] (fun _ => 1)
  rw [generator_hessian_identity,hEq,hEq,onePointTest_mass] at h
  have hm1 : (![1,0] : Fin 2 → ℕ) ∈ onePointTest := by simp [onePointTest]
  have hm2 : (![0,1] : Fin 2 → ℕ) ∈ onePointTest := by simp [onePointTest]
  simp only [if_pos hm1,if_pos hm2,one_pow,Fin.sum_univ_two] at h
  have he : Real.exp (-1) < (1/2 : ℝ) := by
    have heq : Real.exp (-1)*Real.exp 1 = 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (-1),Real.exp_one_gt_two]
  have hh := le_abs_self (2*((1-Real.exp (-1))+(1-Real.exp (-1))))
  linarith

/-- The former solution-existence clause is false already in dimension two. -/
theorem not_euclidean_solution_statement :
    ¬ (∀ A : Set (Fin 2 → ℕ), ∃ g : (Fin 2 → ℕ) → ℝ,
      (∀ z, steinGenerator halfRates g z = (if z ∈ A then 1 else 0) - poissonTestMass halfRates A) ∧
      (∀ z alpha, |hessianQuadratic g z alpha| ≤ ∑ i, (alpha i)^2)) := by
  intro h
  obtain ⟨g,hEq,hbound⟩ := h onePointTest
  exact no_euclidean_solution g hEq hbound

end
end PaperC.V282.DirectionalSteinCounterexample
