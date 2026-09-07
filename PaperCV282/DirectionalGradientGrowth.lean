import PaperCV282.DirectionalHessian
import PaperCV282.DirectionalSteinComparison
import PaperCV282.PoissonPolynomialIntegrability

/-! # Growth of directional Stein gradients

Only the proved Hessian entry bound is used. No integrability or bounded-gradient
claim is added to the published Stein input.
-/
namespace PaperC.V282.DirectionalGradientGrowth

open DirectionalSteinInput DirectionalSteinComparison DirectionalHessian
open MeasureTheory PoissonFieldMeasure PoissonPolynomialIntegrability
open scoped BigOperators NNReal

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Repeated coordinates are actual unit steps, with their own directional weights. -/
theorem vector_difference_le (f : (κ → ℕ) → ℝ) (weight : κ → ℝ)
    (hstep : ∀ z j, |f (addPoint z j)-f z|≤weight j) (v z : κ → ℕ) :
    |f (v+z)-f v|≤∑ j, (z j : ℝ)*weight j := by
  let index := (j : κ) × Fin (z j)
  let X : index → Unit → Bool := fun _ _ => true
  let kind : index → κ := fun i => i.1
  have hz : typedSum X kind Finset.univ ()=z := by
    ext k
    simp only [typedSum, X, kind, if_true, Finset.sum_apply, Pi.single_apply]
    change (∑ j : (j : κ) × Fin (z j), if k=j.1 then 1 else 0)=z k
    rw [Fintype.sum_sigma]
    dsimp only
    calc
      (∑ x, ∑ _y : Fin (z x), if k=x then 1 else 0) = ∑ x, if k=x then z x else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases h : k=x <;> simp [h]
      _ = z k := by simp
  have h := typedSum_difference_le X kind Finset.univ f weight hstep v ()
  rw [hz] at h
  simpa [X,kind,index,Fintype.sum_sigma] using h

/-- The unweighted source Hessian estimate implies at most linear growth. -/
theorem firstDifference_growth (g : (κ → ℕ) → ℝ)
    (hsecond : ∀ z i j, |secondDifference g i j z|≤1) (i : κ) (z : κ → ℕ) :
    |firstDifference g i z|≤|firstDifference g i 0|+∑ j, (z j : ℝ) := by
  have hs : ∀ z j, |firstDifference g i (addPoint z j)-firstDifference g i z|≤(1 : ℝ) := by
    intro z j
    rw [firstDifference_addPoint]
    exact hsecond z i j
  have h := vector_difference_le (firstDifference g i) (fun _ => 1) hs 0 z
  simp only [zero_add,mul_one] at h
  have hh := abs_sub_le (firstDifference g i z) (firstDifference g i 0) 0
  simp only [sub_zero] at hh
  linarith

/-- Any fixed translation of a Stein gradient is integrable under the actual filling. -/
theorem integrable_firstDifference_shift (rate : κ → ℝ≥0) (g : (κ → ℕ) → ℝ)
    (hsecond : ∀ z i j, |secondDifference g i j z|≤1) (i : κ) (v : κ → ℕ) :
    Integrable (fun z => firstDifference g i (v+z)) (fieldMeasure rate) := by
  apply integrable_of_affine_bound rate _ (|firstDifference g i 0|+∑ j, (v j : ℝ)) 1
  intro z
  have h := firstDifference_growth g hsecond i (v+z)
  simpa only [Pi.add_apply,Nat.cast_add,Finset.sum_add_distrib,one_mul,add_assoc] using h

/-- The coordinate times a gradient remains integrable for every coordinatewise bounded shift. -/
theorem integrable_coordinate_firstDifference (rate : κ → ℝ≥0) (g : (κ → ℕ) → ℝ)
    (hsecond : ∀ z i j, |secondDifference g i j z|≤1) (i j : κ) (v : κ → ℕ)
    (shift : (κ → ℕ) → κ → ℕ) (hshift : ∀ z k, shift z k≤v k+z k) :
    Integrable (fun z => (z j : ℝ)*firstDifference g i (shift z)) (fieldMeasure rate) := by
  let A : ℝ := |firstDifference g i 0|+∑ k, (v k : ℝ)
  have hA : 0≤A := by dsimp [A];positivity
  apply integrable_of_quadratic_bound rate _ 0 A 1
  intro z
  let S : ℝ := ∑ k, (z k : ℝ)
  have hS : 0≤S := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hgrad : |firstDifference g i (shift z)|≤A+S := by
    apply (firstDifference_growth g hsecond i (shift z)).trans
    have hs : (∑ k, (shift z k : ℝ))≤(∑ k, (v k : ℝ))+(∑ k, (z k : ℝ)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro k hk
      exact_mod_cast hshift z k
    dsimp [A,S]
    linarith
  rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
  have hmul := mul_le_mul_of_nonneg_left hgrad (Nat.cast_nonneg (z j))
  have hmul2 := mul_le_mul_of_nonneg_right (coordinate_le_total z j) (add_nonneg hA hS)
  change _≤0+A*S+1*S^2
  change _≤S*(A+S) at hmul2
  nlinarith

end
end PaperC.V282.DirectionalGradientGrowth
