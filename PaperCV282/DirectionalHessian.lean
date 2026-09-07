import PaperCV282.DirectionalSteinInput

/-! # Entrywise Hessian bounds derived by polarization
The primary source supplies a constant entrywise bound and a weighted
quadratic-form bound for the same solution. This module extracts the
weighted entrywise estimate by polarization and combines the two bounds.
-/
namespace PaperC.V282.DirectionalHessian

open DirectionalSteinInput
open scoped BigOperators NNReal

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def entryFactor (t : κ → ℝ≥0) (i j : κ) : ℝ :=
  min 1 (directionalCoefficient t / (Real.sqrt (t i : ℝ) * Real.sqrt (t j : ℝ)))

omit [DecidableEq κ] in
theorem entryFactor_nonneg (t : κ → ℝ≥0) (i j : κ) : 0 ≤ entryFactor t i j := by
  unfold entryFactor
  exact le_min (by norm_num) (div_nonneg (directionalCoefficient_nonneg t) (by positivity))

omit [DecidableEq κ] in
theorem entryFactor_le_one (t : κ → ℝ≥0) (i j : κ) : entryFactor t i j ≤ 1 := min_le_left _ _

theorem quadratic_two_single (g : (κ → ℕ) → ℝ) (z : κ → ℕ) (i j : κ) (a b : ℝ) :
    hessianQuadratic g z (Pi.single i a + Pi.single j b) =
      a^2*secondDifference g i i z + 2*a*b*secondDifference g i j z + b^2*secondDifference g j j z := by
  unfold hessianQuadratic
  simp only [Pi.add_apply,add_mul,mul_add,Finset.sum_add_distrib]
  simp [Pi.single_apply,ite_mul,mul_ite,Finset.sum_ite_eq' ]
  rw [secondDifference_symm g j i z]
  ring

theorem square_two_single {i j : κ} (hij : i ≠ j) (a b : ℝ) (u : κ → ℝ) :
    (∑ k, ((Pi.single i a : κ → ℝ) k + (Pi.single j b : κ → ℝ) k)^2*u k) = a^2*u i+b^2*u j := by
  simp only [add_sq,add_mul,Finset.sum_add_distrib]
  simp [Pi.single_apply,ite_mul,mul_ite,Ne.symm hij,Finset.sum_ite_eq' ]

/-- A uniform quadratic-form norm bound controls every matrix entry. -/
theorem entry_le_of_quadratic (g : (κ → ℕ) → ℝ) (z : κ → ℕ) (u : κ → ℝ)
    (hu : ∀ i, 0<u i) {K : ℝ}
    (hb : ∀ alpha : κ → ℝ, |hessianQuadratic g z alpha|≤K*∑ i, (alpha i)^2/(u i)^2)
    (i j : κ) : |secondDifference g i j z|≤K/(u i*u j) := by
  by_cases hij : i=j
  · subst j
    have hh := hb (Pi.single i (u i))
    have heq : hessianQuadratic g z (Pi.single i (u i)) = (u i)^2*secondDifference g i i z := by
      simpa using
        quadratic_two_single g z i i (u i) 0
    rw [heq,abs_mul,abs_of_nonneg (sq_nonneg _)] at hh
    have hs : (∑ k, ((Pi.single i (u i) : κ → ℝ) k)^2/(u k)^2) = 1 := by
      simp [Pi.single_apply,ite_div,Finset.sum_ite_eq',ne_of_gt (hu i)]
    rw [hs,mul_one] at hh
    apply (le_div_iff₀ (mul_pos (hu i) (hu i))).mpr
    nlinarith
  · have hp := hb (Pi.single i (u i)+Pi.single j (u j))
    have hm := hb (Pi.single i (u i)+Pi.single j (-u j))
    have hs (a b : ℝ) : (∑ k, ((Pi.single i a+Pi.single j b : κ → ℝ) k)^2/(u k)^2) =
        a^2/(u i)^2+b^2/(u j)^2 := by
      simpa only [Pi.add_apply,div_eq_mul_inv] using square_two_single hij a b (fun k => ((u k)^2)⁻¹)
    rw [hs] at hp hm
    have hpp : (u i)^2/(u i)^2+(u j)^2/(u j)^2=2 := by norm_num [ne_of_gt (hu i),ne_of_gt (hu j)]
    have hmm : (u i)^2/(u i)^2+(-u j)^2/(u j)^2=2 := by norm_num [ne_of_gt (hu i),ne_of_gt (hu j)]
    rw [hpp] at hp
    rw [hmm] at hm
    rw [quadratic_two_single] at hp hm
    have hh := abs_sub_le ( (u i)^2*secondDifference g i i z+2*u i*u j*secondDifference g i j z+(u j)^2*secondDifference g j j z) 0
      ((u i)^2*secondDifference g i i z+2*u i*(-u j)*secondDifference g i j z+(-u j)^2*secondDifference g j j z)
    simp only [sub_zero, zero_sub, abs_neg] at hh
    have heq : (u i)^2*secondDifference g i i z+2*u i*u j*secondDifference g i j z+(u j)^2*secondDifference g j j z-
        ((u i)^2*secondDifference g i i z+2*u i*(-u j)*secondDifference g i j z+(-u j)^2*secondDifference g j j z)=
      (4*u i*u j)*secondDifference g i j z := by ring
    rw [heq,abs_mul,abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hu i).le) (hu j).le : 0≤4*u i*u j)] at hh
    apply (le_div_iff₀ (mul_pos (hu i) (hu j))).mpr
    nlinarith

/-- The two source bounds give their minimum, without a dimension factor. -/
theorem secondDifference_le_entryFactor (t : κ → ℝ≥0) (ht : ∀ i, 0<t i)
    (g : (κ → ℕ) → ℝ)
    (hone : ∀ z i j, |secondDifference g i j z|≤1)
    (hweight : ∀ z alpha, |hessianQuadratic g z alpha|≤directionalCoefficient t*∑ i, (alpha i)^2/(t i : ℝ))
    (z : κ → ℕ) (i j : κ) : |secondDifference g i j z|≤entryFactor t i j := by
  apply le_min
  · exact hone z i j
  · exact entry_le_of_quadratic g z (fun i => Real.sqrt (t i : ℝ))
      (fun i => Real.sqrt_pos.2 (ht i))
      (by intro a;simpa only [Real.sq_sqrt (NNReal.coe_nonneg _)] using hweight z a) i j

end
end PaperC.V282.DirectionalHessian
