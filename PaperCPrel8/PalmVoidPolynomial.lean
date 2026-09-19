import PaperCPrel8.PalmTargetSignBound

/-! # The exact finite normalized avoidance polynomial

The law may be an actual planted conditional law. Centering uses the reference
p, without assuming that it equals any of the planted marginal means.
-/
namespace PaperC.Prel8.PalmVoidPolynomial
open PaperC.IndependentThinning PaperC.ArratiaGoldsteinGordonInput PaperC.V282.SteinFiniteExpectation
open scoped BigOperators
noncomputable section
variable {Ω ι : Type*} [Fintype Ω] [DecidableEq ι]

/-- A finite polynomial identity, retaining the singleton terms. -/
theorem normalized_product (S : Finset ι) (J : ι → ℝ) (p t : ℝ) (hp : 1-t*p ≠ 0) :
    (∏ j ∈ S, (1-t*J j))/(1-t*p)^S.card =
      ∑ T ∈ S.powerset, (-t/(1-t*p))^T.card*∏ j ∈ T, (J j-p) := by
  have hpoint (j : ι) : (1-t*J j)/(1-t*p)=1+(-t/(1-t*p))*(J j-p) := by field_simp; ring
  calc
    _ = ∏ j ∈ S, (1-t*J j)/(1-t*p) := by rw [Finset.prod_div_distrib,Finset.prod_const]
    _ = ∏ j ∈ S, (1+(-t/(1-t*p))*(J j-p)) := by simp_rw [hpoint]
    _ = _ := by rw [Finset.prod_one_add]; simp_rw [Finset.prod_mul_distrib,Finset.prod_const]

/-- The exact avoidance expansion holds for every finite source law, including Palm laws. -/
theorem normalized_expectation (mu : FinitePMF Ω) (S : Finset ι) (J : ι → Ω → ℝ)
    (p t : ℝ) (hp : 1-t*p ≠ 0) :
    finitePMFExpectation mu (fun z => ∏ j ∈ S, (1-t*J j z))/(1-t*p)^S.card =
      ∑ T ∈ S.powerset, (-t/(1-t*p))^T.card*
        finitePMFExpectation mu (fun z => ∏ j ∈ T, (J j z-p)) := by
  have he : finitePMFExpectation mu (fun z => (∏ j ∈ S, (1-t*J j z))/(1-t*p)^S.card)=
      finitePMFExpectation mu (fun z => ∏ j ∈ S, (1-t*J j z))/(1-t*p)^S.card := by
    simp only [div_eq_mul_inv,expectation_mul_const]
  rw [← he]
  simp_rw [normalized_product S _ p t hp]
  rw [expectation_finset_sum]
  apply Finset.sum_congr rfl
  intro T _
  exact expectation_const_mul _ _ _

/-- The constant coefficient is one for the actual probability law. -/
theorem empty_centered_moment (mu : FinitePMF Ω) (J : ι → Ω → ℝ) (p : ℝ) :
    finitePMFExpectation mu (fun z => ∏ j ∈ (∅ : Finset ι), (J j z-p))=1 := by
  simp only [Finset.prod_empty,expectation_const]

/-- The singleton coefficient records the planted marginal correction; it need not vanish. -/
theorem singleton_centered_moment (mu : FinitePMF Ω) (J : ι → Ω → ℝ) (p : ℝ) (j : ι) :
    finitePMFExpectation mu (fun z => ∏ i ∈ ({j} : Finset ι), (J i z-p))=
      finitePMFExpectation mu (J j)-p := by
  simp only [Finset.prod_singleton,expectation_sub,expectation_const]

/-- At t=1 the numerator is the actual event of no remaining occurrence. -/
theorem avoidance_probability (mu : FinitePMF Ω) (S : Finset ι) (J : ι → Ω → Bool) :
    finitePMFExpectation mu (fun z => ∏ j ∈ S, (1-(if J j z then (1:ℝ) else 0)))=
      eventProbability mu (fun z => ∀ j ∈ S, J j z=false) := by
  classical
  have he (z : Ω) : (∏ j ∈ S, (1-(if J j z then (1:ℝ) else 0)))=
      if ∀ j ∈ S, J j z=false then 1 else 0 := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert j S hj ih =>
      rw [Finset.prod_insert hj,ih]
      cases h : J j z <;> simp [h]
  simp_rw [he]
  unfold finitePMFExpectation eventProbability
  apply Finset.sum_congr rfl
  intro z _
  by_cases h : ∀ j ∈ S, J j z=false <;> simp [h]

end
end PaperC.Prel8.PalmVoidPolynomial
