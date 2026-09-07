import PaperCV282.ScalarSteinInput
import PaperCV282.SteinScalarTelescoping
import PaperCV282.SteinSoftTelescoping

/-!
# Scalar Poisson bounds from the proved finite Stein calculation

Both the dependency-graph bound and the soft-exception bound use actual
Poisson mass functions and half-L1 total variation. Their sole named
literature premise concerns scalar Stein solutions, not these probability
bounds. Zero target intensity is included by the internal zero-rate proof.
-/

namespace PaperC.V282.ScalarPoissonBounds

open ArratiaGoldsteinGordonInput IndependentThinning SectionThirteenFiniteBound
open SteinFiniteExpectation SteinTestTotalVariation ScalarSteinInput
open SteinScalarTelescoping SteinSoftTelescoping
open scoped BigOperators NNReal

noncomputable section

local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- Integrating the Stein equation gives the actual test-set discrepancy. -/
theorem expectation_stein_equation (μ : FinitePMF Ω) (W : Ω → ℕ)
    (rate : ℝ≥0) (A : Set ℕ) (f : ℕ → ℝ)
    (heq : ∀ k : ℕ, (rate : ℝ) * f (k + 1) - (k : ℝ) * f k =
      (if k ∈ A then 1 else 0) - poissonSetMass rate A) :
    (rate : ℝ) * finitePMFExpectation μ (fun ω => f (W ω + 1)) -
      finitePMFExpectation μ (fun ω => (W ω : ℝ) * f (W ω)) =
        eventProbability μ (fun ω => W ω ∈ A) - poissonSetMass rate A := by
  classical
  have htest : finitePMFExpectation μ (fun ω => if W ω ∈ A then (1 : ℝ) else 0) =
      eventProbability μ (fun ω => W ω ∈ A) := by
    unfold finitePMFExpectation eventProbability
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h : W ω ∈ A <;> simp [h]
  calc
    _ = finitePMFExpectation μ (fun ω => (rate : ℝ) * f (W ω + 1) - (W ω : ℝ) * f (W ω)) := by
      rw [expectation_sub, expectation_const_mul]
    _ = finitePMFExpectation μ (fun ω => (if W ω ∈ A then 1 else 0) - poissonSetMass rate A) :=
      expectation_congr μ (fun ω => heq (W ω))
    _ = _ := by rw [expectation_sub, expectation_const, htest]

/-- Sharp scalar dependency-graph factor for the actual matching intensity. -/
theorem scalar_poisson_bound_of_solutions (μ : FinitePMF Ω) (X : ι → Ω → Bool)
    (G : SimpleGraph ι) (hdep : HasExactDependencyGraph μ X G) {c d : ℝ}
    (hsol : SteinSolutionBounds (poissonRate μ X) c d) :
    natTotalVariation (finiteNatLaw μ (indicatorSum X)) (poissonMass (poissonRate μ X)) ≤
      d * (bOne μ X G + bTwo μ X G) := by
  apply finiteNatLaw_totalVariation_le_of_test_sets μ (indicatorSum X)
    (hasSum_poissonMass _) (poissonMass_nonneg _)
  intro A
  obtain ⟨f, heq, _, hd⟩ := hsol A
  have h := scalar_stein_error_le μ X G hdep f hd
  have hidentity := expectation_stein_equation μ (indicatorSum X) (poissonRate μ X) A f heq
  change poissonParameter μ X * _ - _ = _ at hidentity
  rw [hidentity] at h
  exact h

/-- Scalar AGG consequence with the intensity of the actual masked family. -/
theorem scalar_poisson_bound (hStein : ScalarSteinFactorsStatement)
    (μ : FinitePMF Ω) (X : ι → Ω → Bool) (G : SimpleGraph ι)
    (hdep : HasExactDependencyGraph μ X G) :
    natTotalVariation (finiteNatLaw μ (indicatorSum X)) (poissonMass (poissonRate μ X)) ≤
      firstSteinFactor (poissonRate μ X) * (bOne μ X G + bTwo μ X G) :=
  scalar_poisson_bound_of_solutions μ X G hdep (steinSolutionBounds_all hStein _)

/-- Exact soft-exception Poisson bound with arbitrary supplied solution norms. -/
theorem soft_poisson_bound_of_solutions (μ : FinitePMF Ω) (X : ι → Ω → Bool)
    (G : SimpleGraph ι) (hdep : HasExactDependencyGraph μ X G)
    (good : Finset ι) {p : ℝ} (hp : 0 ≤ p)
    (hgood : ∀ i ∈ good, marginal μ X i = p)
    (rate : ℝ≥0) (hrate : (rate : ℝ) = (Fintype.card ι : ℝ) * p) {c d : ℝ}
    (hsol : SteinSolutionBounds rate c d) :
    natTotalVariation (finiteNatLaw μ (indicatorSum X)) (poissonMass rate) ≤
      d * goodSteinCost μ X G good p +
        c * ((Finset.univ \ good).card * p + ∑ i ∈ Finset.univ \ good, marginal μ X i) := by
  apply finiteNatLaw_totalVariation_le_of_test_sets μ (indicatorSum X)
    (hasSum_poissonMass _) (poissonMass_nonneg _)
  intro A
  obtain ⟨f, heq, hf, hd⟩ := hsol A
  have h := soft_stein_error_le μ X G hdep good hp hgood f hf hd
  have hidentity := expectation_stein_equation μ (indicatorSum X) rate A f heq
  rw [hrate] at hidentity
  rw [hidentity] at h
  exact h

/-- Companion Lemma B.2 on each finite conditioning fibre, including zero rate. -/
theorem lemma_b_two_finite (hStein : ScalarSteinFactorsStatement)
    (μ : FinitePMF Ω) (X : ι → Ω → Bool) (G : SimpleGraph ι)
    (hdep : HasExactDependencyGraph μ X G) (good : Finset ι)
    {p : ℝ} (hp : 0 ≤ p) (hgood : ∀ i ∈ good, marginal μ X i = p)
    (rate : ℝ≥0) (hrate : (rate : ℝ) = (Fintype.card ι : ℝ) * p) :
    natTotalVariation (finiteNatLaw μ (indicatorSum X)) (poissonMass rate) ≤
      firstSteinFactor rate * goodSteinCost μ X G good p +
        zeroSteinFactor rate *
          ((Finset.univ \ good).card * p + ∑ i ∈ Finset.univ \ good, marginal μ X i) :=
  soft_poisson_bound_of_solutions μ X G hdep good hp hgood rate hrate
    (steinSolutionBounds_all hStein rate)

end
end PaperC.V282.ScalarPoissonBounds
