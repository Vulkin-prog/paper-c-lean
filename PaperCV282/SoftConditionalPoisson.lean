import PaperCV282.ScalarPoissonBounds

/-!
# Averaging the finite soft-exception bound

The conditioning environment has an arbitrary finite probability law.
Neighbour marginals and pair probabilities are averaged exactly; no
exceptional neighbour is assigned the common good-site marginal.
-/

namespace PaperC.V282.SoftConditionalPoisson

open ArratiaGoldsteinGordonInput IndependentThinning SectionThirteenFiniteBound
open SteinFiniteExpectation SteinSoftTelescoping ScalarSteinInput ScalarPoissonBounds
open scoped BigOperators NNReal

noncomputable section

variable {Ω Θ ι : Type*} [Fintype Ω] [Fintype Θ] [Fintype ι] [DecidableEq ι]

/-- Exact mean cost: the neighbours keep their true averaged marginals. -/
theorem average_goodSteinCost (ν : FinitePMF Θ) (μ : Θ → FinitePMF Ω)
    (X : Θ → ι → Ω → Bool) (G : SimpleGraph ι) (good : Finset ι) (p : ℝ) :
    finitePMFExpectation ν (fun θ => goodSteinCost (μ θ) (X θ) G good p) =
      good.card * p ^ 2 +
        p * (∑ i ∈ good, ∑ j ∈ (closedNeighborhood G i).erase i,
          finitePMFExpectation ν (fun θ => marginal (μ θ) (X θ) j)) +
        ∑ i ∈ good, ∑ j ∈ (closedNeighborhood G i).erase i,
          finitePMFExpectation ν (fun θ => jointMarginal (μ θ) (X θ) i j) := by
  simp only [goodSteinCost, expectation_add, expectation_const_mul,
    expectation_const, expectation_finset_sum]

/-- Companion (B.4): mean conditional total variation, with both intensity factors. -/
theorem lemma_b_two_average (hStein : ScalarSteinFactorsStatement)
    (ν : FinitePMF Θ) (μ : Θ → FinitePMF Ω) (X : Θ → ι → Ω → Bool)
    (G : SimpleGraph ι) (hdep : ∀ θ, HasExactDependencyGraph (μ θ) (X θ) G)
    (good : Finset ι) {p : ℝ} (hp : 0 ≤ p)
    (hgood : ∀ θ, ∀ i ∈ good, marginal (μ θ) (X θ) i = p)
    (rate : ℝ≥0) (hrate : (rate : ℝ) = (Fintype.card ι : ℝ) * p) :
    finitePMFExpectation ν (fun θ =>
      natTotalVariation (finiteNatLaw (μ θ) (indicatorSum (X θ))) (poissonMass rate)) ≤
      firstSteinFactor rate *
        (good.card * p ^ 2 +
          p * (∑ i ∈ good, ∑ j ∈ (closedNeighborhood G i).erase i,
            finitePMFExpectation ν (fun θ => marginal (μ θ) (X θ) j)) +
          ∑ i ∈ good, ∑ j ∈ (closedNeighborhood G i).erase i,
            finitePMFExpectation ν (fun θ => jointMarginal (μ θ) (X θ) i j)) +
      zeroSteinFactor rate *
        ((Finset.univ \ good).card * p +
          ∑ i ∈ Finset.univ \ good, finitePMFExpectation ν (fun θ => marginal (μ θ) (X θ) i)) := by
  have h := expectation_mono ν (fun θ =>
    lemma_b_two_finite hStein (μ θ) (X θ) G (hdep θ) good hp (hgood θ) rate hrate)
  simpa only [expectation_add, expectation_const_mul, expectation_const,
    expectation_finset_sum, average_goodSteinCost] using h

/-- Restriction to a positive-probability environment event costs one inverse mass. -/
theorem weighted_environment_restriction_le (ν : FinitePMF Θ)
    (event : Θ → Prop) [DecidablePred event] (distance budget : Θ → ℝ)
    (hpoint : ∀ θ, distance θ ≤ budget θ) (hbudget : ∀ θ, 0 ≤ budget θ)
    {eventMass : ℝ} (hmass : 0 < eventMass) :
    finitePMFExpectation ν (fun θ => if event θ then distance θ else 0) / eventMass ≤
      finitePMFExpectation ν budget / eventMass := by
  apply div_le_div_of_nonneg_right _ hmass.le
  apply expectation_mono
  intro θ
  by_cases h : event θ
  · simpa [h] using hpoint θ
  · simpa [h] using hbudget θ

end
end PaperC.V282.SoftConditionalPoisson
