import PaperCV282.SteinLocalTelescoping

/-!
# Scalar Stein identity for arbitrary finite marginals

Zero indicators outside a deterministic mask are allowed. Thus the
matching rate is the mask's actual good-site mean, even when the index
type is a larger ambient family.
-/

namespace PaperC.V282.SteinScalarTelescoping

open ArratiaGoldsteinGordonInput IndependentThinning
open SteinFiniteExpectation SteinLocalTelescoping
open scoped BigOperators

noncomputable section

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]

/-- The sum of the literal local costs is exactly b1+b2. -/
theorem sum_local_cost_eq_bOne_add_bTwo (μ : FinitePMF Ω) (X : ι → Ω → Bool)
    (G : SimpleGraph ι) :
    (∑ i, (marginal μ X i ^ 2 +
      marginal μ X i * ∑ j ∈ (closedNeighborhood G i).erase i, marginal μ X j +
      ∑ j ∈ (closedNeighborhood G i).erase i, jointMarginal μ X i j)) =
      bOne μ X G + bTwo μ X G := by
  classical
  unfold bOne bTwo
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum]
  rw [← Finset.add_sum_erase (closedNeighborhood G i) (fun j => marginal μ X j)
    (self_mem_closedNeighborhood G i)]
  ring

/-- Exact scalar telescoping, with no common-marginal restriction. -/
theorem scalar_stein_error_le (μ : FinitePMF Ω) (X : ι → Ω → Bool)
    (G : SimpleGraph ι) (hdep : HasExactDependencyGraph μ X G)
    (f : ℕ → ℝ) {d : ℝ} (hd : ∀ k, |f (k + 1) - f k| ≤ d) :
    |poissonParameter μ X * finitePMFExpectation μ (fun ω => f (indicatorSum X ω + 1)) -
      finitePMFExpectation μ (fun ω => (indicatorSum X ω : ℝ) * f (indicatorSum X ω))| ≤
      d * (bOne μ X G + bTwo μ X G) := by
  classical
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => local_stein_error_le μ X G hdep i f hd)
  rw [← Finset.mul_sum, sum_local_cost_eq_bOne_add_bTwo] at hsum
  have htriangle := Finset.abs_sum_le_sum_abs
    (fun i => marginal μ X i * finitePMFExpectation μ (fun ω => f (indicatorSum X ω + 1)) -
      finitePMFExpectation μ (fun ω => (if X i ω = true then (1 : ℝ) else 0) * f (indicatorSum X ω)))
    Finset.univ
  have hid :
      (∑ i, (marginal μ X i * finitePMFExpectation μ (fun ω => f (indicatorSum X ω + 1)) -
        finitePMFExpectation μ (fun ω => (if X i ω = true then (1 : ℝ) else 0) * f (indicatorSum X ω)))) =
      poissonParameter μ X * finitePMFExpectation μ (fun ω => f (indicatorSum X ω + 1)) -
        finitePMFExpectation μ (fun ω => (indicatorSum X ω : ℝ) * f (indicatorSum X ω)) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [← expectation_finset_sum]
    have heq : (fun ω => ∑ i, (if X i ω = true then (1 : ℝ) else 0) * f (indicatorSum X ω)) =
        (fun ω => (indicatorSum X ω : ℝ) * f (indicatorSum X ω)) := by
      funext ω
      rw [← countOn_univ X ω, countOn_cast, Finset.sum_mul]
    rw [heq]
    rfl
  rw [hid] at htriangle
  exact htriangle.trans hsum

end
end PaperC.V282.SteinScalarTelescoping
