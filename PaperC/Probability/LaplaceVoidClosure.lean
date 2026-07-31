import PaperC.Probability.IndependentThinning
import PaperC.Probability.PoissonLaplaceFunctional

/-!
# Finite closure of the auxiliary-thinning Laplace argument

This module joins the two exact finite interfaces used by Section 14:

* independent exponential thinning identifies a void probability with the
  expectation of the original exponential functional;
* Arratia--Goldstein--Gordon controls that void probability by the
  exponential of the thinned Poisson parameter.

The dependency-graph hypothesis is explicit, so later spatial and marked
instantiations can reuse the statement without any new bridge.
-/

namespace PaperC
namespace LaplaceVoidClosure

open scoped BigOperators

open ArratiaGoldsteinGordonInput
open IndependentThinning
open PoissonVoidApproximation
open SpatialThinningFinite

noncomputable section

universe u v

/-- The thinned indicator count is the previously defined thinned count. -/
theorem indicatorSum_thinnedIndicator_eq_thinnedCount
    {Ω : Type u} {ι : Type v}
    [Fintype ι] [DecidableEq ι]
    (X : ι → Ω → Bool) (z : Ω × (ι → Bool)) :
    indicatorSum (thinnedIndicator X) z =
      thinnedCount (fun i ↦ X i z.1) z.2 := by
  classical
  unfold indicatorSum thinnedCount
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    thinnedIndicator_eq_true_iff]

/-- Zero thinned count is exactly the no-retained-active event. -/
theorem indicatorSum_thinnedIndicator_eq_zero_iff
    {Ω : Type u} {ι : Type v}
    [Fintype ι] [DecidableEq ι]
    (X : ι → Ω → Bool) (z : Ω × (ι → Bool)) :
    indicatorSum (thinnedIndicator X) z = 0 ↔
      NoRetainedActive (fun i ↦ X i z.1) z.2 := by
  rw [indicatorSum_thinnedIndicator_eq_thinnedCount]
  exact thinnedCount_eq_zero_iff _ _

/-- Exact formula for the thinned Poisson parameter. -/
theorem poissonParameter_thinnedIndicator
    {Ω : Type u} {ι : Type v}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool)
    (q : ι → ℝ)
    (hq0 : ∀ i, 0 ≤ q i)
    (hq1 : ∀ i, q i ≤ 1) :
    poissonParameter
        (productPMF μ (bernoulliProductPMF q hq0 hq1))
        (thinnedIndicator X) =
      ∑ i, marginal μ X i * q i := by
  unfold poissonParameter
  apply Finset.sum_congr rfl
  intro i hi
  exact marginal_thinnedIndicator μ X q hq0 hq1 i

/--
Finite Laplace/void closure.  The expectation of the exponential functional
is within `4(b₁+b₂)` of `exp(-∑ pᵢqᵢ)`.
-/
theorem abs_exponentialFunctional_sub_exp_neg_parameter_le
    (hAGG : ArratiaGoldsteinGordonStatement)
    {Ω : Type} {ι : Type}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool)
    (G : SimpleGraph ι)
    (g : ι → ℝ) (hg : ∀ i, 0 ≤ g i)
    (hDependency :
      HasExactDependencyGraph
        (productPMF μ
          (bernoulliProductPMF
            (exponentialRetention g)
            (fun i ↦ exponentialRetention_nonneg g hg i)
            (fun i ↦ exponentialRetention_le_one g i)))
        (thinnedIndicator X) G) :
    |(∑ ω, μ.prob ω * exponentialFunctional g X ω) -
        Real.exp
          (-(∑ i,
            marginal μ X i * exponentialRetention g i))| ≤
      4 *
        (bOne
          (productPMF μ
            (bernoulliProductPMF
              (exponentialRetention g)
              (fun i ↦ exponentialRetention_nonneg g hg i)
              (fun i ↦ exponentialRetention_le_one g i)))
          (thinnedIndicator X) G +
        bTwo
          (productPMF μ
            (bernoulliProductPMF
              (exponentialRetention g)
              (fun i ↦ exponentialRetention_nonneg g hg i)
              (fun i ↦ exponentialRetention_le_one g i)))
          (thinnedIndicator X) G) := by
  let ν :=
    bernoulliProductPMF
      (exponentialRetention g)
      (fun i ↦ exponentialRetention_nonneg g hg i)
      (fun i ↦ exponentialRetention_le_one g i)
  let μprod := productPMF μ ν
  have hvoid :=
    abs_voidProbability_sub_exp_neg_parameter_le
      hAGG μprod (thinnedIndicator X) G hDependency
  have hevent :
      (fun z : Ω × (ι → Bool) ↦
        indicatorSum (thinnedIndicator X) z = 0) =
      (fun z ↦
        NoRetainedActive (fun i ↦ X i z.1) z.2) := by
    ext z
    exact indicatorSum_thinnedIndicator_eq_zero_iff X z
  rw [hevent,
    eventProbability_no_thinned_active_eq_exponentialFunctional
      μ X g hg] at hvoid
  have hparameter :
      poissonParameter μprod (thinnedIndicator X) =
        ∑ i, marginal μ X i * exponentialRetention g i := by
    exact poissonParameter_thinnedIndicator μ X
      (exponentialRetention g)
      (fun i ↦ exponentialRetention_nonneg g hg i)
      (fun i ↦ exponentialRetention_le_one g i)
  rw [hparameter] at hvoid
  exact hvoid

/--
Source-facing finite closure.  It is enough to prove the dependency graph
for the original indicators: independent thinning preserves that graph and
can only decrease both AGG terms.
-/
theorem abs_exponentialFunctional_sub_exp_neg_parameter_le_of_dependency
    (hAGG : ArratiaGoldsteinGordonStatement)
    {Ω : Type} {ι : Type}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool)
    (G : SimpleGraph ι)
    (g : ι → ℝ) (hg : ∀ i, 0 ≤ g i)
    (hDependency : HasExactDependencyGraph μ X G) :
    |(∑ ω, μ.prob ω * exponentialFunctional g X ω) -
        Real.exp
          (-(∑ i,
            marginal μ X i * exponentialRetention g i))| ≤
      4 * (bOne μ X G + bTwo μ X G) := by
  let q : ι → ℝ := exponentialRetention g
  have hq0 : ∀ i, 0 ≤ q i :=
    fun i ↦ exponentialRetention_nonneg g hg i
  have hq1 : ∀ i, q i ≤ 1 :=
    fun i ↦ exponentialRetention_le_one g i
  have hthinned :
      HasExactDependencyGraph
        (productPMF μ (bernoulliProductPMF q hq0 hq1))
        (thinnedIndicator X) G :=
    hasExactDependencyGraph_thinnedIndicator
      μ X G hDependency q hq0 hq1
  have hfinite :=
    abs_exponentialFunctional_sub_exp_neg_parameter_le
      hAGG μ X G g hg (by
        simpa only [q, hq0, hq1] using hthinned)
  have hbOne :=
    bOne_thinnedIndicator_le μ X G q hq0 hq1
  have hbTwo :=
    bTwo_thinnedIndicator_le μ X G q hq0 hq1
  calc
    |(∑ ω, μ.prob ω * exponentialFunctional g X ω) -
        Real.exp
          (-(∑ i,
            marginal μ X i * exponentialRetention g i))| ≤
      4 *
        (bOne
          (productPMF μ (bernoulliProductPMF q hq0 hq1))
          (thinnedIndicator X) G +
        bTwo
          (productPMF μ (bernoulliProductPMF q hq0 hq1))
          (thinnedIndicator X) G) := by
      simpa only [q, hq0, hq1] using hfinite
    _ ≤ 4 * (bOne μ X G + bTwo μ X G) :=
      mul_le_mul_of_nonneg_left
        (add_le_add hbOne hbTwo) (by norm_num)

end

end LaplaceVoidClosure
end PaperC
