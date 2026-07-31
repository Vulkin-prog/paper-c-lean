import PaperC.Probability.SectionThirteenFiniteBound

set_option maxHeartbeats 1200000

/-!
# From finite Poisson approximation to void probabilities

The point-process arguments in Section 14 use Arratia--Goldstein--Gordon
only through the probability that a thinned indicator family is empty.
This file supplies that conversion once and for all.  It is entirely finite:
the zero atom of the indicator-sum law differs from
`exp (-∑ pᵢ)` by at most twice its total-variation distance, and hence by
`4 (b₁+b₂)` under the convention used in the paper.
-/

namespace PaperC
namespace PoissonVoidApproximation

open scoped BigOperators NNReal

open ProbabilityTheory
open ArratiaGoldsteinGordonInput
open SectionThirteenFiniteBound

noncomputable section

universe u v

/-- The AGG indicator-sum law is the generic finite pushforward law. -/
theorem indicatorSumLaw_eq_finiteNatLaw
    {Ω : Type u} {ι : Type v} [Fintype Ω] [Fintype ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool) :
    indicatorSumLaw μ X =
      finiteNatLaw μ (indicatorSum X) := by
  classical
  funext k
  unfold indicatorSumLaw finiteNatLaw eventProbability
  apply Finset.sum_congr rfl
  intro ω _hω
  by_cases h : indicatorSum X ω = k <;> simp [h]

/-- The law of a finite indicator sum is summable. -/
theorem summable_indicatorSumLaw
    {Ω : Type u} {ι : Type v} [Fintype Ω] [Fintype ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool) :
    Summable (indicatorSumLaw μ X) := by
  rw [indicatorSumLaw_eq_finiteNatLaw]
  exact summable_finiteNatLaw μ (indicatorSum X)

/-- The matching Poisson mass function is summable. -/
theorem summable_matchingPoissonLaw
    {Ω : Type u} {ι : Type v} [Fintype Ω] [Fintype ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool) :
    Summable (matchingPoissonLaw μ X) := by
  have hmatching :
      matchingPoissonLaw μ X = fun k : ℕ ↦
        Real.exp (-(poissonRate μ X : ℝ)) *
          (poissonRate μ X : ℝ) ^ k / (Nat.factorial k : ℝ) := by
    rfl
  rw [hmatching]
  exact (hasSum_one_poissonMeasure (poissonRate μ X)).summable

/-- The zero atom of the matching Poisson law. -/
theorem matchingPoissonLaw_zero
    {Ω : Type u} {ι : Type v} [Fintype Ω] [Fintype ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool) :
    matchingPoissonLaw μ X 0 =
      Real.exp (-(poissonParameter μ X)) := by
  have hzero :
      matchingPoissonLaw μ X 0 =
        Real.exp (-(poissonRate μ X : ℝ)) *
          (poissonRate μ X : ℝ) ^ 0 / (Nat.factorial 0 : ℝ) := by
    rfl
  rw [hzero]
  norm_num
  rfl

/-- A single atom is bounded by twice half-`ℓ¹` total variation. -/
theorem abs_mass_zero_sub_le_two_mul_natTotalVariation
    {p q : ℕ → ℝ}
    (hp : Summable p) (hq : Summable q)
    (hp0 : ∀ k, 0 ≤ p k) (hq0 : ∀ k, 0 ≤ q k) :
    |p 0 - q 0| ≤
      2 * natTotalVariation p q := by
  have hs :
      Summable fun k ↦ |p k - q k| :=
    summable_abs_sub_of_nonneg hp hq hp0 hq0
  let g : ℕ → ℝ :=
    fun k ↦ if k = 0 then |p k - q k| else 0
  have hg : HasSum g |p 0 - q 0| := by
    have hfun :
        g =
          fun k : ℕ ↦
            if k = 0 then |p 0 - q 0| else 0 := by
      funext k
      by_cases hk : k = 0
      · subst k
        simp [g]
      · simp [g, hk]
    rw [hfun]
    exact hasSum_ite_eq 0 (|p 0 - q 0| : ℝ)
  have hmono :
      g ≤ (fun k : ℕ ↦ |p k - q k|) := by
    intro k
    dsimp only [g]
    split_ifs
    · exact le_rfl
    · exact abs_nonneg _
  have hsingle :
      |p 0 - q 0| ≤ ∑' k : ℕ, |p k - q k| := by
    calc
      |p 0 - q 0| = ∑' k : ℕ, g k := hg.tsum_eq.symm
      _ ≤ ∑' k : ℕ, |p k - q k| :=
        hg.summable.tsum_le_tsum hmono hs
  unfold natTotalVariation
  linarith

/--
A zero-atom error is at most twice half-`ℓ¹` total variation.
-/
theorem abs_indicatorSumLaw_zero_sub_matching_le
    {Ω : Type u} {ι : Type v} [Fintype Ω] [Fintype ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool) :
    |indicatorSumLaw μ X 0 - matchingPoissonLaw μ X 0| ≤
      2 * totalVariationToPoisson μ X := by
  have h :=
    abs_mass_zero_sub_le_two_mul_natTotalVariation
      (summable_indicatorSumLaw μ X)
      (summable_matchingPoissonLaw μ X)
      (indicatorSumLaw_nonneg μ X)
      (fun k ↦ by
        rw [show matchingPoissonLaw μ X k =
            Real.exp (-(poissonRate μ X : ℝ)) *
              (poissonRate μ X : ℝ) ^ k / (Nat.factorial k : ℝ) by
          rfl]
        positivity)
  simpa only [natTotalVariation, totalVariationToPoisson] using h

/--
Void-probability form of AGG for an exact dependency graph.
-/
theorem abs_voidProbability_sub_exp_neg_parameter_le
    (hAGG : ArratiaGoldsteinGordonStatement)
    {Ω : Type} {ι : Type}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool)
    (G : SimpleGraph ι)
    (hDependency : HasExactDependencyGraph μ X G) :
    |eventProbability μ (fun ω ↦ indicatorSum X ω = 0) -
        Real.exp (-(poissonParameter μ X))| ≤
      4 * (bOne μ X G + bTwo μ X G) := by
  have hzero :=
    abs_indicatorSumLaw_zero_sub_matching_le μ X
  rw [matchingPoissonLaw_zero] at hzero
  have htv :=
    totalVariationToPoisson_le hAGG μ X G hDependency
  calc
    |eventProbability μ (fun ω ↦ indicatorSum X ω = 0) -
        Real.exp (-(poissonParameter μ X))| ≤
      2 * totalVariationToPoisson μ X := hzero
    _ ≤ 2 * (2 * (bOne μ X G + bTwo μ X G)) :=
      mul_le_mul_of_nonneg_left htv (by norm_num)
    _ = 4 * (bOne μ X G + bTwo μ X G) := by ring

end

end PoissonVoidApproximation
end PaperC
