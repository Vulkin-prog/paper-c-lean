import PaperCV282.SoftConditionalPoisson
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Soft retention under an arbitrary probability environment

The environment need not be finite. A measurable family of finite joint
indicator laws is enough, as obtained from conditional probabilities of
the finitely many Boolean patterns. This module proves measurability and
integrability of the actual total-variation distance before averaging.
-/

namespace PaperC.V282.SoftMeasureAverage

open MeasureTheory ArratiaGoldsteinGordonInput SectionThirteenFiniteBound
open ScalarSteinInput ScalarPoissonBounds SteinSoftTelescoping
open scoped BigOperators NNReal Topology

noncomputable section

variable {Θ Ω ι : Type*} [MeasurableSpace Θ] [Fintype Ω] [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- A finite pushforward is a measurable function of the joint-pattern masses. -/
theorem measurable_finiteNatLaw (μ : Θ → FinitePMF Ω)
    (hμ : ∀ ω, Measurable (fun θ => (μ θ).prob ω)) (W : Ω → ℕ) (k : ℕ) :
    Measurable (fun θ => finiteNatLaw (μ θ) W k) := by
  classical
  unfold finiteNatLaw
  apply Finset.measurable_sum
  intro ω _
  by_cases h : W ω = k
  · simpa only [h, if_true] using hμ ω
  · simpa only [h, if_false] using (measurable_const : Measurable (fun _ : Θ => (0 : ℝ)))

omit [Fintype ι] [DecidableEq ι] in
/-- The infinite sum in Poisson total variation is measurable by its finite partial sums. -/
theorem measurable_poissonDistance (μ : Θ → FinitePMF Ω)
    (hμ : ∀ ω, Measurable (fun θ => (μ θ).prob ω)) (W : Ω → ℕ) (rate : ℝ≥0) :
    Measurable (fun θ => natTotalVariation (finiteNatLaw (μ θ) W) (poissonMass rate)) := by
  have hsum : Measurable (fun θ => ∑' k, |finiteNatLaw (μ θ) W k - poissonMass rate k|) := by
    apply measurable_of_tendsto_metrizable
      (f := fun n θ => ∑ k ∈ Finset.range n, |finiteNatLaw (μ θ) W k - poissonMass rate k|)
    · intro n
      exact Finset.measurable_sum _ (fun k _ =>
        (continuous_abs.measurable.comp ((measurable_finiteNatLaw μ hμ W k).sub measurable_const)))
    · apply tendsto_pi_nhds.mpr
      intro θ
      exact (summable_abs_sub_of_nonneg (summable_finiteNatLaw _ _)
        (hasSum_poissonMass _).summable (finiteNatLaw_nonneg _ _)
        (poissonMass_nonneg _)).hasSum.tendsto_sum_nat
  exact hsum.const_mul (2 : ℝ)⁻¹

omit [Fintype ι] [DecidableEq ι] in
/-- Measurable finite-PMF masses are integrable under any probability environment. -/
theorem integrable_probability_mass (ν : Measure Θ) [IsProbabilityMeasure ν]
    (μ : Θ → FinitePMF Ω) (hμ : ∀ ω, Measurable (fun θ => (μ θ).prob ω)) (ω : Ω) :
    Integrable (fun θ => (μ θ).prob ω) ν := by
  apply (integrable_const (1 : ℝ)).mono' (hμ ω).aestronglyMeasurable
  apply ae_of_all
  intro θ
  rw [Real.norm_eq_abs, abs_of_nonneg ((μ θ).nonneg ω)]
  calc
    (μ θ).prob ω ≤ ∑ z, (μ θ).prob z :=
      Finset.single_le_sum (fun z _ => (μ θ).nonneg z) (Finset.mem_univ ω)
    _ = 1 := (μ θ).sum_prob

omit [Fintype ι] [DecidableEq ι] in
/-- All fixed pattern events have integrable conditional probabilities. -/
theorem integrable_eventProbability (ν : Measure Θ) [IsProbabilityMeasure ν]
    (μ : Θ → FinitePMF Ω) (hμ : ∀ ω, Measurable (fun θ => (μ θ).prob ω))
    (event : Ω → Prop) : Integrable (fun θ => eventProbability (μ θ) event) ν := by
  classical
  unfold eventProbability
  apply integrable_finsetSum
  intro ω _
  by_cases h : event ω
  · simpa only [h, if_true] using integrable_probability_mass ν μ hμ ω
  · simpa only [h, if_false] using (integrable_const (0 : ℝ) : Integrable (fun _ : Θ => (0 : ℝ)) ν)

/-- The soft error budget is integrable; exceptional neighbours retain their actual laws. -/
theorem integrable_soft_budget (ν : Measure Θ) [IsProbabilityMeasure ν]
    (μ : Θ → FinitePMF Ω) (hμ : ∀ ω, Measurable (fun θ => (μ θ).prob ω))
    (X : ι → Ω → Bool) (G : SimpleGraph ι) (good : Finset ι) (p : ℝ) (rate : ℝ≥0) :
    Integrable (fun θ => firstSteinFactor rate * goodSteinCost (μ θ) X G good p +
      zeroSteinFactor rate * ((Finset.univ \ good).card * p +
        ∑ i ∈ Finset.univ \ good, marginal (μ θ) X i)) ν := by
  classical
  have hm i : Integrable (fun θ => marginal (μ θ) X i) ν :=
    integrable_eventProbability ν μ hμ _
  have hj i j : Integrable (fun θ => jointMarginal (μ θ) X i j) ν :=
    integrable_eventProbability ν μ hμ _
  unfold goodSteinCost
  exact ((integrable_const _).add
    ((integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hm j))).const_mul p)
      |>.add (integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hj i j)))).const_mul _
    |>.add (((integrable_const _).add (integrable_finsetSum _ (fun i _ => hm i))).const_mul _)

/-- B.4 for an arbitrary probability environment, expressed through its finite conditional laws. -/
theorem lemma_b_two_integral (hStein : ScalarSteinFactorsStatement)
    (ν : Measure Θ) [IsProbabilityMeasure ν]
    (μ : Θ → FinitePMF Ω) (hμ : ∀ ω, Measurable (fun θ => (μ θ).prob ω))
    (X : ι → Ω → Bool) (G : SimpleGraph ι)
    (hdep : ∀ᵐ θ ∂ν, HasExactDependencyGraph (μ θ) X G) (good : Finset ι)
    {p : ℝ} (hp : 0 ≤ p)
    (hgood : ∀ᵐ θ ∂ν, ∀ i ∈ good, marginal (μ θ) X i = p)
    (rate : ℝ≥0) (hrate : (rate : ℝ) = (Fintype.card ι : ℝ) * p) :
    (∫ θ, natTotalVariation (finiteNatLaw (μ θ) (indicatorSum X)) (poissonMass rate) ∂ν) ≤
      firstSteinFactor rate *
        (good.card * p ^ 2 +
          p * (∑ i ∈ good, ∑ j ∈ (closedNeighborhood G i).erase i,
            ∫ θ, marginal (μ θ) X j ∂ν) +
          ∑ i ∈ good, ∑ j ∈ (closedNeighborhood G i).erase i,
            ∫ θ, jointMarginal (μ θ) X i j ∂ν) +
      zeroSteinFactor rate *
        ((Finset.univ \ good).card * p +
          ∑ i ∈ Finset.univ \ good, ∫ θ, marginal (μ θ) X i ∂ν) := by
  classical
  have hpoint : ∀ᵐ θ ∂ν,
      natTotalVariation (finiteNatLaw (μ θ) (indicatorSum X)) (poissonMass rate) ≤
        firstSteinFactor rate * goodSteinCost (μ θ) X G good p +
        zeroSteinFactor rate * ((Finset.univ \ good).card * p +
          ∑ i ∈ Finset.univ \ good, marginal (μ θ) X i) := by
    filter_upwards [hdep, hgood] with θ hd hg
    exact lemma_b_two_finite hStein (μ θ) X G hd good hp hg rate hrate
  have hbudget := integrable_soft_budget ν μ hμ X G good p rate
  have hdist : Integrable
      (fun θ => natTotalVariation (finiteNatLaw (μ θ) (indicatorSum X)) (poissonMass rate)) ν := by
    apply hbudget.mono' (measurable_poissonDistance μ hμ (indicatorSum X) rate).aestronglyMeasurable
    filter_upwards [hpoint] with θ ht
    simpa only [Real.norm_eq_abs, abs_of_nonneg (natTotalVariation_nonneg _ _)] using ht
  have h := integral_mono_ae hdist hbudget hpoint
  have hm i : Integrable (fun θ => marginal (μ θ) X i) ν := integrable_eventProbability ν μ hμ _
  have hj i j : Integrable (fun θ => jointMarginal (μ θ) X i j) ν := integrable_eventProbability ν μ hμ _
  have hM := integrable_finsetSum good (fun i _ =>
    integrable_finsetSum ((closedNeighborhood G i).erase i) (fun j _ => hm j))
  have hJ := integrable_finsetSum good (fun i _ =>
    integrable_finsetSum ((closedNeighborhood G i).erase i) (fun j _ => hj i j))
  have hB := integrable_finsetSum (Finset.univ \ good) (fun i _ => hm i)
  have hC : Integrable (fun θ => good.card * p ^ 2 +
      p * (∑ i ∈ good, ∑ j ∈ (closedNeighborhood G i).erase i, marginal (μ θ) X j) +
      ∑ i ∈ good, ∑ j ∈ (closedNeighborhood G i).erase i, jointMarginal (μ θ) X i j) ν :=
    ((integrable_const (good.card * p ^ 2)).add (hM.const_mul p)).add hJ
  unfold goodSteinCost at h
  have hsplit := integral_add (hC.const_mul (firstSteinFactor rate))
    (((integrable_const ((Finset.univ \ good).card * p)).add hB).const_mul (zeroSteinFactor rate))
  simp only [Pi.add_apply] at hsplit
  rw [hsplit] at h
  simp only [integral_const_mul] at h
  have hsplitJ := integral_add ((integrable_const (good.card * p ^ 2)).add (hM.const_mul p)) hJ
  have hsplitM := integral_add (integrable_const (good.card * p ^ 2)) (hM.const_mul p)
  have hsplitB := integral_add (integrable_const ((Finset.univ \ good).card * p)) hB
  simp only [Pi.add_apply] at hsplitJ hsplitM hsplitB
  rw [hsplitJ, hsplitM, hsplitB] at h
  simp only [integral_const_mul, integral_const, probReal_univ, one_smul] at h
  rw [integral_finsetSum good (fun i _ =>
      integrable_finsetSum ((closedNeighborhood G i).erase i) (fun j _ => hm j)),
    integral_finsetSum good (fun i _ =>
      integrable_finsetSum ((closedNeighborhood G i).erase i) (fun j _ => hj i j)),
    integral_finsetSum (Finset.univ \ good) (fun i _ => hm i)] at h
  simp_rw [integral_finsetSum _ (fun j _ => hm j),
    integral_finsetSum _ (fun j _ => hj _ j)] at h
  exact h

end
end PaperC.V282.SoftMeasureAverage
