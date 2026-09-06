import PaperCV282.FiniteFieldPoissonCoupling

/-!
# Explicit process Arratia-Goldstein-Gordon interface

Primary source: Arratia, Goldstein and Gordon, Annals of Probability 17 (1989),
9-25, Theorem 2, printed page 11.
https://dornsife.usc.edu/larry-goldstein/wp-content/uploads/sites/221/2023/06/AGG-1.pdf

The source norm is twice the half-L1 distance used here. Its process bound
2(2*b1+2*b2+b3) therefore gives 2(b1+b2) when the exact graph makes b3 zero.
The finite specialization includes zero coordinates by deleting deterministic
zeros and restoring them in both laws. The empty family is deterministic.
This published process input is a visible Prop argument, never a Lean axiom.
It does not follow from the earlier scalar AGG statement.
-/

namespace PaperC.V282.ProcessAGGInput

open ArratiaGoldsteinGordonInput FiniteFieldTotalVariation FiniteFieldPoissonCoupling
open scoped BigOperators NNReal

noncomputable section

def indicatorField {Ω ι : Type*} (X : ι → Ω → Bool) (ω : Ω) (i : ι) : ℕ :=
  if X i ω = true then 1 else 0

def fieldRates {Ω ι : Type*} [Fintype Ω] (μ : FinitePMF Ω)
    (X : ι → Ω → Bool) (i : ι) : ℝ≥0 :=
  ⟨marginal μ X i, marginal_nonneg μ X i⟩

theorem indicatorField_active {Ω ι : Type*} (X : ι → Ω → Bool) (ω : Ω) (i : ι) :
    indicatorField X ω i ≠ 0 ↔ X i ω = true := by
  cases h : X i ω <;> simp [indicatorField, h]

theorem eventProbability_indicatorField_active {Ω ι : Type*} [Fintype Ω]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool) (i : ι) :
    eventProbability μ (fun ω => indicatorField X ω i ≠ 0) = marginal μ X i := by
  classical
  unfold eventProbability marginal
  apply Finset.sum_congr rfl
  intro ω _
  cases h : X i ω <;> simp [indicatorField, h]

def retainedIndicators {Ω ι : Type*} (good : Finset ι) (X : ι → Ω → Bool)
    (i : ι) (ω : Ω) : Bool := by
  classical
  exact if i ∈ good then X i ω else false

theorem indicatorField_retainedIndicators {Ω ι : Type*} (good : Finset ι)
    (X : ι → Ω → Bool) :
    indicatorField (retainedIndicators good X) = retainedField good (indicatorField X) := by
  classical
  funext ω i
  by_cases hi : i ∈ good <;> simp [indicatorField, retainedIndicators, retainedField, hi]

theorem fieldRates_retainedIndicators {Ω ι : Type*} [Fintype Ω] (μ : FinitePMF Ω)
    (good : Finset ι) (X : ι → Ω → Bool) :
    fieldRates μ (retainedIndicators good X) = retainedRates good (fieldRates μ X) := by
  classical
  funext i
  by_cases hi : i ∈ good
  · simp only [retainedRates, if_pos hi]
    apply NNReal.eq
    change marginal μ (retainedIndicators good X) i = marginal μ X i
    simp only [retainedIndicators, if_pos hi, marginal, eventProbability]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h : X i ω = true <;> simp [h]
  · simp only [retainedRates, if_neg hi]
    apply NNReal.eq
    change marginal μ (retainedIndicators good X) i = 0
    simp [retainedIndicators, marginal, eventProbability, hi]

def ProcessAGGStatement : Prop :=
  ∀ (Ω ι : Type) [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool) (G : SimpleGraph ι),
    HasExactDependencyGraph μ X G →
      massTotalVariation (finiteFieldLaw μ (indicatorField X)) (poissonFieldMass (fieldRates μ X)) ≤
        2 * (bOne μ X G + bTwo μ X G)

theorem process_totalVariation_le (hAGG : ProcessAGGStatement)
    {Ω ι : Type} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool) (G : SimpleGraph ι)
    (hdep : HasExactDependencyGraph μ X G) :
    massTotalVariation (finiteFieldLaw μ (indicatorField X)) (poissonFieldMass (fieldRates μ X)) ≤
      2 * (bOne μ X G + bTwo μ X G) :=
  hAGG Ω ι μ X G hdep

theorem process_totalVariation_with_target_rates (hAGG : ProcessAGGStatement)
    {Ω ι : Type} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool) (G : SimpleGraph ι)
    (hdep : HasExactDependencyGraph μ X G) (target : ι → ℝ≥0) :
    massTotalVariation (finiteFieldLaw μ (indicatorField X)) (poissonFieldMass target) ≤
      2 * (bOne μ X G + bTwo μ X G) +
        ∑ i, |marginal μ X i - (target i : ℝ)| := by
  have hprocess := process_totalVariation_le hAGG μ X G hdep
  have htarget := massTotalVariation_poissonField_le_sum_abs (fieldRates μ X) target
  have htriangle := massTotalVariation_triangle
    (summable_finiteFieldLaw μ (indicatorField X))
    (summable_poissonFieldMass (fieldRates μ X)) (summable_poissonFieldMass target)
    (finiteFieldLaw_nonneg μ (indicatorField X))
    (poissonFieldMass_nonneg (fieldRates μ X)) (poissonFieldMass_nonneg target)
  exact htriangle.trans (add_le_add hprocess htarget)

theorem process_totalVariation_via_retention (hAGG : ProcessAGGStatement)
    {Ω ι : Type} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (μ : FinitePMF Ω) (X : ι → Ω → Bool) (good : Finset ι) (target : ι → ℝ≥0)
    (G : SimpleGraph ι) (hdep : HasExactDependencyGraph μ (retainedIndicators good X) G)
    (hrates : fieldRates μ (retainedIndicators good X) = retainedRates good target) :
    massTotalVariation (finiteFieldLaw μ (indicatorField X)) (poissonFieldMass target) ≤
      (∑ i ∈ badFieldSites good, marginal μ X i) +
        2 * (bOne μ (retainedIndicators good X) G + bTwo μ (retainedIndicators good X) G) +
          ∑ i ∈ badFieldSites good, (target i : ℝ) := by
  have hprocess := process_totalVariation_le hAGG μ (retainedIndicators good X) G hdep
  rw [indicatorField_retainedIndicators, hrates] at hprocess
  have h := field_comparison_via_retention μ (indicatorField X) good target hprocess
  simpa only [eventProbability_indicatorField_active] using h

end

end PaperC.V282.ProcessAGGInput
