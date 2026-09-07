import PaperCV282.SpatialMarkedTargetProjection
import PaperCV282.CompoundPoissonTarget
import PaperC.Analysis.SpatialMarkedParameters

/-!
# Actual Laplace integrals of the spatial marked target

The integral is under the complete configuration law. A finite mark test is
transported through its proved product-Poisson projection before evaluating it.
-/
namespace PaperC.V282.SpatialMarkedTargetLaplace

open MeasureTheory ProbabilityTheory SpatialMarkedTypes SpatialMarkedTarget
open SpatialMarkedTargetProjection PoissonFieldMeasure CompoundPoissonTarget
open ExactMarkedModel ExactMarkedFieldTransfer ConditionalStartProbability
open SpatialMarkedParameters
open scoped BigOperators NNReal ENNReal Topology

noncomputable section

theorem integral_field_laplace {I : Type*} [Fintype I] (rate : I → ℝ≥0) (g : I → ℝ) :
    (∫ k : I → ℕ, Real.exp (-(∑ i, g i*(k i : ℝ))) ∂fieldMeasure rate) =
      Real.exp (-(∑ i, (rate i : ℝ)*(1-Real.exp (-g i)))) := by
  have heq (k : I → ℕ) : Real.exp (-(∑ i, g i*(k i : ℝ))) =
      ∏ i, (Real.exp (-g i)) ^ k i := by
    rw [← Finset.sum_neg_distrib,Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i hi
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp_rw [heq]
  have hd := (independent_coordinates rate).comp
    (fun i => fun n : ℕ => (Real.exp (-g i))^n) (fun _ => measurable_of_countable _)
  have hp := hd.integral_fun_prod_eq_prod_integral
    (fun i => ((measurable_of_countable (fun n : ℕ => (Real.exp (-g i))^n)).comp
      (measurable_pi_apply i)).aestronglyMeasurable)
  simp only [Function.comp_apply] at hp
  rw [hp]
  have hi (i : I) : (∫ k : I → ℕ, (Real.exp (-g i))^k i ∂fieldMeasure rate) =
      Real.exp ((rate i : ℝ)*(Real.exp (-g i)-1)) :=
    ((hasLaw_coordinate rate i).integral_comp
      (measurable_of_countable (fun n : ℕ => (Real.exp (-g i))^n)).aestronglyMeasurable).trans
        (integral_poisson_powers (rate i) _)
  simp_rw [hi]
  rw [← Real.exp_sum,← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

def finiteSpatialLaplaceExpectation (N L E : ℕ) (g : ℝ → ℕ → F₂ → ℝ) : ℝ :=
  ∫ config, Real.exp (-(∑ i : SignedMarkIndex N E,
    g ((i.1.val : ℝ)/(N : ℝ)) i.2.1.val i.2.2 * (projectConfiguration N E config i : ℝ)))
      ∂spatialTargetMeasure N L

def signedSpatialParameter (N L E : ℕ) (g : ℝ → ℕ → F₂ → ℝ) : ℝ :=
  ∑ i : SignedMarkIndex N E, (signedMarkRate L i.2.1.val : ℝ)*
    (1-Real.exp (-g ((i.1.val : ℝ)/(N : ℝ)) i.2.1.val i.2.2))

theorem finiteSpatialLaplace_eq (N L E : ℕ) (g : ℝ → ℕ → F₂ → ℝ) :
    finiteSpatialLaplaceExpectation N L E g = Real.exp (-signedSpatialParameter N L E g) := by
  have h := (hasLaw_projectConfiguration N L E).integral_comp
    (measurable_of_countable (fun k : SignedMarkIndex N E → ℕ => Real.exp (-(∑ i,
      g ((i.1.val : ℝ)/(N : ℝ)) i.2.1.val i.2.2*(k i : ℝ))))).aestronglyMeasurable
  have hh := h.trans (integral_field_laplace (allSignedRates N L E (dyadicBlock N))
    (fun i => g ((i.1.val : ℝ)/(N : ℝ)) i.2.1.val i.2.2))
  have hr (i : SignedMarkIndex N E) :
      allSignedRates N L E (dyadicBlock N) i = signedMarkRate L i.2.1.val := if_pos i.1.property
  simpa only [finiteSpatialLaplaceExpectation,signedSpatialParameter,Function.comp_apply,hr] using hh

theorem signedSpatialParameter_eq (N L E : ℕ) (g : ℝ → ℕ → F₂ → ℝ) :
    signedSpatialParameter N L E g =
      (1/2 : ℝ)*∑ s : F₂, markedThinnedParameter N L E (fun t e => g t e s) := by
  classical
  unfold signedSpatialParameter
  simp only [Fintype.sum_prod_type]
  calc
    _ = ∑ x : {x : ℕ // x ∈ dyadicBlock N}, ∑ s : F₂, ∑ e : Fin (E+1),
        (signedMarkRate L e.val : ℝ)*(1-Real.exp (-g ((x.val : ℝ)/N) e.val s)) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact Finset.sum_comm
    _ = ∑ s : F₂, ∑ x : {x : ℕ // x ∈ dyadicBlock N}, ∑ e : Fin (E+1),
        (signedMarkRate L e.val : ℝ)*(1-Real.exp (-g ((x.val : ℝ)/N) e.val s)) := Finset.sum_comm
    _ = ∑ s : F₂, (1/2 : ℝ)*markedThinnedParameter N L E (fun t e => g t e s) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [markedThinnedParameter_eq_literal]
      unfold literalMarkedThinnedParameter
      rw [Finset.mul_sum,Finset.sum_coe_sort (dyadicBlock N)
        (fun x => ∑ e : Fin (E+1), (signedMarkRate L e.val : ℝ)*
          (1-Real.exp (-g ((x : ℝ)/N) e.val s)))]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Fin.sum_univ_eq_sum_range
        (fun e => (signedMarkRate L e : ℝ)*(1-Real.exp (-g ((x : ℝ)/N) e s))) (E+1),
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      change (1/(2 : ℝ)^(L+e+2))*(1-Real.exp (-g ((x : ℝ)/N) e s)) =
        (1/2 : ℝ)*((1-Real.exp (-g ((x : ℝ)/N) e s))/(2 : ℝ)^(L+e+1))
      rw [show L+e+2=(L+e+1)+1 by omega,pow_succ]
      ring
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- The actual finite-mark target Laplace integrals converge along every converging intensity scale. -/
theorem finiteSpatialLaplace_tendsto {N L : ℕ → ℕ} {rate : ℝ} (E : ℕ)
    (g : ℝ → ℕ → F₂ → ℝ) (hN : Filter.Tendsto N Filter.atTop Filter.atTop)
    (hrate : Filter.Tendsto (fun n => criticalSpatialScale (N n) (L n)) Filter.atTop (𝓝 rate))
    (hg : ∀ e ≤ E, ∀ s, ContinuousOn (fun t => g t e s) (Set.Icc (1 : ℝ) 2)) :
    Filter.Tendsto (fun n => finiteSpatialLaplaceExpectation (N n) (L n) E g) Filter.atTop
      (𝓝 (Real.exp (-((1/2 : ℝ)*∑ s : F₂, rate*
        ∫ t in Set.Ico (1 : ℝ) 2, markedRetentionIntegrand E (fun u e => g u e s) t)))) := by
  have hs : Filter.Tendsto
      (fun n => ∑ s : F₂, markedThinnedParameter (N n) (L n) E (fun t e => g t e s))
      Filter.atTop (𝓝 (∑ s : F₂, rate*
        ∫ t in Set.Ico (1 : ℝ) 2, markedRetentionIntegrand E (fun u e => g u e s) t)) := by
    apply tendsto_finsetSum
    intro s hs
    exact tendsto_markedThinnedParameter hN hrate (fun e he => hg e he s)
  simpa only [finiteSpatialLaplace_eq,signedSpatialParameter_eq,Function.comp_def] using
    Real.continuous_exp.continuousAt.tendsto.comp ((hs.const_mul (1/2 : ℝ)).neg)

end
end PaperC.V282.SpatialMarkedTargetLaplace
