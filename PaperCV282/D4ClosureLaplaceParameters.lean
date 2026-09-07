import PaperCV282.SpatialMarkedTargetLaplace

/-! # Finite spatial Laplace parameters with a moving bounded intensity

The Riemann error is independent of the intensity. No convergent phase is
required to compare the lattice law with its moving deterministic parameter.
-/
namespace PaperC.V282.D4ClosureLaplaceParameters

open MeasureTheory Filter Topology Real SpatialMarkedParameters SpatialRiemannSums
open SpatialMarkedTargetLaplace
open scoped BigOperators

noncomputable section

def markedRiemannParameter (N E : ℕ) (g : ℝ → ℕ → ℝ) : ℝ :=
  ∑ e ∈ Finset.range (E+1), geometricMarkWeight e *
    dyadicRiemannSum N (spatialRetention (fun t => g t e))

theorem marked_parameter_factorization {N L : ℕ} (hN : 0 < N)
    (E : ℕ) (g : ℝ → ℕ → ℝ) :
    markedThinnedParameter N L E g =
      criticalSpatialScale N L * markedRiemannParameter N E g := by
  unfold markedThinnedParameter markedRiemannParameter
  simp_rw [spatialThinnedParameter_eq_scale_mul hN]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  ring

theorem marked_riemann_tendsto (sizes : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop)
    (E : ℕ) (g : ℝ → ℕ → ℝ)
    (hg : ∀ e ≤ E, ContinuousOn (fun t => g t e) (Set.Icc (1 : ℝ) 2)) :
    Tendsto (fun n => markedRiemannParameter (sizes n) E g) atTop
      (𝓝 (∫ t in Set.Ico (1 : ℝ) 2, markedRetentionIntegrand E g t)) := by
  rw [integral_markedRetentionIntegrand hg]
  apply tendsto_finsetSum
  intro e he
  exact ((tendsto_dyadicRiemannSum_of_continuousOn
    (continuousOn_spatialRetention (hg e (by simpa using Finset.mem_range.mp he)))).comp
      hsizes).const_mul _

theorem bounded_scale_riemann_error (sizes lengths : ℕ → ℕ)
    (hsizes : Tendsto sizes atTop atTop) (K : ℝ)
    (hK : ∀ᶠ n in atTop, criticalSpatialScale (sizes n) (lengths n) ≤ K)
    (E : ℕ) (g : ℝ → ℕ → ℝ)
    (hg : ∀ e ≤ E, ContinuousOn (fun t => g t e) (Set.Icc (1 : ℝ) 2)) :
    Tendsto (fun n => markedThinnedParameter (sizes n) (lengths n) E g -
      criticalSpatialScale (sizes n) (lengths n) *
        ∫ t in Set.Ico (1 : ℝ) 2, markedRetentionIntegrand E g t) atTop (𝓝 0) := by
  have herr := (marked_riemann_tendsto sizes hsizes E g hg).sub_const
    (∫ t in Set.Ico (1 : ℝ) 2, markedRetentionIntegrand E g t)
  simp only [sub_self] at herr
  refine squeeze_zero_norm' ?_ (by simpa only [abs_zero,mul_zero] using herr.abs.const_mul K)
  filter_upwards [hsizes.eventually (eventually_ge_atTop (1 : ℕ)),hK] with n hn hk
  rw [marked_parameter_factorization (by omega),← mul_sub,Real.norm_eq_abs,abs_mul,
    abs_of_nonneg (by unfold criticalSpatialScale; positivity)]
  exact mul_le_mul_of_nonneg_right hk (abs_nonneg _)

theorem unsigned_parameter_eq (N L E : ℕ) (g : ℝ → ℕ → ℝ) :
    signedSpatialParameter N L E (fun t e _ => g t e) =
      markedThinnedParameter N L E g := by
  rw [signedSpatialParameter_eq]
  simp

theorem exp_moving_error {a b : ℕ → ℝ}
    (hb : ∀ n, 0 ≤ b n) (h : Tendsto (fun n => a n-b n) atTop (𝓝 0)) :
    Tendsto (fun n => exp (-a n)-exp (-b n)) atTop (𝓝 0) := by
  have he := (Real.continuous_exp.continuousAt.tendsto.comp h.neg).sub_const 1
  simp only [neg_zero,exp_zero,sub_self] at he
  refine squeeze_zero_norm (fun n => ?_) (by simpa only [abs_zero] using he.abs)
  have hid : exp (-a n)-exp (-b n) =
      exp (-b n)*(exp (-(a n-b n))-1) := by
    rw [mul_sub,← exp_add,mul_one,show -b n+ -(a n-b n) = -a n by ring]
  rw [hid,Real.norm_eq_abs,abs_mul,abs_of_pos (exp_pos _)]
  exact mul_le_of_le_one_left (abs_nonneg _) (exp_le_one_iff.mpr (neg_nonpos.mpr (hb n)))

/-- The actual complete target law has the moving Laplace parameter, without a phase limit. -/
theorem finite_laplace_moving_error (sizes lengths : ℕ → ℕ)
    (hsizes : Tendsto sizes atTop atTop) (K : ℝ)
    (hK : ∀ᶠ n in atTop, criticalSpatialScale (sizes n) (lengths n) ≤ K)
    (E : ℕ) (g : ℝ → ℕ → ℝ)
    (hg : ∀ e ≤ E, ContinuousOn (fun t => g t e) (Set.Icc (1 : ℝ) 2))
    (hg0 : ∀ t e, 0 ≤ g t e) :
    Tendsto (fun n => finiteSpatialLaplaceExpectation (sizes n) (lengths n) E
        (fun t e _ => g t e) -
      exp (-(criticalSpatialScale (sizes n) (lengths n) *
        ∫ t in Set.Ico (1 : ℝ) 2, markedRetentionIntegrand E g t))) atTop (𝓝 0) := by
  simp_rw [finiteSpatialLaplace_eq,unsigned_parameter_eq]
  apply exp_moving_error _ (bounded_scale_riemann_error sizes lengths hsizes K hK E g hg)
  intro n
  apply mul_nonneg (by unfold criticalSpatialScale; positivity)
  exact integral_nonneg (markedRetentionIntegrand_nonneg hg0)

end
end PaperC.V282.D4ClosureLaplaceParameters
