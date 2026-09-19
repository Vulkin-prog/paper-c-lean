import PaperCPrel8.EmpiricalWindowConvergence
import PaperCV282.GeometricSaddleSummability

/-! # Numerical ingredients for dyadic empirical count limits

The full microscopic error is summable on the actual dyadic heights. Rounding
a window floor(tau/p) perturbs its Poisson mean by at most p. These statements
do not assume summability or mean convergence of the final empirical error.
-/
namespace PaperC.Prel8.EmpiricalScaleBounds
open Filter Topology MeasureTheory ProbabilityTheory
open PaperC.V282.GeometricSaddleSummability PaperC.V282.SaddleParameters
open PaperC.V282.SaddleScales
open scoped NNReal
noncomputable section

/-- Literal powers of two satisfy the geometric growth hypothesis. -/
theorem dyadic_geometric_growth : GeometricLowerGrowth (fun k => 2^k) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1/Real.log 2, by positivity, Eventually.of_forall fun k => ?_⟩
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  field_simp
  rfl

/-- The proved full-field error is summable along every geometrically growing sequence. -/
theorem summable_full_error {sizes : ℕ → ℕ} (hg : GeometricLowerGrowth sizes)
    {c epsilon : ℝ} (hc : 0 < c) (he : epsilon < 1/3) :
    Summable (fun k => 10*Real.exp (-c*saddleNu 1 (Real.log (sizes k)))+
      4*(sizes k:ℝ)^(-(1/(3:ℝ))+epsilon)) := by
  have hx := (summable_exp_neg_nu hg (by norm_num : (0:ℝ)<1) hc).mul_left 10
  have hp := (summable_size_rpow_neg hg (by linarith : 0<1/3-epsilon)).mul_left 4
  simpa only [show -(1/(3:ℝ)-epsilon)= -(1/(3:ℝ))+epsilon by ring] using hx.add hp

/-- In particular the literal dyadic field-comparison error is summable. -/
theorem summable_dyadic_full_error {c epsilon : ℝ} (hc : 0 < c) (he : epsilon < 1/3) :
    Summable (fun k : ℕ => 10*Real.exp (-c*saddleNu 1 (Real.log (2^k:ℕ)))+
      4*((2^k:ℕ):ℝ)^(-(1/(3:ℝ))+epsilon)) :=
  summable_full_error dyadic_geometric_growth hc he

/-- Rounding the window length changes its mean by less than one site rate. -/
theorem floor_window_mean_error {tau p : ℝ} (ht : 0 ≤ tau) (hp : 0 < p) :
    0 ≤ tau-(⌊tau/p⌋₊:ℝ)*p ∧ tau-(⌊tau/p⌋₊:ℝ)*p < p := by
  have hlow := Nat.floor_le (div_nonneg ht hp.le)
  have hhi := Nat.lt_floor_add_one (tau/p)
  have hle : (⌊tau/p⌋₊:ℝ)*p ≤ tau := (le_div_iff₀ hp).mp hlow
  have hlt : tau < ((⌊tau/p⌋₊:ℝ)+1)*p := (div_lt_iff₀ hp).mp hhi
  constructor <;> linarith

/-- Vanishing site rates imply convergence of the actual rounded window mean. -/
theorem floor_window_mean_tendsto (tau : ℝ) (ht : 0 ≤ tau) (p : ℕ → ℝ)
    (hp : ∀ k, 0 < p k) (hpzero : Tendsto p atTop (𝓝 0)) :
    Tendsto (fun k => (⌊tau/p k⌋₊:ℝ)*p k) atTop (𝓝 tau) := by
  have hd : Tendsto (fun k => tau-(⌊tau/p k⌋₊:ℝ)*p k) atTop (𝓝 0) :=
    squeeze_zero (fun k => (floor_window_mean_error ht (hp k)).1)
      (fun k => (floor_window_mean_error ht (hp k)).2.le) hpzero
  simpa using (tendsto_const_nhds (x := tau)).sub hd

/-- Poisson singleton probabilities are continuous in their actual mean. -/
theorem poisson_mass_tendsto (p : ℕ → ℝ≥0) (tau : ℝ≥0)
    (hp : Tendsto (fun k => (p k:ℝ)) atTop (𝓝 (tau:ℝ))) (r : ℕ) :
    Tendsto (fun k => (poissonMeasure (p k)).real {r}) atTop
      (𝓝 ((poissonMeasure tau).real {r})) := by
  simp_rw [poissonMeasure_real_singleton]
  exact (((Real.continuous_exp.tendsto _).comp hp.neg).mul (hp.pow r)).div_const _

end
end PaperC.Prel8.EmpiricalScaleBounds
