import PaperCV282.PoissonQuantitativeLocal

/-! # Relative Gaussian local limits with bounded rounding

The comparison is at the actual Poisson atom, with the standard normal density
and the true lattice mesh. The observation can be any integer within a fixed
bounded distance of rate+t*sqrt(rate), including either rounding convention.
-/
namespace PaperC.V282.PoissonQuantitativeCentral

open MeasureTheory ProbabilityTheory Filter Topology Real PoissonStirlingBounds
open PoissonCentralAsymptotics PoissonQuantitativeLocal
open scoped NNReal

noncomputable section

/-- The cubic central hypothesis forces the actual observations to infinity. -/
theorem observations_tendsto_atTop (rate value : ℕ→ℝ)
    (hrate : Tendsto rate atTop atTop)
    (hthird : Tendsto (fun k => |value k-rate k|^3/(rate k)^2) atTop (𝓝 0)) :
    Tendsto value atTop atTop := by
  have hr := ratio_tendsto_one_of_cubic rate value hrate hthird
  apply tendsto_atTop_mono' atTop ?_ (hrate.const_mul_atTop (by norm_num : (0 : ℝ)<1/2))
  filter_upwards [hrate.eventually (eventually_gt_atTop (0 : ℝ)),
    hr.eventually (lt_mem_nhds (by norm_num : (1/2 : ℝ)<1))] with k hk hh
  have h := (lt_div_iff₀ hk).mp hh
  linarith

/-- Robbins' remainder vanishes along the actual observation sequence. -/
theorem stirlingLogError_tendsto_zero (n : ℕ→ℕ)
    (hn : Tendsto (fun k => (n k : ℝ)) atTop atTop) :
    Tendsto (fun k => stirlingLogError (n k)) atTop (𝓝 0) := by
  have hi : Tendsto (fun k => 1/(12*(n k : ℝ))) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop (hn.const_mul_atTop (by norm_num : (0 : ℝ)<12))
  have hp : ∀ᶠ k in atTop,0<n k := by
    filter_upwards [hn.eventually (eventually_gt_atTop (0 : ℝ))] with k hk
    exact_mod_cast hk
  exact squeeze_zero' (hp.mono fun _ h => stirlingLogError_nonneg h)
    (hp.mono fun _ h => stirlingLogError_le h) hi

/-- No rate of growth or sign restriction on the moving central coordinate is needed. -/
theorem localLogCorrection_tendsto_zero (rate : ℕ→ℝ) (n : ℕ→ℕ) (t : ℕ→ℝ) (K : ℝ)
    (hrate : Tendsto rate atTop atTop)
    (ht : Tendsto (fun k => t k/(rate k)^(1/6 : ℝ)) atTop (𝓝 0))
    (hround : ∀ᶠ k in atTop,|(n k : ℝ)-(rate k+t k*sqrt (rate k))|≤K) :
    Tendsto (fun k => localLogCorrection (rate k) (n k) (t k)) atTop (𝓝 0) := by
  obtain ⟨hl,he⟩ := bounded_rounding_central_errors rate n t K hrate ht hround
  have hthird := cubic_error_tendsto_zero_of_bounded_rounding rate (fun k => (n k : ℝ)) t K hrate ht hround
  have hs := stirlingLogError_tendsto_zero n (observations_tendsto_atTop rate (fun k => (n k : ℝ)) hrate hthird)
  have hh := ((hl.neg.div_const 2).sub hs).sub he
  simpa only [neg_zero,zero_div,sub_zero,neg_sub,localLogCorrection] using hh

/-- The true Poisson local probability is asymptotic to phi(t)/sqrt(rate), relatively. -/
theorem poisson_gaussian_local_ratio_tendsto_one (rates : ℕ→ℝ≥0) (n : ℕ→ℕ) (t : ℕ→ℝ) (K : ℝ)
    (hrate : Tendsto (fun k => (rates k : ℝ)) atTop atTop)
    (ht : Tendsto (fun k => t k/(rates k : ℝ)^(1/6 : ℝ)) atTop (𝓝 0))
    (hround : ∀ᶠ k in atTop,|(n k : ℝ)-((rates k : ℝ)+t k*sqrt (rates k))|≤K) :
    Tendsto (fun k => (poissonMeasure (rates k)).real {n k}/gaussianLatticeMass (rates k) (t k))
      atTop (𝓝 1) := by
  have he := Real.continuous_exp.continuousAt.tendsto.comp
    (localLogCorrection_tendsto_zero (fun k => (rates k : ℝ)) n t K hrate ht hround)
  simp only [Real.exp_zero,Function.comp_def] at he
  have hthird := cubic_error_tendsto_zero_of_bounded_rounding (fun k => (rates k : ℝ))
    (fun k => (n k : ℝ)) t K hrate ht hround
  have hn := observations_tendsto_atTop (fun k => (rates k : ℝ)) (fun k => (n k : ℝ)) hrate hthird
  apply he.congr'
  filter_upwards [hrate.eventually (eventually_gt_atTop (0 : ℝ)),
    hn.eventually (eventually_gt_atTop (0 : ℝ))] with k hr hp
  have hnat : 0<n k := by exact_mod_cast hp
  rw [poisson_atom_exact (rates k) hr hnat (t k),
    mul_div_cancel_right₀ _ (gaussianLatticeMass_pos (rate := (rates k : ℝ)) hr (t k)).ne']

/-- The central local limit in the standard Gaussian density notation used in D.1. -/
theorem poisson_scaled_atom_div_density_tendsto_one (rates : ℕ→ℝ≥0) (n : ℕ→ℕ) (t : ℕ→ℝ) (K : ℝ)
    (hrate : Tendsto (fun k => (rates k : ℝ)) atTop atTop)
    (ht : Tendsto (fun k => t k/(rates k : ℝ)^(1/6 : ℝ)) atTop (𝓝 0))
    (hround : ∀ᶠ k in atTop,|(n k : ℝ)-((rates k : ℝ)+t k*sqrt (rates k))|≤K) :
    Tendsto (fun k => sqrt (rates k)*(poissonMeasure (rates k)).real {n k}/gaussianPDFReal 0 1 (t k))
      atTop (𝓝 1) := by
  apply (poisson_gaussian_local_ratio_tendsto_one rates n t K hrate ht hround).congr'
  filter_upwards [hrate.eventually (eventually_gt_atTop (0 : ℝ))] with k hk
  rw [gaussianLatticeMass_eq_density hk]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

end
end PaperC.V282.PoissonQuantitativeCentral
