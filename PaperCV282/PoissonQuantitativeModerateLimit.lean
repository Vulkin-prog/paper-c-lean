import PaperCV282.PoissonQuantitativeModerate

/-! # The full sixth-root moderate range, with the actual integer threshold -/
namespace PaperC.V282.PoissonQuantitativeModerateLimit

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open PoissonQuantitativeModerate PoissonQuantitativeMills
open scoped NNReal

noncomputable section

theorem sixth_root_cube {rate t : ℝ} (hr : 0<rate) :
    (t/rate^(1/6 : ℝ))^3=t^3/sqrt rate := by
  rw [div_pow,← rpow_mul_natCast hr.le,sqrt_eq_rpow]
  norm_num

theorem moderate_error_scale_tendsto_zero (rates t : ℕ→ℝ)
    (hrate : Tendsto rates atTop atTop)
    (ht : Tendsto (fun k => t k/(rates k)^(1/6 : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun k => (1+(t k)^3)/sqrt (rates k)) atTop (𝓝 0) := by
  have hc : Tendsto (fun k => (t k)^3/sqrt (rates k)) atTop (𝓝 0) := by
    have hh := ht.pow 3
    simp only [zero_pow (by norm_num : (3 : ℕ)≠0)] at hh
    apply hh.congr'
    filter_upwards [hrate.eventually (eventually_gt_atTop (0 : ℝ))] with k hk
    exact sixth_root_cube hk
  have hi : Tendsto (fun k => 1/sqrt (rates k)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_sqrt_atTop.comp hrate)
  simpa only [add_div,add_zero] using hi.add hc

/-- The effective error and its domain both hold eventually, before any integer threshold. -/
theorem moderate_domain_eventually (rates t : ℕ→ℝ)
    (hrate : Tendsto rates atTop atTop)
    (ht : Tendsto (fun k => t k/(rates k)^(1/6 : ℝ)) atTop (𝓝 0)) :
    ∀ᶠ k in atTop,4096≤rates k ∧ (t k)^3/sqrt (rates k)≤1 := by
  have hh := ht.pow 3
  simp only [zero_pow (by norm_num : (3 : ℕ)≠0)] at hh
  filter_upwards [hrate.eventually (eventually_ge_atTop (4096 : ℝ)),
    hh.eventually (eventually_le_nhds (by norm_num : (0 : ℝ)<1))] with k hk hc
  exact ⟨hk,by rwa [sixth_root_cube (by linarith : 0<rates k)] at hc⟩

/-- The upper-tail ratio in D.1, for every nonnegative moving moderate coordinate. -/
theorem poisson_moderate_ratio_tendsto_one (rates : ℕ→ℝ≥0) (t : ℕ→ℝ)
    (hrate : Tendsto (fun k => (rates k : ℝ)) atTop atTop)
    (ht : Tendsto (fun k => t k/(rates k : ℝ)^(1/6 : ℝ)) atTop (𝓝 0))
    (htnonneg : ∀ᶠ k in atTop,0≤t k) :
    Tendsto (fun k => (poissonMeasure (rates k)).real
      (Ici ⌈(rates k : ℝ)+sqrt (rates k)*t k⌉₊)/normalTail (t k)) atTop (𝓝 1) := by
  have hb := (moderate_error_scale_tendsto_zero (fun k => (rates k : ℝ)) t hrate ht).const_mul moderateConstant
  simp only [mul_zero] at hb
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) _ hb
  filter_upwards [moderate_domain_eventually (fun k => (rates k : ℝ)) t hrate ht,htnonneg]
    with k hk htk
  exact poisson_moderate_relative_error (rates k) hk.1 (t k) htk hk.2

end
end PaperC.V282.PoissonQuantitativeModerateLimit
