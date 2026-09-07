import PaperCV282.DyadicPrefixProbability

/-! # Summability of the quantitative finite-prefix error scales -/
namespace PaperC.V282.DyadicPrefixRemainders

open Filter Topology DyadicPrefixThresholds

noncomputable section

/-- Any exponential scale dominating log k absorbs every fixed polynomial prefactor. -/
theorem summable_polynomial_exponential (g : ℕ → ℝ)
    (hg : ∀ᶠ k in atTop, 0<g k)
    (hlog : Tendsto (fun k : ℕ => Real.log k/g k) atTop (𝓝 0))
    (c : ℝ) (hc : 0<c) (p : ℕ) :
    Summable (fun k : ℕ => (k : ℝ)^p*Real.exp (-c*g k)) := by
  have hp : (0 : ℝ)<(p : ℝ)+2 := by positivity
  apply (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ)< -1)).of_norm_bounded_eventually_nat
  filter_upwards [hg,hlog.eventually (eventually_lt_nhds (div_pos hc hp)),
    eventually_ge_atTop (1 : ℕ)] with k hg hk hk1
  have hk0 : (0 : ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hh : ((p : ℝ)+2)*Real.log k ≤ c*g k := by
    have h1 := (div_lt_iff₀ hg).mp hk
    have h2 := mul_le_mul_of_nonneg_left h1.le hp.le
    have he : ((p : ℝ)+2)*(c/((p : ℝ)+2)*g k) = c*g k := by field_simp
    linarith
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),← Real.rpow_natCast,
    Real.rpow_def_of_pos hk0,Real.rpow_def_of_pos hk0,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem log_squared_div_nat_tendsto_zero :
    Tendsto (fun k : ℕ => (Real.log k)^2/(k : ℝ)) atTop (𝓝 0) := by
  simpa only [one_mul,add_zero,Function.comp_def] using
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp
      tendsto_natCast_atTop_atTop

theorem log_div_sqrt_index_log_tendsto_zero :
    Tendsto (fun k : ℕ => Real.log k/Real.sqrt ((k : ℝ)*Real.log k)) atTop (𝓝 0) := by
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp log_div_nat_tendsto_zero
  simp only [Real.sqrt_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with k hk
  have hk0 : (0 : ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hl : 0<Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast hk)
  simp only [Function.comp_def]
  rw [Real.sqrt_div hl.le,Real.sqrt_mul hk0.le]
  have hsk : Real.sqrt (k : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hk0).ne'
  have hsl : Real.sqrt (Real.log k) ≠ 0 := (Real.sqrt_pos.mpr hl).ne'
  field_simp
  rw [Real.sq_sqrt hl.le]

/-- In particular the saddle scale appearing in the dyadic proof has a summable polynomial envelope. -/
theorem summable_polynomial_saddle (c : ℝ) (hc : 0<c) (p : ℕ) :
    Summable (fun k : ℕ => (k : ℝ)^p*Real.exp (-c*Real.sqrt ((k : ℝ)*Real.log k))) := by
  apply summable_polynomial_exponential _ ?_ log_div_sqrt_index_log_tendsto_zero c hc p
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with k hk
  apply Real.sqrt_pos.mpr
  exact mul_pos (by exact_mod_cast (show 0<k by omega)) (Real.log_pos (by exact_mod_cast hk))

/-- The slower deep-start and microscopic-border scale is still summable. -/
theorem summable_polynomial_deep (c : ℝ) (hc : 0<c) (p : ℕ) :
    Summable (fun k : ℕ => (k : ℝ)^p*Real.exp (-c*((k : ℝ)/Real.log k))) := by
  apply summable_polynomial_exponential _ ?_ ?_ c hc p
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with k hk
    exact div_pos (by exact_mod_cast (show 0<k by omega)) (Real.log_pos (by exact_mod_cast hk))
  · convert log_squared_div_nat_tendsto_zero using 1
    ext k
    simp only [div_div_eq_mul_div]
    ring

/-- All fixed negative powers of the prefix size remain summable after polynomial factors in k. -/
theorem summable_polynomial_dyadic_power (delta : ℝ) (hdelta : 0<delta) (p : ℕ) :
    Summable (fun k : ℕ => (k : ℝ)^p*(2 : ℝ)^(-delta*(k : ℝ))) := by
  have hs := summable_polynomial_exponential (fun k => (k : ℝ))
    (by filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
        exact_mod_cast (show 0<k by omega))
    log_div_nat_tendsto_zero (delta*Real.log 2) (mul_pos hdelta (Real.log_pos (by norm_num))) p
  apply hs.congr
  intro k
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ)<2)]
  congr 2
  ring

/-- The common majorant for all errors of (7.10)--(7.11) on the two dyadic thresholds. -/
theorem summable_common_prefix_remainder (C c : ℝ) (hc : 0<c) :
    Summable (fun k : ℕ =>
      C*(k : ℝ)^2*Real.exp (-c*Real.sqrt ((k : ℝ)*Real.log k))+
      C*Real.exp (-c*((k : ℝ)/Real.log k))+
      C*(k : ℝ)^2*(2 : ℝ)^(-(k : ℝ)/4)) := by
  have h1 := (summable_polynomial_saddle c hc 2).mul_left C
  have h2 := (summable_polynomial_deep c hc 0).mul_left C
  have h3 := (summable_polynomial_dyadic_power (1/4) (by norm_num) 2).mul_left C
  apply ((h1.add h2).add h3).congr
  intro k
  have he : -(1/4 : ℝ)*(k : ℝ) = -(k : ℝ)/4 := by ring
  simp only [pow_zero,one_mul,he]
  ring

end
end PaperC.V282.DyadicPrefixRemainders
