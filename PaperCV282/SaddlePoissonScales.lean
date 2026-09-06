import PaperCV282.SaddleCutoffAdmissibility

/-!
# Vanishing arithmetic cutoff costs at genuine saddles

The scale nu is negligible relative to the saddle exponent. Thus every
fixed positive multiple of the negative saddle exponent dominates any
fixed eta*nu error. These facts use no prime-counting hypothesis.
-/

namespace PaperC.V282.SaddlePoissonScales

open Set Filter Topology SaddleParameters SaddleScales SaddleAsymptotics SaddleExpansion
open PrimeEulerSaddle SaddleCutoffAdmissibility

noncomputable section

/-- The saddle exponent dominates the smaller remainder scale nu. -/
theorem tendsto_saddleCutoff_div_nu {a : ℝ} (ha : 0 < a) :
    Tendsto (fun H => saddleCutoff a H / saddleNu a H) atTop atTop := by
  have hdiff : Tendsto (fun H => saddleParameter a H -
      normalizedExponentialIntegral (saddleParameter a H)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [(tendsto_saddleParameter_atTop ha).eventually (eventually_ge_atTop (b + 2)),
      (tendsto_normalizedExponentialIntegral.comp (tendsto_saddleParameter_atTop ha)).eventually
        (gt_mem_nhds (by norm_num : (1 : ℝ) < 2))] with H hu he
    dsimp only [Function.comp_def] at he
    linarith
  apply (hdiff.const_mul_atTop ha).congr'
  filter_upwards [eventually_ge_atTop (saddleThreshold a)] with H hH
  have hw := saddleCutoff_pos ha hH
  have hHpos := (saddleThreshold_pos ha).trans_le hH
  rw [← saddleCutoff_square_div_identity ha hH]
  unfold saddleNu
  field_simp [hw.ne', hHpos.ne']

theorem tendsto_nu_div_saddleCutoff {a : ℝ} (ha : 0 < a) :
    Tendsto (fun H => saddleNu a H / saddleCutoff a H) atTop (𝓝 0) := by
  apply (tendsto_saddleCutoff_div_nu ha).inv_tendsto_atTop.congr
  intro H
  change (saddleCutoff a H / saddleNu a H)⁻¹ = _
  rw [inv_div]

/-- A fixed positive saddle cost wins over any fixed multiple of nu. -/
theorem saddle_exponential_tendsto_zero (a c eta : ℝ) (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun H => Real.exp (-c * saddleCutoff a H + eta * saddleNu a H)) atTop (𝓝 0) := by
  have hcoef : Tendsto (fun H => -c + eta * (saddleNu a H / saddleCutoff a H)) atTop (𝓝 (-c)) := by
    simpa only [mul_zero, add_zero] using
      ((tendsto_nu_div_saddleCutoff ha).const_mul eta).const_add (-c)
  have hexponent := (tendsto_saddleCutoff_atTop ha).atTop_mul_neg (neg_neg_iff_pos.mpr hc) hcoef
  apply (Real.tendsto_exp_atBot.comp hexponent).congr'
  filter_upwards [eventually_ge_atTop (saddleThreshold a)] with H hH
  have hw := saddleCutoff_pos ha hH
  dsimp only [Function.comp_def]
  congr 1
  field_simp [hw.ne']

/-- Natural population scale H=log N, uniform before any window or mask is chosen. -/
theorem saddle_exponential_nat_tendsto_zero (a c eta : ℝ) (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun N : ℕ => Real.exp (-c * saddleCutoff a (Real.log N) + eta * saddleNu a (Real.log N)))
      atTop (𝓝 0) :=
    (saddle_exponential_tendsto_zero a c eta ha hc).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- Explicit smallness threshold, used in particular for a removed fraction at most one half. -/
theorem saddle_exponential_le_eventually (a c eta delta : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hdelta : 0 < delta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero,
      Real.exp (-c * saddleCutoff a (Real.log N) + eta * saddleNu a (Real.log N)) ≤ delta := by
  exact eventually_atTop.1 ((saddle_exponential_nat_tendsto_zero a c eta ha hc).eventually
    (gt_mem_nhds hdelta) |>.mono fun _ h => h.le)

end
end PaperC.V282.SaddlePoissonScales
