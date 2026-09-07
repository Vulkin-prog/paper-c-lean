import PaperCV282.PrimeEulerFreeScales

/-! # The literal auxiliary scale equivalences in companion B.1 -/
namespace PaperC.V282.FreeCutoffClosureScales

open Filter Topology Real PrimeEulerFreeScales SaddleBranch SaddleBranchAsymptotics

noncomputable section

/-- Logarithm of either fixed multiple of the source square-root scale. -/
theorem log_sqrt_scale {H c : ℝ} (hH : 1<H) (hc : 0<c) :
    log (c*sqrt (H*log H))=log c+(log H+log (log H))/2 := by
  have hh : 0<H := by linarith
  have hl := log_pos hH
  rw [log_mul hc.ne' (by positivity),log_sqrt (by positivity),
    log_mul (by positivity) (log_pos hH).ne']

/-- Uniform in an arbitrary moving cutoff in a fixed positive multiplicative band. -/
theorem log_cutoff_div_log_tendsto {α : Type*} {l : Filter α} (H w : α→ℝ)
    (c C : ℝ) (hc : 0<c) (hC : 0<C) (hH : Tendsto H l atTop)
    (hband : ∀ᶠ k in l,c*sqrt (H k*log (H k))≤w k ∧ w k≤C*sqrt (H k*log (H k))) :
    Tendsto (fun k => log (w k)/log (H k)) l (𝓝 (1/2)) := by
  have hlog := tendsto_log_atTop.comp hH
  have hll : Tendsto (fun k => log (log (H k))/log (H k)) l (𝓝 0) :=
    (isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp hlog
  have hscale (a : ℝ) (ha : 0<a) :
      Tendsto (fun k => log (a*sqrt (H k*log (H k)))/log (H k)) l (𝓝 (1/2)) := by
    have he := ((tendsto_const_nhds (x := log a)).div_atTop hlog).add
      (((tendsto_const_nhds (x := (1 : ℝ))).add hll).div_const 2)
    norm_num at he
    apply he.congr'
    filter_upwards [hH.eventually (eventually_gt_atTop (1 : ℝ))] with k hk
    rw [log_sqrt_scale hk ha]
    field_simp [(log_pos hk).ne']
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (hscale c hc) (hscale C hC)
  · filter_upwards [hband,hH.eventually (eventually_gt_atTop (1 : ℝ))] with k hb hk
    have hh : 0<H k := by linarith
    have hl := log_pos hk
    exact div_le_div_of_nonneg_right (log_le_log (by positivity) hb.1) (log_pos hk).le
  · filter_upwards [hband,hH.eventually (eventually_gt_atTop (1 : ℝ))] with k hb hk
    have hh : 0<H k := by linarith
    have hl := log_pos hk
    have hw : 0<w k := lt_of_lt_of_le (by positivity : 0<c*sqrt (H k*log (H k))) hb.1
    exact div_le_div_of_nonneg_right (log_le_log hw hb.2) (log_pos hk).le

/-- The free upper-branch parameter has the exact one-half logarithmic equivalent. -/
theorem parameter_div_log_tendsto {α : Type*} {l : Filter α} (H w : α→ℝ)
    (c C : ℝ) (hc : 0<c) (hC : 0<C) (hH : Tendsto H l atTop)
    (hband : ∀ᶠ k in l,c*sqrt (H k*log (H k))≤w k ∧ w k≤C*sqrt (H k*log (H k))) :
    Tendsto (fun k => upperSaddleBranch (H k/w k)/log (H k)) l (𝓝 (1/2)) := by
  obtain ⟨H0,h0⟩ := sqrt_log_band_eventually_in_power_band c C hc hC
  have hp : ∀ᶠ k in l,(H k)^(1/4 : ℝ)≤w k ∧ w k≤(H k)^(3/4 : ℝ) := by
    filter_upwards [hband,hH.eventually (eventually_ge_atTop H0)] with k hb hk
    exact h0 (H k) hk (w k) hb.1 hb.2
  obtain ⟨hw,hn,_,_,_⟩ := power_band_scale_conditions hH hp
  have hl : Tendsto (fun k => log (H k/w k)/log (H k)) l (𝓝 (1/2)) := by
    have he := (tendsto_const_nhds (x := (1 : ℝ))).sub (log_cutoff_div_log_tendsto H w c C hc hC hH hband)
    have he' : Tendsto (fun k => (1 : ℝ)-log (w k)/log (H k)) l (𝓝 (1/2)) := by
      convert he using 1; norm_num
    apply he'.congr'
    filter_upwards [hH.eventually (eventually_gt_atTop (1 : ℝ)),
      hw.eventually (eventually_gt_atTop (0 : ℝ))] with k hk hkw
    rw [log_div (by positivity) hkw.ne',sub_div,div_self (log_pos hk).ne']
  have he := (tendsto_upperSaddleBranch_div_log.comp hn).mul hl
  norm_num at he
  apply he.congr'
  filter_upwards [hn.eventually (eventually_gt_atTop (1 : ℝ))] with k hk
  field_simp [(log_pos hk).ne']

/-- The logarithmic overhead is negligible uniformly throughout the same free band. -/
theorem log_div_nu_tendsto_zero {α : Type*} {l : Filter α} (H w : α→ℝ)
    (c C : ℝ) (hc : 0<c) (hC : 0<C) (hH : Tendsto H l atTop)
    (hband : ∀ᶠ k in l,c*sqrt (H k*log (H k))≤w k ∧ w k≤C*sqrt (H k*log (H k))) :
    Tendsto (fun k => log (H k)/(H k/w k)) l (𝓝 0) := by
  obtain ⟨H0,h0⟩ := sqrt_log_band_eventually_in_power_band c C hc hC
  have hlim := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ)<1/4)).tendsto_div_nhds_zero.comp hH
  apply squeeze_zero' _ _ hlim
  · filter_upwards [hband,hH.eventually (eventually_gt_atTop (1 : ℝ))] with k hb hk
    have hh : 0<H k := by linarith
    have hl := log_pos hk
    have hw : 0<w k := lt_of_lt_of_le (by positivity : 0<c*sqrt (H k*log (H k))) hb.1
    exact div_nonneg (log_pos hk).le (by positivity)
  · filter_upwards [hband,hH.eventually (eventually_ge_atTop H0),
      hH.eventually (eventually_ge_atTop (1 : ℝ))] with k hb hk h1
    obtain ⟨hp,hq⟩ := h0 (H k) hk (w k) hb.1 hb.2
    have hs := power_band_bounds h1 hp hq
    exact div_le_div_of_nonneg_left (log_nonneg h1) (by positivity) hs.2.2.2.1

end
end PaperC.V282.FreeCutoffClosureScales
