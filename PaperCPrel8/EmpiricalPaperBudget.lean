import PaperCPrel8.EmpiricalPaperScales

/-! # Admissibility and summable overlap ratios at the literal empirical scales

The strict alpha<1 margin supplies every fixed microscopic information
budget. The strict alpha>0 margin makes the actual window/origin ratio
summable. No final probability estimate is assumed in these scale lemmas.
-/
namespace PaperC.Prel8.EmpiricalPaperBudget
open Filter Topology
open PaperC.Prel8.EmpiricalPaperScales PaperC.Prel8.MicroscopicPaperBudget
open PaperC.Prel8.EmpiricalScaleBounds PaperC.Prel8.MicroscopicDiscardRates
open PaperC.V282.SaddleParameters PaperC.V282.SaddleScales
open PaperC.V282.SaddlePoissonScales PaperC.V282.GeometricSaddleSummability
open PaperC.V282.AllStartSoftPoisson
noncomputable section

/-- The actual intensity is between exp(alpha*V)/4 and exp(alpha*V). -/
theorem intensity_bounds (alpha : ℝ) (ha : 0 ≤ alpha) :
    ∀ᶠ k in atTop,
      Real.exp (alpha*cutoff k)/4 ≤ siteRate (size k) (length alpha k) ∧
      siteRate (size k) (length alpha k) ≤ Real.exp (alpha*cutoff k) := by
  filter_upwards [length_band alpha ha,length_quarter alpha ha,
    cutoff_tendsto.eventually (eventually_ge_atTop (0:ℝ))] with k hb hq hV
  have hr := rounded_intensity_bounds alpha (mul_nonneg ha hV)
  have hc := siteRate_comparison (size k) (length alpha k) (by omega)
  rw [fullRate_coe,dyadic_rate_identity alpha hb.1] at hc
  constructor <;> linarith [hc.1,hc.2,hr.1,hr.2]

/-- The actual number of expected starts diverges at every positive alpha. -/
theorem intensity_tendsto (alpha : ℝ) (ha : 0 < alpha) :
    Tendsto (fun k => siteRate (size k) (length alpha k)) atTop atTop :=
  tendsto_atTop_mono' atTop ((intensity_bounds alpha ha.le).mono (fun _ h => h.1))
    ((Real.tendsto_exp_atTop.comp (cutoff_tendsto.const_mul_atTop ha)).atTop_div_const (by norm_num))

/-- Every fixed microscopic margin is available when alpha<1. -/
theorem information_budget (alpha c : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∀ᶠ k in atTop,
      Real.log (siteRate (size k) (length alpha k)) ≤
        cutoff k-c*saddleNu 1 (Real.log (size k)) := by
  have hc : Tendsto (fun k => c*(saddleNu 1 (Real.log (size k))/cutoff k))
      atTop (𝓝 0) := by
    simpa [cutoff,size] using ((tendsto_nu_div_saddleCutoff (by norm_num : (0:ℝ)<1)).comp
      (log_sizes_tendsto_atTop dyadic_geometric_growth)).const_mul c
  filter_upwards [intensity_bounds alpha ha.le,
    cutoff_tendsto.eventually (eventually_gt_atTop (0:ℝ)),
    (intensity_tendsto alpha ha).eventually (eventually_gt_atTop (0:ℝ)),
    hc.eventually (gt_mem_nhds (by linarith : (0:ℝ)<1-alpha))] with k hb hV hr hc
  have hl := Real.log_le_log hr hb.2
  rw [Real.log_exp] at hl
  have hh : c*saddleNu 1 (Real.log (size k)) ≤ (1-alpha)*cutoff k := by
    apply (div_le_iff₀ hV).mp
    simpa only [mul_div_assoc] using hc.le
  linarith

/-- A positive fraction of the actual hard saddle gives a summable exponential. -/
theorem summable_cutoff_exponential (alpha : ℝ) (ha : 0 < alpha) :
    Summable (fun k => Real.exp (-alpha*cutoff k)) := by
  obtain ⟨Mzero,hM⟩ := nu_le_saddle_eventually
  apply (summable_exp_neg_nu dyadic_geometric_growth (by norm_num : (0:ℝ)<1) ha).of_norm_bounded_eventually_nat
  filter_upwards [size_tendsto.eventually (eventually_ge_atTop Mzero)] with k hk
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hb := (hM (size k) hk).2
  change saddleNu 1 (Real.log (size k)) ≤ cutoff k at hb
  change -alpha*cutoff k ≤ -alpha*saddleNu 1 (Real.log (size k))
  nlinarith

/-- The actual h/n ratio has an explicit summable bound, including window rounding. -/
theorem window_sites_ratio_bound (alpha tau : ℝ) (ha : 0 < alpha) (ht : 0 ≤ tau) :
    ∀ᶠ k in atTop, 0 < sites alpha k ∧
      (windowSize alpha tau k:ℝ)/(sites alpha k) ≤ 4*tau*Real.exp (-alpha*cutoff k) := by
  filter_upwards [intensity_bounds alpha ha.le,
    (intensity_tendsto alpha ha).eventually (eventually_gt_atTop (0:ℝ))] with k hb hr
  have hn : (0:ℝ) < sites alpha k := by
    change 0 < (sites alpha k:ℝ)/(2:ℝ)^(length alpha k) at hr
    exact (div_pos_iff_of_pos_right (by positivity : (0:ℝ)<2^(length alpha k))).mp hr
  have hf := Nat.floor_le (mul_nonneg ht (by positivity : (0:ℝ)≤2^(length alpha k)))
  change (windowSize alpha tau k:ℝ) ≤ tau*(2:ℝ)^(length alpha k) at hf
  refine ⟨Nat.cast_pos.mp hn,?_⟩
  calc
    _ ≤ (tau*(2:ℝ)^(length alpha k))/(sites alpha k) := div_le_div_of_nonneg_right hf hn.le
    _ = tau / siteRate (size k) (length alpha k) := by unfold siteRate sites; field_simp
    _ ≤ tau/(Real.exp (alpha*cutoff k)/4) :=
      div_le_div_of_nonneg_left ht (by positivity) hb.1
    _ = _ := by rw [neg_mul,Real.exp_neg]; ring

/-- The actual h/n ratio is summable. -/
theorem summable_window_sites_ratio (alpha tau : ℝ) (ha : 0 < alpha) (ht : 0 ≤ tau) :
    Summable (fun k => (windowSize alpha tau k:ℝ)/(sites alpha k)) := by
  apply ((summable_cutoff_exponential alpha ha).mul_left (4*tau)).of_norm_bounded_eventually_nat
  filter_upwards [window_sites_ratio_bound alpha tau ha ht] with k hk
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  exact hk.2

/-- Eventually the actual window is positive and fits in half of the available sites. -/
theorem window_fits (alpha tau : ℝ) (ha : 0 < alpha) (ht : 0 < tau) :
    ∀ᶠ k in atTop, 0 < windowSize alpha tau k ∧
      2*windowSize alpha tau k ≤ sites alpha k := by
  have hr := (summable_window_sites_ratio alpha tau ha ht.le).tendsto_atTop_zero
  have hp : Tendsto (fun k => tau*(2:ℝ)^(length alpha k)) atTop atTop :=
    ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).comp
      (length_tendsto alpha ha.le)).const_mul_atTop ht
  filter_upwards [window_sites_ratio_bound alpha tau ha ht.le,
    hr.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)),
    hp.eventually (eventually_ge_atTop (1:ℝ))] with k hb hr hp
  have hh : 1 ≤ windowSize alpha tau k := by
    exact Nat.le_floor (by exact_mod_cast hp)
  have hn : (0:ℝ)<sites alpha k := Nat.cast_pos.mpr hb.1
  have hs : 2*(windowSize alpha tau k:ℝ) ≤ sites alpha k := by
    have := (div_lt_iff₀ hn).mp hr
    linarith
  exact ⟨by omega,by exact_mod_cast hs⟩

/-- The number of origins dominates half the available sites once windows fit. -/
theorem origins_comparison (alpha tau : ℝ) {k : ℕ}
    (hfit : 2*windowSize alpha tau k ≤ sites alpha k) :
    sites alpha k ≤ 2*origins alpha tau k ∧
      origins alpha tau k+windowSize alpha tau k = sites alpha k+1 := by
  unfold origins
  omega

/-- The true h/N ratio, needed by Chebyshev, is summable. -/
theorem summable_window_origins_ratio (alpha tau : ℝ) (ha : 0 < alpha) (ht : 0 < tau) :
    Summable (fun k => (windowSize alpha tau k:ℝ)/(origins alpha tau k)) := by
  apply ((summable_window_sites_ratio alpha tau ha ht.le).mul_left 2).of_norm_bounded_eventually_nat
  filter_upwards [window_fits alpha tau ha ht,
    window_sites_ratio_bound alpha tau ha ht.le] with k hf hs
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hn : (0:ℝ)<sites alpha k := Nat.cast_pos.mpr hs.1
  have hN : (0:ℝ)<origins alpha tau k := Nat.cast_pos.mpr (origins_pos _ _ _)
  have hcomp : (sites alpha k:ℝ) ≤ 2*(origins alpha tau k:ℝ) := by
    exact_mod_cast (origins_comparison alpha tau hf.2).1
  apply (div_le_iff₀ hN).mpr
  have hh := mul_le_mul_of_nonneg_left hcomp
    (div_nonneg (Nat.cast_nonneg (windowSize alpha tau k)) hn.le)
  have he : (windowSize alpha tau k:ℝ)/(sites alpha k)*(sites alpha k) = windowSize alpha tau k :=
    div_mul_cancel₀ _ hn.ne'
  rw [he] at hh
  nlinarith

end
end PaperC.Prel8.EmpiricalPaperBudget
