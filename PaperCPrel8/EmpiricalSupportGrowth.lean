import PaperCPrel8.EmpiricalSupportScales

/-! # The displayed N*p^2 = M^(-1+o(1)) in remark 7.8b

The logarithmic exponent is proved at the literal integer scales, including
all floor operations and the number of fully contained origins.
-/
namespace PaperC.Prel8.EmpiricalSupportGrowth
open Filter Topology
open PaperC.Prel8.EmpiricalPaperScales PaperC.Prel8.EmpiricalPaperBudget
open PaperC.Prel8.EmpiricalSupportScales PaperC.Prel8.EmpiricalScaleBounds
open PaperC.V282.GeometricSaddleSummability
noncomputable section

/-- Eventually the actual origin count is comparable to the dyadic height. -/
theorem origins_size_bounds (alpha tau : ℝ) (ha : 0 < alpha) (ht : 0 < tau) :
    ∀ᶠ k in atTop, (size k:ℝ)/4 ≤ origins alpha tau k ∧
      (origins alpha tau k:ℝ) ≤ 2*(size k:ℝ) := by
  filter_upwards [length_quarter alpha ha.le,window_fits alpha tau ha ht] with k hL hf
  have hn := (origins_comparison alpha tau hf.2).1
  have hlow : size k ≤ 4*origins alpha tau k := by unfold sites at hn; omega
  constructor
  · have h : (size k:ℝ) ≤ 4*(origins alpha tau k:ℝ) := by exact_mod_cast hlow
    linarith
  · exact_mod_cast origins_le_twice_size alpha tau k

/-- There are M^(1+o(1)) contained origins. -/
theorem origins_log_ratio_tendsto (alpha tau : ℝ) (ha : 0 < alpha) (ht : 0 < tau) :
    Tendsto (fun k => Real.log (origins alpha tau k)/Real.log (size k)) atTop (𝓝 1) := by
  have hlog := log_sizes_tendsto_atTop dyadic_geometric_growth
  have hlim (C : ℝ) : Tendsto (fun k => 1+Real.log C/Real.log (size k)) atTop (𝓝 1) := by
    have hc : Tendsto (fun k => Real.log C/Real.log (size k)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hlog
    simpa using hc.const_add 1
  have he (C : ℝ) (hC : 0 < C) {k : ℕ} (hk : 0 < Real.log (size k)) :
      Real.log (C*(size k:ℝ))/Real.log (size k) = 1+Real.log C/Real.log (size k) := by
    have hm : (0:ℝ)<size k := by unfold size; positivity
    rw [Real.log_mul hC.ne' hm.ne']
    field_simp
    ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlim (1/4)) (hlim 2)
  · filter_upwards [origins_size_bounds alpha tau ha ht,
      hlog.eventually (eventually_gt_atTop (0:ℝ))] with k hb hk
    change 0 < Real.log (size k) at hk
    rw [← he (1/4) (by norm_num) hk]
    apply div_le_div_of_nonneg_right _ hk.le
    have hm : (0:ℝ)<size k := by unfold size; positivity
    apply Real.log_le_log (by positivity)
    linarith [hb.1]
  · filter_upwards [origins_size_bounds alpha tau ha ht,
      hlog.eventually (eventually_gt_atTop (0:ℝ))] with k hb hk
    change 0 < Real.log (size k) at hk
    rw [← he 2 (by norm_num) hk]
    apply div_le_div_of_nonneg_right _ hk.le
    exact Real.log_le_log (by exact_mod_cast origins_pos alpha tau k) hb.2

/-- The exact base length has logarithmic exponent one. -/
theorem length_log_ratio_tendsto (alpha : ℝ) (ha : 0 ≤ alpha) :
    Tendsto (fun k => (length alpha k:ℝ)*Real.log 2/Real.log (size k)) atTop (𝓝 1) := by
  have hd : Tendsto (fun k => (depth alpha k:ℝ)/Real.log (size k)) atTop (𝓝 0) :=
    (rounded_depth_small alpha ha).comp size_tendsto
  have hh : Tendsto (fun k => 1-((depth alpha k:ℝ)/Real.log (size k))*Real.log 2)
      atTop (𝓝 1) := by simpa using (hd.mul_const (Real.log 2)).const_sub 1
  apply hh.congr'
  filter_upwards [length_band alpha ha,eventually_ge_atTop (1:ℕ)] with k hb hk
  have hsum : (length alpha k:ℝ)+(depth alpha k:ℝ)=k := by
    exact_mod_cast (Nat.sub_add_cancel hb.1 : length alpha k+depth alpha k=k)
  have hl : Real.log (size k) ≠ 0 := by rw [log_size]; positivity
  have he := log_size k
  field_simp
  nlinarith [congrArg (fun t : ℝ => t*Real.log 2) hsum]

/-- Precise logarithmic meaning of N_k*p_k^2 = M_k^(-1+o(1)). -/
theorem support_penalty_log_ratio_tendsto (alpha tau : ℝ) (ha : 0 < alpha) (ht : 0 < tau) :
    Tendsto (fun k => Real.log ((origins alpha tau k:ℝ)*((1:ℝ)/2^(length alpha k))^2)/
      Real.log (size k)) atTop (𝓝 (-1:ℝ)) := by
  have hn := origins_log_ratio_tendsto alpha tau ha ht
  have hl := length_log_ratio_tendsto alpha ha.le
  have hh := hn.sub (hl.const_mul 2)
  convert hh using 1
  · ext k
    have hn0 : (0:ℝ)<origins alpha tau k := by exact_mod_cast origins_pos alpha tau k
    rw [Real.log_mul hn0.ne' (by positivity),Real.log_pow,
      Real.log_div (by norm_num) (by positivity),Real.log_one,Real.log_pow]
    ring
  · norm_num

end
end PaperC.Prel8.EmpiricalSupportGrowth
