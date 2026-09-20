import PaperCPrel8.EmpiricalPaperBudget

/-! # The additional window-size assertions in corollary 7.8a

Explicit constants replace the O(1) in h=M*exp(-alpha*V+O(1));
log(h)/log(M) tends to one. These do not replace the exact mean normalization.
-/
namespace PaperC.Prel8.EmpiricalWindowGrowth
open Filter Topology
open PaperC.Prel8.EmpiricalPaperScales PaperC.Prel8.EmpiricalPaperBudget
open PaperC.V282.SaddleCutoffAdmissibility PaperC.V282.GeometricSaddleSummability
open PaperC.Prel8.EmpiricalScaleBounds
noncomputable section

/-- Explicit positive constants in h=M*exp(-alpha*V+O(1)). -/
theorem window_size_bounds (alpha tau : ℝ) (ha : 0 < alpha) (ht : 0 < tau) :
    ∀ᶠ k in atTop,
      (tau/2)*(size k:ℝ)*Real.exp (-alpha*cutoff k) ≤ windowSize alpha tau k ∧
      (windowSize alpha tau k:ℝ) ≤ 2*tau*(size k:ℝ)*Real.exp (-alpha*cutoff k) := by
  have hp : Tendsto (fun k => tau*(2:ℝ)^(length alpha k)) atTop atTop :=
    ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).comp
      (length_tendsto alpha ha.le)).const_mul_atTop ht
  filter_upwards [length_band alpha ha.le,cutoff_tendsto.eventually (eventually_ge_atTop (0:ℝ)),
    hp.eventually (eventually_ge_atTop (2:ℝ))] with k hd hV hp
  have hr := rounded_intensity_bounds alpha (mul_nonneg ha.le hV)
  rw [← dyadic_rate_identity alpha hd.1] at hr
  have he : Real.exp (-alpha*cutoff k) = (Real.exp (alpha*cutoff k))⁻¹ := by
    rw [neg_mul,Real.exp_neg]
  have hb : (size k:ℝ)*Real.exp (-alpha*cutoff k) ≤ (2:ℝ)^(length alpha k) ∧
      (2:ℝ)^(length alpha k) ≤ 2*(size k:ℝ)*Real.exp (-alpha*cutoff k) := by
    have hpow : (0:ℝ)<(2:ℝ)^(length alpha k) := by positivity
    have hE : 0 < Real.exp (alpha*cutoff k) := Real.exp_pos _
    have hlo := (div_le_iff₀ hpow).mp hr.2
    have hhi := (le_div_iff₀ hpow).mp hr.1
    rw [he]
    constructor
    · rw [← div_eq_mul_inv]
      exact (div_le_iff₀ hE).mpr (by nlinarith)
    · rw [← div_eq_mul_inv]
      exact (le_div_iff₀ hE).mpr (by nlinarith)
  have hf := Nat.floor_le (by positivity : 0 ≤ tau*(2:ℝ)^(length alpha k))
  have hf' := Nat.lt_floor_add_one (tau*(2:ℝ)^(length alpha k))
  change (windowSize alpha tau k:ℝ) ≤ tau*(2:ℝ)^(length alpha k) at hf
  change tau*(2:ℝ)^(length alpha k) < (windowSize alpha tau k:ℝ)+1 at hf'
  constructor <;> nlinarith [hb.1,hb.2]

/-- Logarithmic formulation of the displayed M^(1-o(1)) window scale. -/
theorem window_log_ratio_tendsto (alpha tau : ℝ) (ha : 0 < alpha) (ht : 0 < tau) :
    Tendsto (fun k => Real.log (windowSize alpha tau k)/(Real.log (size k))) atTop (𝓝 1) := by
  have hlog := log_sizes_tendsto_atTop dyadic_geometric_growth
  have hv : Tendsto (fun k => cutoff k/Real.log (size k)) atTop (𝓝 0) :=
    (tendsto_saddleCutoff_div_height (by norm_num : (0:ℝ)<1)).comp hlog
  have hlim (C : ℝ) : Tendsto
      (fun k => 1+Real.log C/Real.log (size k)-alpha*(cutoff k/Real.log (size k))) atTop (𝓝 1) := by
    have hc : Tendsto (fun k => Real.log C/Real.log (size k)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hlog
    simpa using ((tendsto_const_nhds (x := (1:ℝ))).add hc).sub (hv.const_mul alpha)
  have he (C : ℝ) (hC : 0 < C) {k : ℕ} (hk : 0 < Real.log (size k)) :
      Real.log (C*(size k:ℝ)*Real.exp (-alpha*cutoff k))/Real.log (size k) =
        1+Real.log C/Real.log (size k)-alpha*(cutoff k/Real.log (size k)) := by
    have hm : (0:ℝ)<size k := by unfold size; positivity
    rw [Real.log_mul (mul_pos hC hm).ne' (Real.exp_ne_zero _),
      Real.log_mul hC.ne' hm.ne', Real.log_exp]
    field_simp
    ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlim (tau/2)) (hlim (2*tau))
  · filter_upwards [window_size_bounds alpha tau ha ht,
      hlog.eventually (eventually_gt_atTop (0:ℝ))] with k hb hk
    change 0 < Real.log (size k) at hk
    rw [← he (tau/2) (by positivity) hk]
    apply div_le_div_of_nonneg_right _ hk.le
    have hm : (0:ℝ)<size k := by unfold size; positivity
    exact Real.log_le_log (by positivity) hb.1
  · filter_upwards [window_size_bounds alpha tau ha ht,
      hlog.eventually (eventually_gt_atTop (0:ℝ))] with k hb hk
    change 0 < Real.log (size k) at hk
    rw [← he (2*tau) (by positivity) hk]
    apply div_le_div_of_nonneg_right _ hk.le
    have hm : (0:ℝ)<size k := by unfold size; positivity
    have hw : (0:ℝ)<windowSize alpha tau k := lt_of_lt_of_le (by positivity) hb.1
    exact Real.log_le_log hw hb.2

end
end PaperC.Prel8.EmpiricalWindowGrowth
