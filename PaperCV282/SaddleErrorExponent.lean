import PaperCV282.SaddleMarkTruncation

/-!
# The leading 1/sqrt(2) exponent on the critical square-root scale

Fixed multiplicative constants, the smaller saddle remainder and any
negative power of N are absorbed uniformly before the window length.
-/
namespace PaperC.V282.SaddleErrorExponent

open Filter Topology SaddleParameters SaddleScales SaddlePoissonScales
open SaddleCutoffAdmissibility

noncomputable section

def criticalScale (N : ℕ) : ℝ := Real.sqrt (Real.log N * Real.log (Real.log N))

theorem criticalScale_tendsto_atTop : Tendsto criticalScale atTop atTop := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact Real.tendsto_sqrt_atTop.comp (hlog.atTop_mul_atTop₀ (Real.tendsto_log_atTop.comp hlog))

theorem cutoff_div_criticalScale_tendsto :
    Tendsto (fun N : ℕ => saddleCutoff 1 (Real.log N)/criticalScale N)
      atTop (𝓝 (Real.sqrt (1/2))) :=
  (tendsto_saddleCutoff_normalized (a := 1) (by norm_num)).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

theorem nu_div_criticalScale_tendsto_zero :
    Tendsto (fun N : ℕ => saddleNu 1 (Real.log N)/criticalScale N) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h := ((tendsto_nu_div_saddleCutoff (a := 1) (by norm_num)).comp hlog).mul
    cutoff_div_criticalScale_tendsto
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [hlog.eventually (eventually_ge_atTop (saddleThreshold 1))] with N hN
  have hv := (saddleCutoff_pos (a := 1) (by norm_num) hN).ne'
  dsimp only [Function.comp_apply]
  field_simp

/-- The paper's coefficient is exactly the normalized positive hard saddle. -/
theorem critical_coefficient_eq : Real.sqrt (1/2 : ℝ) = 1/Real.sqrt 2 := by
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1),Real.sqrt_one]

/-- A power-saving term is eventually smaller than the hard exponential remainder. -/
theorem polynomial_le_saddle_eventually (delta eta : ℝ) (hdelta : 0 < delta) (heta : 0 ≤ eta) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ)^(-delta) ≤
      Real.exp (-saddleCutoff 1 (Real.log N)+eta*saddleNu 1 (Real.log N)) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio := ((tendsto_saddleCutoff_div_height (a := 1) (by norm_num)).comp hlog).eventually
    (gt_mem_nhds hdelta)
  filter_upwards [hratio,hlog.eventually (eventually_gt_atTop (0 : ℝ)),
    hlog.eventually (eventually_ge_atTop (saddleThreshold 1)),eventually_ge_atTop (1 : ℕ)]
    with N hratio hn hth hN
  have hv := saddleCutoff_pos (a := 1) (by norm_num) hth
  have hnu : 0 ≤ saddleNu 1 (Real.log N) := by unfold saddleNu; positivity
  have hcost := (div_lt_iff₀ hn).mp hratio
  have hNp : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  rw [Real.rpow_def_of_pos hNp]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg heta hnu]

/-- Every coefficient below 1/sqrt(2) bounds the complete numerical error eventually. -/
theorem complete_error_le_exponential_eventually (K delta eta a : ℝ)
    (hK : 0 < K) (hdelta : 0 < delta) (heta : 0 ≤ eta) (ha : a < 1/Real.sqrt 2) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero,
      K*(Real.exp (-saddleCutoff 1 (Real.log N)+eta*saddleNu 1 (Real.log N))+
        (N : ℝ)^(-delta)) ≤ Real.exp (-a*criticalScale N) := by
  have hcoef : Tendsto (fun N : ℕ => Real.log (2*K)/criticalScale N -
      saddleCutoff 1 (Real.log N)/criticalScale N +
      eta*(saddleNu 1 (Real.log N)/criticalScale N)) atTop (𝓝 (-(1/Real.sqrt 2))) := by
    have hh := ((tendsto_const_nhds (x := Real.log (2*K))).div_atTop criticalScale_tendsto_atTop).sub
      cutoff_div_criticalScale_tendsto |>.add (nu_div_criticalScale_tendsto_zero.const_mul eta)
    simpa only [zero_sub,mul_zero,add_zero,critical_coefficient_eq] using hh
  have hc := hcoef.eventually (gt_mem_nhds (show -(1/Real.sqrt 2)< -a by linarith))
  apply eventually_atTop.1
  filter_upwards [hc,criticalScale_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    polynomial_le_saddle_eventually delta eta hdelta heta] with N hc hs hp
  have hcost : Real.log (2*K)-saddleCutoff 1 (Real.log N)+eta*saddleNu 1 (Real.log N) ≤
      -a*criticalScale N := by
    have hr : Real.log (2*K)/criticalScale N-saddleCutoff 1 (Real.log N)/criticalScale N+
        eta*(saddleNu 1 (Real.log N)/criticalScale N) =
        (Real.log (2*K)-saddleCutoff 1 (Real.log N)+eta*saddleNu 1 (Real.log N))/criticalScale N := by ring
    rw [hr] at hc
    exact ((div_lt_iff₀ hs).mp hc).le
  calc
    _ ≤ (2*K)*Real.exp (-saddleCutoff 1 (Real.log N)+eta*saddleNu 1 (Real.log N)) := by nlinarith
    _ = Real.exp (Real.log (2*K)-saddleCutoff 1 (Real.log N)+eta*saddleNu 1 (Real.log N)) := by
      rw [show Real.log (2*K)-saddleCutoff 1 (Real.log N)+eta*saddleNu 1 (Real.log N) =
        Real.log (2*K)+(-saddleCutoff 1 (Real.log N)+eta*saddleNu 1 (Real.log N)) by ring]
      conv_rhs => rw [Real.exp_add,Real.exp_log (by positivity)]
    _ ≤ _ := Real.exp_le_exp.mpr hcost

end
end PaperC.V282.SaddleErrorExponent
