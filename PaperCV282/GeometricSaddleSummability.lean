import PaperCV282.SaddleCutoffAdmissibility
import Mathlib.Analysis.PSeries

/-!
# Summability of the actual saddle remainders on geometric scales

Only a geometric lower growth bound is needed. The saddle is the implicit
root already constructed in the arithmetic development; no asymptotic scale
or summability premise is added.
-/
namespace PaperC.V282.GeometricSaddleSummability

open Filter Topology PrimeEulerSaddle SaddleBranch SaddleParameters SaddleScales SaddleAsymptotics SaddleCutoffAdmissibility

noncomputable section

/-- This lower growth condition includes every sequence comparable to q^k, q>1. -/
def GeometricLowerGrowth (sizes : ℕ → ℕ) : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∀ᶠ k : ℕ in atTop, (k : ℝ) ≤ A * Real.log (sizes k)

theorem log_sizes_tendsto_atTop {sizes : ℕ → ℕ} (h : GeometricLowerGrowth sizes) :
    Tendsto (fun k => Real.log (sizes k)) atTop atTop := by
  obtain ⟨A,hA,h⟩ := h
  apply tendsto_atTop_mono' atTop ?_
    (tendsto_natCast_atTop_atTop.atTop_div_const hA)
  filter_upwards [h] with k hk
  exact (div_le_iff₀ hA).mpr (by simpa only [mul_comm] using hk)

/-- Exponential saddle errors are eventually smaller than every fixed inverse power of the index. -/
theorem exp_neg_nu_le_index_rpow {sizes : ℕ → ℕ} (hg : GeometricLowerGrowth sizes)
    {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (p : ℝ) (hp : 0 ≤ p) :
    ∀ᶠ k in atTop, Real.exp (-c * saddleNu a (Real.log (sizes k))) ≤ (k : ℝ)^(-p) := by
  obtain ⟨A,hA,hgrowth⟩ := hg
  have hlog := log_sizes_tendsto_atTop ⟨A,hA,hgrowth⟩
  have hnu := (tendsto_saddleNu_atTop ha).comp hlog
  have hcost : Tendsto (fun k => p * ((|Real.log A|+Real.log (Real.log (sizes k))) /
      saddleNu a (Real.log (sizes k)))) atTop (𝓝 0) := by
    simpa only [add_div,add_zero,mul_zero,Function.comp_def] using
      (((tendsto_const_nhds (x := |Real.log A|)).div_atTop hnu).add
        ((tendsto_log_div_saddleNu ha).comp hlog)).const_mul p
  filter_upwards [hgrowth,hlog.eventually (eventually_gt_atTop (0 : ℝ)),
    hnu.eventually (eventually_gt_atTop (0 : ℝ)),
    hcost.eventually (gt_mem_nhds hc),eventually_ge_atTop (1 : ℕ)] with k hg hH hn hb hk
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0<k by omega)
  have hlg : Real.log (k : ℝ) ≤ |Real.log A|+Real.log (Real.log (sizes k)) := by
    have hh := Real.log_le_log hkpos hg
    rw [Real.log_mul (ne_of_gt hA) (ne_of_gt hH)] at hh
    linarith [le_abs_self (Real.log A)]
  have hb' : p*(|Real.log A|+Real.log (Real.log (sizes k))) ≤ c*saddleNu a (Real.log (sizes k)) := by
    apply (div_le_iff₀ hn).mp
    simpa only [mul_div_assoc,Function.comp_def] using hb.le
  rw [Real.rpow_def_of_pos hkpos]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hlg hp]

theorem summable_exp_neg_nu {sizes : ℕ → ℕ} (hg : GeometricLowerGrowth sizes)
    {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    Summable (fun k => Real.exp (-c*saddleNu a (Real.log (sizes k)))) := by
  apply (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).of_norm_bounded_eventually_nat
  filter_upwards [exp_neg_nu_le_index_rpow hg ha hc 2 (by norm_num)] with k hk
  simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hk

/-- The saddle error scale is negligible against log N. -/
theorem nu_div_log_sizes_tendsto_zero {sizes : ℕ → ℕ} (hg : GeometricLowerGrowth sizes)
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun k => saddleNu a (Real.log (sizes k))/Real.log (sizes k)) atTop (𝓝 0) := by
  have hlog := log_sizes_tendsto_atTop hg
  apply ((tendsto_saddleCutoff_atTop ha).comp hlog).inv_tendsto_atTop.congr'
  filter_upwards [hlog.eventually (eventually_gt_atTop (0 : ℝ))] with k hk
  change (saddleCutoff a (Real.log (sizes k)))⁻¹ =
    saddleNu a (Real.log (sizes k))/Real.log (sizes k)
  unfold saddleNu
  field_simp

/-- Any fixed negative height power is summable on the same scales. -/
theorem summable_size_rpow_neg {sizes : ℕ → ℕ} (hg : GeometricLowerGrowth sizes)
    {c : ℝ} (hc : 0 < c) : Summable (fun k => (sizes k : ℝ)^(-c)) := by
  obtain ⟨A,hA,hgrowth⟩ := hg
  have hlog := log_sizes_tendsto_atTop ⟨A,hA,hgrowth⟩
  have hh : Tendsto (fun k : ℕ => 2*Real.log k/(k : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_div_assoc,mul_zero,Function.comp_def,id_eq] using
      (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop).const_mul 2
  apply (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ)< -1)).of_norm_bounded_eventually_nat
  filter_upwards [hgrowth,hh.eventually (gt_mem_nhds (div_pos hc hA)),
    hlog.eventually (eventually_gt_atTop (0 : ℝ)),eventually_ge_atTop (1 : ℕ)] with k hg hb hH hk
  have hkpos : (0 : ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hN : (0 : ℝ)<sizes k := by
    have : (sizes k : ℝ)≠0 := by intro hz; simp [hz] at hH
    exact lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm this)
  have hb' : 2*Real.log k ≤ (c/A)*(k : ℝ) := (div_le_iff₀ hkpos).mp hb.le
  have hgg : (c/A)*(k : ℝ) ≤ c*Real.log (sizes k) := by
    have := mul_le_mul_of_nonneg_left hg (div_pos hc hA).le
    calc
      (c/A)*(k : ℝ) ≤ (c/A)*(A*Real.log (sizes k)) := this
      _ = c*Real.log (sizes k) := by field_simp
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _),
    Real.rpow_def_of_pos hN,Real.rpow_def_of_pos hkpos]
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- The polynomial arithmetic remainder remains summable after the Markov amplification. -/
theorem summable_exp_nu_mul_size_rpow {sizes : ℕ → ℕ} (hg : GeometricLowerGrowth sizes)
    {a delta : ℝ} (ha : 0<a) (hdelta : 0<delta) (beta : ℝ) :
    Summable (fun k => Real.exp (beta*saddleNu a (Real.log (sizes k)))*(sizes k : ℝ)^(-delta)) := by
  have hlog := log_sizes_tendsto_atTop hg
  have hb : Tendsto (fun k => beta*(saddleNu a (Real.log (sizes k))/Real.log (sizes k)))
      atTop (𝓝 0) := by simpa using (nu_div_log_sizes_tendsto_zero hg ha).const_mul beta
  apply (summable_size_rpow_neg hg (by linarith : 0<delta/2)).of_norm_bounded_eventually_nat
  filter_upwards [hb.eventually (gt_mem_nhds (by linarith : 0<delta/2)),
    hlog.eventually (eventually_gt_atTop (0 : ℝ))] with k hb hH
  have hN : (0 : ℝ)<sizes k := by
    have : (sizes k : ℝ)≠0 := by intro hz; simp [hz] at hH
    exact lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm this)
  have hb' : beta*saddleNu a (Real.log (sizes k)) ≤ (delta/2)*Real.log (sizes k) := by
    apply (div_le_iff₀ hH).mp
    simpa only [mul_div_assoc,Function.comp_def] using hb.le
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),Real.rpow_def_of_pos hN,
    Real.rpow_def_of_pos hN,← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith)

end
end PaperC.V282.GeometricSaddleSummability
