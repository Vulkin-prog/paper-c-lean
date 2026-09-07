import PaperCV282.PrefixEnvelopeSummability
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # The two literal dyadic thresholds of Corollary 7.5 -/
namespace PaperC.V282.DyadicPrefixThresholds

open Filter Topology

noncomputable section

def lowerCenter (k : ℕ) : ℝ := (k : ℝ)-Real.log (Real.log k)/Real.log 2-1

def upperCenter (epsilon : ℝ) (k : ℕ) : ℝ :=
  (k : ℝ)+Real.log k/Real.log 2+(1+epsilon)*Real.log (Real.log k)/Real.log 2

def lowerThreshold (k : ℕ) : ℕ := ⌊lowerCenter k⌋₊

def upperThreshold (epsilon : ℝ) (k : ℕ) : ℕ := ⌈upperCenter epsilon k⌉₊

theorem log_div_nat_tendsto_zero :
    Tendsto (fun k : ℕ => Real.log k/(k : ℝ)) atTop (𝓝 0) := by
  simpa only [Function.comp_def,id_eq] using
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop

theorem log_log_div_nat_tendsto_zero :
    Tendsto (fun k : ℕ => Real.log (Real.log k)/(k : ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun k : ℕ => Real.log k) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply squeeze_zero' ?_ ?_ log_div_nat_tendsto_zero
  · filter_upwards [hlog.eventually (eventually_ge_atTop (1 : ℝ))] with k hk
    exact div_nonneg (Real.log_nonneg hk) (Nat.cast_nonneg k)
  · filter_upwards [hlog.eventually (eventually_gt_atTop (0 : ℝ))] with k hk
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg k)
    linarith [Real.log_le_sub_one_of_pos hk]

theorem center_ratio_tendsto_one (epsilon : ℝ) :
    Tendsto (fun k => lowerCenter k/(k : ℝ)) atTop (𝓝 1) ∧
    Tendsto (fun k => upperCenter epsilon k/(k : ℝ)) atTop (𝓝 1) := by
  have hlog := log_div_nat_tendsto_zero.div_const (Real.log 2)
  have hloglog := log_log_div_nat_tendsto_zero.div_const (Real.log 2)
  have hi : Tendsto (fun k : ℕ => 1/(k : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hid : Tendsto (fun k : ℕ => (k : ℝ)/(k : ℝ)) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
    simp [ne_of_gt (show (0 : ℝ)<k by exact_mod_cast (show 0<k by omega))]
  constructor
  · convert (hid.sub hloglog).sub hi using 1 <;> (try simp only [zero_div,sub_zero])
    ext k
    unfold lowerCenter
    ring
  · convert (hid.add hlog).add (hloglog.const_mul (1+epsilon)) using 1 <;> (try simp only [zero_div,mul_zero,add_zero])
    ext k
    unfold upperCenter
    ring

theorem centers_nonneg_eventually (epsilon : ℝ) :
    ∀ᶠ k in atTop, 0 ≤ lowerCenter k ∧ 0 ≤ upperCenter epsilon k := by
  obtain ⟨hl,hu⟩ := center_ratio_tendsto_one epsilon
  filter_upwards [hl.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ)<1)),
    hu.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ)<1)),
    eventually_ge_atTop (1 : ℕ)] with k hl hu hk
  have hk0 : (0 : ℝ)<k := by exact_mod_cast (show 0<k by omega)
  exact ⟨(div_pos_iff.mp hl).resolve_right (by simp [hk0.not_gt]) |>.1.le,
    (div_pos_iff.mp hu).resolve_right (by simp [hk0.not_gt]) |>.1.le⟩

theorem threshold_rounding (epsilon : ℝ) :
    ∀ᶠ k in atTop,
      lowerCenter k-1 ≤ (lowerThreshold k : ℝ) ∧
      (lowerThreshold k : ℝ) ≤ lowerCenter k ∧
      upperCenter epsilon k ≤ (upperThreshold epsilon k : ℝ) ∧
      (upperThreshold epsilon k : ℝ) ≤ upperCenter epsilon k+1 := by
  filter_upwards [centers_nonneg_eventually epsilon] with k hk
  exact ⟨by have := Nat.lt_floor_add_one (lowerCenter k); unfold lowerThreshold; linarith,
    Nat.floor_le hk.1,Nat.le_ceil _,by have := Nat.ceil_lt_add_one hk.2; unfold upperThreshold; linarith⟩

theorem threshold_ratio_tendsto_one (epsilon : ℝ) :
    Tendsto (fun k => (lowerThreshold k : ℝ)/(k : ℝ)) atTop (𝓝 1) ∧
    Tendsto (fun k => (upperThreshold epsilon k : ℝ)/(k : ℝ)) atTop (𝓝 1) := by
  obtain ⟨hl,hu⟩ := center_ratio_tendsto_one epsilon
  have hi : Tendsto (fun k : ℕ => 1/(k : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  constructor
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using hl.sub hi) hl
    · filter_upwards [threshold_rounding epsilon] with k hk
      simpa only [sub_div,one_div] using div_le_div_of_nonneg_right hk.1 (Nat.cast_nonneg k)
    · filter_upwards [threshold_rounding epsilon] with k hk
      exact div_le_div_of_nonneg_right hk.2.1 (Nat.cast_nonneg k)
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hu (by simpa using hu.add hi)
    · filter_upwards [threshold_rounding epsilon] with k hk
      exact div_le_div_of_nonneg_right hk.2.2.1 (Nat.cast_nonneg k)
    · filter_upwards [threshold_rounding epsilon] with k hk
      simpa only [add_div,one_div] using div_le_div_of_nonneg_right hk.2.2.2 (Nat.cast_nonneg k)

/-- Both thresholds lie in a single fixed whole logarithmic band. -/
theorem threshold_band_eventually (epsilon : ℝ) :
    ∀ᶠ k in atTop, ∀ L ∈ ({lowerThreshold k,upperThreshold epsilon k} : Finset ℕ),
      (1/(2*Real.log 2))*Real.log (2^k : ℕ) ≤ (L : ℝ)+1 ∧
      (L : ℝ)+1 ≤ (2/Real.log 2)*Real.log (2^k : ℕ) := by
  obtain ⟨hl,hu⟩ := threshold_ratio_tendsto_one epsilon
  have hi : Tendsto (fun k : ℕ => 1/(k : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hl' := hl.add hi
  have hu' := hu.add hi
  simp only [add_zero] at hl' hu'
  filter_upwards [hl'.eventually (eventually_gt_nhds (by norm_num : (1/2 : ℝ)<1)),
    hl'.eventually (eventually_lt_nhds (by norm_num : (1 : ℝ)<2)),
    hu'.eventually (eventually_gt_nhds (by norm_num : (1/2 : ℝ)<1)),
    hu'.eventually (eventually_lt_nhds (by norm_num : (1 : ℝ)<2)),
    eventually_ge_atTop (1 : ℕ)] with k hll hlu hul huu hk L hL
  have hk0 : (0 : ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  simp only [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
  have he1 : 1/(2*Real.log 2)*((k : ℝ)*Real.log 2) = (k : ℝ)/2 := by field_simp
  have he2 : 2/Real.log 2*((k : ℝ)*Real.log 2) = 2*(k : ℝ) := by field_simp
  rw [he1,he2]
  simp only [Finset.mem_insert,Finset.mem_singleton] at hL
  rcases hL with rfl | rfl
  · have hl1 := (lt_div_iff₀ hk0).mp (show (1/2 : ℝ)<((lowerThreshold k : ℝ)+1)/k by simpa [add_div] using hll)
    have hl2 := (div_lt_iff₀ hk0).mp (show ((lowerThreshold k : ℝ)+1)/k<2 by simpa [add_div] using hlu)
    constructor <;> linarith
  · have hl1 := (lt_div_iff₀ hk0).mp (show (1/2 : ℝ)<((upperThreshold epsilon k : ℝ)+1)/k by simpa [add_div] using hul)
    have hl2 := (div_lt_iff₀ hk0).mp (show ((upperThreshold epsilon k : ℝ)+1)/k<2 by simpa [add_div] using huu)
    constructor <;> linarith

/-- Exact target intensity on a dyadic prefix. -/
theorem dyadic_intensity_eq_rpow (k L : ℕ) :
    ((2^k : ℕ) : ℝ)/(2 : ℝ)^L = (2 : ℝ)^((k : ℝ)-L) := by
  rw [Real.rpow_sub (by norm_num : (0 : ℝ)<2),Real.rpow_natCast,Real.rpow_natCast]
  norm_cast

theorem two_rpow_logRatio {x : ℝ} (hx : 0<x) :
    (2 : ℝ)^(Real.log x/Real.log 2) = x :=
  Real.rpow_logb (by norm_num) (by norm_num) hx

/-- The unrounded lower threshold has intensity exactly twice log k. -/
theorem lower_center_intensity {k : ℕ} (hk : 1 < k) :
    (2 : ℝ)^((k : ℝ)-lowerCenter k) = 2*Real.log k := by
  have hl : 0<Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast hk)
  have he : (k : ℝ)-lowerCenter k = Real.log (Real.log k)/Real.log 2+1 := by
    unfold lowerCenter
    ring
  rw [he,Real.rpow_add (by norm_num : (0 : ℝ)<2),
    two_rpow_logRatio hl,Real.rpow_one,mul_comm]

/-- The unrounded upper threshold has the summable logarithmic harmonic intensity. -/
theorem upper_center_intensity (epsilon : ℝ) {k : ℕ} (hk : 1 < k) :
    (2 : ℝ)^((k : ℝ)-upperCenter epsilon k) =
      1/((k : ℝ)*(Real.log k)^(1+epsilon)) := by
  have hk0 : (0 : ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hl : 0<Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast hk)
  have he : (k : ℝ)-upperCenter epsilon k =
      -(Real.log k/Real.log 2+(Real.log (Real.log k)/Real.log 2)*(1+epsilon)) := by
    unfold upperCenter
    ring
  rw [he,Real.rpow_neg (by norm_num : (0 : ℝ)≤2),
    Real.rpow_add (by norm_num : (0 : ℝ)<2),Real.rpow_mul (by norm_num : (0 : ℝ)≤2),
    two_rpow_logRatio hk0,
    two_rpow_logRatio hl,one_div]

/-- The natural floor gives precisely the intensity bounds in the proof of7.5. -/
theorem lower_intensity_bounds :
    ∀ᶠ k : ℕ in atTop, 2*Real.log k ≤ ((2^k : ℕ) : ℝ)/(2 : ℝ)^(lowerThreshold k) ∧
      ((2^k : ℕ) : ℝ)/(2 : ℝ)^(lowerThreshold k) < 4*Real.log k := by
  filter_upwards [threshold_rounding 0,eventually_ge_atTop (2 : ℕ)] with k hk hk2
  rw [dyadic_intensity_eq_rpow]
  constructor
  · rw [← lower_center_intensity (by omega : 1<k)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [hk.2.1])
  · have hlt : (k : ℝ)-(lowerThreshold k : ℝ) < (k : ℝ)-lowerCenter k+1 := by
      have hh := Nat.lt_floor_add_one (lowerCenter k)
      change lowerCenter k < (lowerThreshold k : ℝ)+1 at hh
      linarith
    have hh := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ)<2) hlt
    rw [Real.rpow_add (by norm_num : (0 : ℝ)<2),lower_center_intensity (by omega),Real.rpow_one] at hh
    linarith

/-- The ceiling gives the stated summable upper intensity. -/
theorem upper_intensity_le (epsilon : ℝ) {k : ℕ} (hk : 1 < k) :
    ((2^k : ℕ) : ℝ)/(2 : ℝ)^(upperThreshold epsilon k) ≤
      1/((k : ℝ)*(Real.log k)^(1+epsilon)) := by
  rw [dyadic_intensity_eq_rpow,← upper_center_intensity epsilon hk]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hh := Nat.le_ceil (upperCenter epsilon k)
  change upperCenter epsilon k ≤ (upperThreshold epsilon k : ℝ) at hh
  linarith

/-- The target lower-tail probability is eventually at most k to power minus two. -/
theorem lower_target_void_le :
    ∀ᶠ k in atTop,
      Real.exp (-(((2^k : ℕ) : ℝ)/(2 : ℝ)^(lowerThreshold k))) ≤ (k : ℝ)^(-2 : ℝ) := by
  filter_upwards [lower_intensity_bounds,eventually_ge_atTop (1 : ℕ)] with k hk hk1
  rw [Real.rpow_def_of_pos (by exact_mod_cast (show 0<k by omega))]
  apply Real.exp_le_exp.mpr
  linarith [hk.1]

end
end PaperC.V282.DyadicPrefixThresholds
