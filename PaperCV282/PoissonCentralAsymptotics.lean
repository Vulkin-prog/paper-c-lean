import PaperCV282.PoissonResolutionBudget
import PaperCV282.PoissonEntropyTaylor
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Central Poisson entropy with bounded rounding

The cubic remainder, the logarithmic correction and the actual normalized
coordinate are kept explicit. No Gaussian approximation or probability bound
is assumed here.
-/
namespace PaperC.V282.PoissonCentralAsymptotics

open Filter Topology Real PoissonStirlingBounds

noncomputable section

/-- A bounded factor preserves convergence to zero. -/
theorem bounded_mul_tendsto_zero (u v : ℕ → ℝ) (K : ℝ)
    (hu : ∀ᶠ k in atTop, |u k|≤K) (hv : Tendsto v atTop (𝓝 0)) :
    Tendsto (fun k => u k*v k) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
    (by simpa using hv.norm.const_mul K)
  filter_upwards [hu] with k hk
  simpa only [Real.norm_eq_abs,abs_mul] using mul_le_mul_of_nonneg_right hk (abs_nonneg (v k))

/-- The cubic central hypothesis already forces n/rate to one. -/
theorem ratio_tendsto_one_of_cubic (rate value : ℕ → ℝ)
    (hrate : Tendsto rate atTop atTop)
    (hthird : Tendsto (fun k => |value k-rate k|^3/(rate k)^2) atTop (𝓝 0)) :
    Tendsto (fun k => value k/rate k) atTop (𝓝 1) := by
  have hcube : Tendsto (fun k => (|value k-rate k|/rate k)^3) atTop (𝓝 0) := by
    apply (hthird.div_atTop hrate).congr'
    filter_upwards [hrate.eventually (eventually_gt_atTop (0 : ℝ))] with k hk
    field_simp
  have habs : Tendsto (fun k => |value k-rate k|/rate k) atTop (𝓝 0) := by
    apply (hcube.rpow_const_nhds_zero (by norm_num : (0 : ℝ)<(3 : ℝ)⁻¹)).congr'
    filter_upwards [hrate.eventually (eventually_gt_atTop (0 : ℝ))] with k hk
    exact Real.pow_rpow_inv_natCast (div_nonneg (abs_nonneg _) hk.le) (by norm_num : (3 : ℕ)≠0)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply habs.congr'
  filter_upwards [hrate.eventually (eventually_gt_atTop (0 : ℝ))] with k hk
  rw [Real.norm_eq_abs,← div_self hk.ne',← sub_div,abs_div,abs_of_pos hk]

/-- The log correction tends to zero on the true positive central domain. -/
theorem log_error_tendsto_zero_of_cubic (rate value : ℕ → ℝ)
    (hrate : Tendsto rate atTop atTop)
    (hthird : Tendsto (fun k => |value k-rate k|^3/(rate k)^2) atTop (𝓝 0)) :
    Tendsto (fun k => Real.log (value k)-Real.log (rate k)) atTop (𝓝 0) := by
  have hratio := ratio_tendsto_one_of_cubic rate value hrate hthird
  have hlog := hratio.log (by norm_num : (1 : ℝ)≠0)
  simp only [Real.log_one] at hlog
  apply hlog.congr'
  filter_upwards [hrate.eventually (eventually_gt_atTop (0 : ℝ)),
    hratio.eventually (lt_mem_nhds (by norm_num : (0 : ℝ)<1))] with k hr hn
  have hn0 : value k≠0 := by intro hz;rw [hz,zero_div] at hn;exact (lt_irrefl _ hn)
  exact Real.log_div hn0 hr.ne'

/-- Both natural powers used in the central change of scale are literal real powers. -/
theorem central_rpow_identities {r : ℝ} (hr : 0<r) :
    Real.sqrt r*r^(1/6 : ℝ)=r^(2/3 : ℝ) ∧
    r^(1/6 : ℝ)*r^(1/3 : ℝ)=Real.sqrt r ∧
    (r^(2/3 : ℝ))^3=r^2 := by
  constructor
  · rw [Real.sqrt_eq_rpow,← Real.rpow_add hr]
    norm_num
  constructor
  · rw [← Real.rpow_add hr,Real.sqrt_eq_rpow]
    norm_num
  · rw [← Real.rpow_mul_natCast hr.le]
    norm_num

/-- A small sixth-root coordinate is also small relative to the standard deviation. -/
theorem coordinate_div_sqrt_tendsto_zero (rate t : ℕ → ℝ)
    (hrate : Tendsto rate atTop atTop)
    (ht : Tendsto (fun k => t k/(rate k)^(1/6 : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun k => t k/Real.sqrt (rate k)) atTop (𝓝 0) := by
  have hp := (tendsto_rpow_atTop (by norm_num : (0 : ℝ)<1/3)).comp hrate
  apply (ht.div_atTop hp).congr'
  filter_upwards [hrate.eventually (eventually_gt_atTop (0 : ℝ))] with k hk
  dsimp only [Function.comp_apply]
  rw [div_div,(central_rpow_identities hk).2.1]

/-- A uniformly bounded rounding error is negligible on the two-thirds scale. -/
theorem centered_two_thirds_tendsto_zero (rate value t : ℕ → ℝ) (K : ℝ)
    (hrate : Tendsto rate atTop atTop)
    (ht : Tendsto (fun k => t k/(rate k)^(1/6 : ℝ)) atTop (𝓝 0))
    (herr : ∀ᶠ k in atTop, |value k-(rate k+t k*Real.sqrt (rate k))|≤K) :
    Tendsto (fun k => (value k-rate k)/(rate k)^(2/3 : ℝ)) atTop (𝓝 0) := by
  have hinv := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ)<2/3)).comp hrate).inv_tendsto_atTop
  have he := bounded_mul_tendsto_zero
    (fun k => value k-(rate k+t k*Real.sqrt (rate k))) _ K herr hinv
  have hh := he.add ht
  simp only [add_zero] at hh
  apply hh.congr'
  filter_upwards [hrate.eventually (eventually_gt_atTop (0 : ℝ))] with k hk
  dsimp only [Function.comp_apply,Pi.inv_apply]
  have hp : (rate k)^(1/6 : ℝ)≠0 := (Real.rpow_pos_of_pos hk _).ne'
  have hq : (rate k)^(2/3 : ℝ)≠0 := (Real.rpow_pos_of_pos hk _).ne'
  have hid := (central_rpow_identities hk).1
  field_simp
  nlinarith only [congrArg (fun x => t k*x) hid]

/-- The familiar sixth-root range with bounded rounding implies the actual cubic hypothesis. -/
theorem cubic_error_tendsto_zero_of_bounded_rounding (rate value t : ℕ → ℝ) (K : ℝ)
    (hrate : Tendsto rate atTop atTop)
    (ht : Tendsto (fun k => t k/(rate k)^(1/6 : ℝ)) atTop (𝓝 0))
    (herr : ∀ᶠ k in atTop, |value k-(rate k+t k*Real.sqrt (rate k))|≤K) :
    Tendsto (fun k => |value k-rate k|^3/(rate k)^2) atTop (𝓝 0) := by
  have h := (centered_two_thirds_tendsto_zero rate value t K hrate ht herr).abs.pow 3
  simp only [abs_zero,zero_pow (by norm_num : (3 : ℕ)≠0)] at h
  apply h.congr'
  filter_upwards [hrate.eventually (eventually_gt_atTop (0 : ℝ))] with k hk
  rw [abs_div,abs_of_pos (Real.rpow_pos_of_pos hk _),div_pow,(central_rpow_identities hk).2.2]

/-- The rounded central quadratic differs from t squared over two by a vanishing amount. -/
theorem quadratic_error_tendsto_zero_of_bounded_rounding (rate value t : ℕ → ℝ) (K : ℝ)
    (hrate : Tendsto rate atTop atTop)
    (ht : Tendsto (fun k => t k/(rate k)^(1/6 : ℝ)) atTop (𝓝 0))
    (herr : ∀ᶠ k in atTop, |value k-(rate k+t k*Real.sqrt (rate k))|≤K) :
    Tendsto (fun k => (value k-rate k)^2/(2*rate k)-(t k)^2/2) atTop (𝓝 0) := by
  let e := fun k => value k-(rate k+t k*Real.sqrt (rate k))
  have he := bounded_mul_tendsto_zero e _ K herr (Real.tendsto_sqrt_atTop.comp hrate).inv_tendsto_atTop
  have hp := bounded_mul_tendsto_zero e _ K herr (coordinate_div_sqrt_tendsto_zero rate t hrate ht)
  have h := ((he.pow 2).div_const 2).add hp
  simp only [zero_pow (by norm_num : (2 : ℕ)≠0),zero_div,add_zero] at h
  apply h.congr'
  filter_upwards [hrate.eventually (eventually_gt_atTop (0 : ℝ))] with k hk
  have hs : Real.sqrt (rate k)≠0 := (Real.sqrt_pos.mpr hk).ne'
  have hsq := Real.sq_sqrt hk.le
  dsimp [e]
  field_simp
  nlinarith only [hsq]

/-- Taylor's finite bound gives the actual entropy remainder, not an assumed limit. -/
theorem entropy_error_tendsto_zero_of_cubic (rate value : ℕ → ℝ)
    (hrate : Tendsto rate atTop atTop)
    (hthird : Tendsto (fun k => |value k-rate k|^3/(rate k)^2) atTop (𝓝 0)) :
    Tendsto (fun k => rate k*poissonEntropy (value k/rate k)-
      (value k-rate k)^2/(2*rate k)) atTop (𝓝 0) := by
  have hratio := ratio_tendsto_one_of_cubic rate value hrate hthird
  have hsmall : Tendsto (fun k => |value k/rate k-1|) atTop (𝓝 0) := by
    simpa only [Real.norm_eq_abs] using tendsto_iff_norm_sub_tendsto_zero.mp hratio
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
    (by simpa using hthird.const_mul 2)
  filter_upwards [hrate.eventually (eventually_gt_atTop (0 : ℝ)),
    hsmall.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/2))] with k hr hh
  have hident : |value k/rate k-1|=|value k-rate k|/rate k := by
    rw [← div_self hr.ne',← sub_div,abs_div,abs_of_pos hr]
  rw [hident] at hh
  have hdomain : |value k-rate k|≤rate k/2 := by
    have h := (div_lt_iff₀ hr).mp hh
    linarith
  simpa only [Real.norm_eq_abs,mul_div_assoc] using
    PoissonEntropyTaylor.entropy_central_remainder_le hr hdomain

/-- The central logarithmic and entropy errors for actual integer counts. -/
theorem log_and_entropy_error_tendsto_zero (rate : ℕ → ℝ) (n : ℕ → ℕ)
    (hrate : Tendsto rate atTop atTop)
    (hthird : Tendsto (fun k => |(n k : ℝ)-rate k|^3/(rate k)^2) atTop (𝓝 0)) :
    Tendsto (fun k => Real.log (n k : ℝ)-Real.log (rate k)) atTop (𝓝 0) ∧
    Tendsto (fun k => rate k*poissonEntropy ((n k : ℝ)/rate k)-
      ((n k : ℝ)-rate k)^2/(2*rate k)) atTop (𝓝 0) :=
  ⟨log_error_tendsto_zero_of_cubic rate (fun k => (n k : ℝ)) hrate hthird,
   entropy_error_tendsto_zero_of_cubic rate (fun k => (n k : ℝ)) hrate hthird⟩

/-- The exact normalized coordinate agrees with the quadratic used in the expansion. -/
theorem normalized_coordinate_square {rate value : ℝ} (hr : 0<rate) :
    (value-rate)^2/(2*rate)=((value-rate)/Real.sqrt rate)^2/2 := by
  rw [div_pow,Real.sq_sqrt hr.le]
  ring

/-- Bounded rounding and t=o(rate^(1/6)) give both true central corrections. -/
theorem bounded_rounding_central_errors (rate : ℕ → ℝ) (n : ℕ → ℕ) (t : ℕ → ℝ) (K : ℝ)
    (hrate : Tendsto rate atTop atTop)
    (ht : Tendsto (fun k => t k/(rate k)^(1/6 : ℝ)) atTop (𝓝 0))
    (hround : ∀ᶠ k in atTop, |(n k : ℝ)-(rate k+t k*Real.sqrt (rate k))|≤K) :
    Tendsto (fun k => Real.log (n k : ℝ)-Real.log (rate k)) atTop (𝓝 0) ∧
    Tendsto (fun k => rate k*poissonEntropy ((n k : ℝ)/rate k)-(t k)^2/2)
      atTop (𝓝 0) := by
  have hthird := cubic_error_tendsto_zero_of_bounded_rounding rate (fun k => (n k : ℝ)) t K hrate ht hround
  have hmain := log_and_entropy_error_tendsto_zero rate n hrate hthird
  refine ⟨hmain.1,?_⟩
  have hquad := quadratic_error_tendsto_zero_of_bounded_rounding rate (fun k => (n k : ℝ)) t K hrate ht hround
  have h := hmain.2.add hquad
  simp only [add_zero] at h
  convert h using 1
  funext k
  ring

end
end PaperC.V282.PoissonCentralAsymptotics
