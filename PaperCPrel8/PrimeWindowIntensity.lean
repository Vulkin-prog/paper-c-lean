import PaperCPrel8.PrimeWindowErrors
import PaperCPrel8.MicroscopicPaperBudget

/-! # Intensity and small marginal errors on the explicit prime windows -/
namespace PaperC.Prel8.PrimeWindowIntensity
open Filter Topology PrimeWindowScales PrimeWindowErrors MicroscopicPaperBudget
open V282.AllStartSoftPoisson
noncomputable section

def referenceRate (q : ℕ) : ℝ := 1/(2:ℝ)^(q-1)

theorem ambient_rate_eq (q : ℕ) :
    (fullRate (window q) (q-1):ℝ)=(2:ℝ)^offset q := by
  rw [fullRate_coe]
  simp only [window,height,Nat.cast_pow,Nat.cast_ofNat,pow_add]
  push_cast
  field_simp

theorem ambient_rate_le {q : ℕ} (hq : 1≤q) :
    (fullRate (window q) (q-1):ℝ)≤q := by
  rw [ambient_rate_eq]
  exact_mod_cast Nat.pow_log_le_self 2 (show q≠0 by omega)

theorem site_rate_eq {q : ℕ} (hq : 1≤q) :
    siteRate (window q) (q-1)=(2:ℝ)^offset q-(q-1:ℕ)*referenceRate q := by
  have hlen : q-1≤window q := (Nat.sub_le _ _).trans (prime_le_window hq)
  rw [siteRate,Nat.cast_sub hlen,sub_div]
  have ha := ambient_rate_eq q
  rw [fullRate_coe] at ha
  rw [ha]
  unfold referenceRate
  ring

theorem site_rate_le {q : ℕ} (hq : 1≤q) : siteRate (window q) (q-1)≤q := by
  rw [site_rate_eq hq]
  have ha := ambient_rate_le hq
  rw [ambient_rate_eq] at ha
  have hnon : 0≤((q-1:ℕ):ℝ)*referenceRate q := by unfold referenceRate; positivity
  linarith

theorem length_mass_le_one (q : ℕ) : ((q-1:ℕ):ℝ)*referenceRate q≤1 := by
  have hh : ((q-1:ℕ):ℝ)≤(2:ℝ)^(q-1) := by exact_mod_cast (q-1).lt_two_pow_self.le
  unfold referenceRate
  rw [mul_one_div]
  exact (div_le_one (by positivity)).mpr hh

theorem site_rate_lower {q : ℕ} (hq : 1≤q) :
    (q:ℝ)/2-1≤siteRate (window q) (q-1) := by
  have hh : (q:ℝ)<(2:ℝ)^offset q*2 := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num : 1<2) q
  rw [site_rate_eq hq]
  have hl := length_mass_le_one q
  linarith

theorem site_rate_atTop : Tendsto (fun q ↦ siteRate (window q) (q-1)) atTop atTop := by
  have hd : Tendsto (fun q : ℕ ↦ (q:ℝ)/2) atTop atTop :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun q : ℕ ↦ (q:ℝ)) atTop atTop).atTop_div_const
      (by norm_num : (0:ℝ)<2)
  have hh : Tendsto (fun q : ℕ ↦ (q:ℝ)/2-1) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1) hd
  apply tendsto_atTop_mono' atTop _ hh
  filter_upwards [eventually_ge_atTop 1] with q hq
  exact site_rate_lower hq

theorem referenceRate_quarter {q : ℕ} (hq : 3≤q) : referenceRate q≤1/4 := by
  have hp : (4:ℝ)≤2^(q-1) := by
    have hh := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (show 2≤q-1 by omega)
    norm_num at hh ⊢
    exact hh
  exact one_div_le_one_div_of_le (by norm_num) hp

/-- Exact low-type means at most p imply a total mean mass at most q. -/
theorem marginal_mass_le {q g : ℕ} (hq : 1≤q) (hg : g≤window q) {r : ℝ}
    (hr : 0≤r) (hrp : r≤referenceRate q) : (g:ℝ)*r≤q := by
  have hh := mul_le_mul (show (g:ℝ)≤window q by exact_mod_cast hg) hrp hr
    (show (0:ℝ)≤window q by positivity)
  have he : (window q:ℝ)*referenceRate q=(fullRate (window q) (q-1):ℝ) := by
    rw [fullRate_coe,referenceRate]
    ring
  rw [he] at hh
  exact hh.trans (ambient_rate_le hq)

/-- The error g*r*H/M vanishes for every admissible retained set and low-type cutoff. -/
theorem marginal_error_tendsto (g : ℕ → ℕ) (r : ℕ → ℝ)
    (hg : ∀ᶠ q : ℕ in atTop, g q≤window q ∧ 0≤r q ∧ r q≤referenceRate q) :
    Tendsto (fun q ↦ (g q:ℝ)*r q*Real.log (window q)/(window q:ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ log_mul_prime_div_window
  · filter_upwards [hg] with q hq
    apply div_nonneg _ (by positivity)
    apply mul_nonneg (mul_nonneg (by positivity) hq.2.1)
    exact Real.log_nonneg (by exact_mod_cast (window_pos q))
  · filter_upwards [hg,eventually_ge_atTop 1] with q hq hq1
    have hh := marginal_mass_le hq1 hq.1 hq.2.1 hq.2.2
    have hl : 0≤Real.log (window q) := Real.log_nonneg (by exact_mod_cast (window_pos q))
    have hh' := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hh hl)
      (show (0:ℝ)≤window q by positivity)
    convert hh' using 1 <;> ring

end
end PaperC.Prel8.PrimeWindowIntensity
