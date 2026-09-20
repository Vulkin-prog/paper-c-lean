import PaperCPrel8.PrimeWindowScales
import PaperCPrel8.ShiftedCylinderPNT

/-! # Vanishing errors and the exact positive obstruction constant -/
namespace PaperC.Prel8.PrimeWindowErrors
open Filter Topology PrimeWindowScales
noncomputable section

def obstructionConstant : ℝ := Real.log 2/2*(Real.log 3-1)

theorem obstructionConstant_pos : 0<obstructionConstant := by
  have h2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 1<Real.log 3 := (Real.lt_log_iff_exp_lt (by norm_num)).mpr Real.exp_one_lt_three
  unfold obstructionConstant
  positivity

theorem prime_le_window {q : ℕ} (hq : 1≤q) : q≤window q := by
  have hp := (q-1).lt_two_pow_self
  have he : q-1≤height q := by unfold height; omega
  have hh : 2^(q-1)≤window q := Nat.pow_le_pow_right (by omega) he
  omega

theorem inverse_prime : Tendsto (fun q : ℕ ↦ 1/(q:ℝ)) atTop (𝓝 0) := by
  simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun q : ℕ ↦ (q:ℝ)) atTop atTop)

theorem log_div_window :
    Tendsto (fun q : ℕ ↦ Real.log (window q)/(window q:ℝ)) atTop (𝓝 0) := by
  have hh := log_ratio.mul (polynomial_ratio 1)
  apply (show Tendsto (fun q : ℕ ↦ (Real.log (window q)/(q:ℝ))*((q:ℝ)/(window q:ℝ)))
    atTop (𝓝 0) by simpa using hh).congr'
  filter_upwards [eventually_ge_atTop 1] with q hq
  have hqr : (q:ℝ)≠0 := by positivity
  field_simp

theorem log_div_prime_square :
    Tendsto (fun q : ℕ ↦ Real.log (window q)/(q:ℝ)^2) atTop (𝓝 0) := by
  have hh := log_ratio.mul inverse_prime
  convert hh using 1
  · ext q
    ring
  · simp

theorem log_mul_prime_div_window :
    Tendsto (fun q : ℕ ↦ Real.log (window q)*(q:ℝ)/(window q:ℝ)) atTop (𝓝 0) := by
  have hh := log_ratio.mul (polynomial_ratio 2)
  apply (show Tendsto (fun q : ℕ ↦ (Real.log (window q)/(q:ℝ))*((q:ℝ)^2/(window q:ℝ)))
    atTop (𝓝 0) by simpa using hh).congr'
  filter_upwards [eventually_ge_atTop 1] with q hq
  have hqr : (q:ℝ)≠0 := by positivity
  field_simp

/-- In particular, any cylinder extension bounded by a fixed multiple of q is harmless. -/
theorem linear_extension_ratio (Q : ℕ → ℕ) (K : ℝ)
    (hQ : ∀ᶠ q : ℕ in atTop, (Q q:ℝ)≤K*q) :
    Tendsto (fun q ↦ (Q q:ℝ)/(window q:ℝ)) atTop (𝓝 0) := by
  have hh := (polynomial_ratio 1).const_mul K
  apply squeeze_zero' (Eventually.of_forall (fun q ↦ by positivity)) _ (by simpa using hh)
  filter_upwards [hQ] with q hq
  have hh := div_le_div_of_nonneg_right hq (show (0:ℝ)≤window q by positivity)
  convert hh using 1 <;> ring

end
end PaperC.Prel8.PrimeWindowErrors
