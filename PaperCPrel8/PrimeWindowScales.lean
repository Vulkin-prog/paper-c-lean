import PaperCPrel8.PrimeWitnessCountBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # The literal q-1+floor(log₂ q) window in G.9 -/
namespace PaperC.Prel8.PrimeWindowScales
open Filter Topology
noncomputable section

def offset (q : ℕ) : ℕ := Nat.log 2 q
def height (q : ℕ) : ℕ := q-1+offset q
def window (q : ℕ) : ℕ := 2^height q

theorem offset_floor (q : ℕ) : offset q=⌊Real.logb 2 q⌋₊ := by
  simpa [offset] using (Real.natFloor_logb_natCast 2 q).symm

theorem offset_ratio : Tendsto (fun q : ℕ ↦ (offset q:ℝ)/q) atTop (𝓝 0) := by
  have hh : Tendsto (fun q : ℕ ↦ (Real.log q/(q:ℝ))/Real.log 2) atTop (𝓝 0) := by
    simpa using (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun q : ℕ ↦ (q:ℝ)) atTop atTop)).div_const (Real.log 2)
  apply squeeze_zero' (Eventually.of_forall (fun q ↦ by positivity)) _ hh
  apply Eventually.of_forall
  intro q
  have h := Real.natLog_le_logb q 2
  have he : (Real.logb 2 q)/(q:ℝ)=(Real.log q/(q:ℝ))/Real.log 2 := by rw [Real.logb]; ring
  rw [← he]
  exact div_le_div_of_nonneg_right h (by positivity)

theorem height_ratio : Tendsto (fun q : ℕ ↦ (height q:ℝ)/q) atTop (𝓝 1) := by
  have hi : Tendsto (fun q : ℕ ↦ 1/(q:ℝ)) atTop (𝓝 0) := by
    simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun q : ℕ ↦ (q:ℝ)) atTop atTop)
  have hh := ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1:ℝ)) atTop (𝓝 1)).sub hi).add offset_ratio
  have hh' : Tendsto (fun q : ℕ ↦ 1-1/(q:ℝ)+(offset q:ℝ)/q) atTop (𝓝 1) := by simpa using hh
  apply hh'.congr'
  filter_upwards [eventually_ge_atTop 1] with q hq
  have hqr : (q:ℝ)≠0 := by positivity
  simp only [height,Nat.cast_add,Nat.cast_sub hq,Nat.cast_one]
  field_simp

theorem log_window (q : ℕ) : Real.log (window q)=(height q:ℝ)*Real.log 2 := by
  simp [window,Real.log_pow]

theorem log_ratio : Tendsto (fun q : ℕ ↦ Real.log (window q)/(q:ℝ)) atTop (𝓝 (Real.log 2)) := by
  have hh := height_ratio.mul_const (Real.log 2)
  simpa only [one_mul] using hh.congr (fun q ↦ by rw [log_window]; ring)

theorem window_pos (q : ℕ) : 0<window q := by unfold window; positivity

theorem twice_window_lower {q : ℕ} (hq : 1≤q) : (2:ℝ)^q ≤ 2*(window q:ℝ) := by
  have he : q≤height q+1 := by unfold height; omega
  have hh := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) he
  simpa only [pow_succ,window,Nat.cast_pow,Nat.cast_ofNat,mul_comm] using hh

/-- Every fixed polynomial in q is negligible compared with the actual window. -/
theorem polynomial_ratio (k : ℕ) :
    Tendsto (fun q : ℕ ↦ (q:ℝ)^k/(window q:ℝ)) atTop (𝓝 0) := by
  have hh := (tendsto_pow_const_div_const_pow_of_one_lt k (by norm_num : (1:ℝ)<2)).const_mul 2
  apply squeeze_zero' (Eventually.of_forall (fun q ↦ by positivity)) _ (by simpa using hh)
  filter_upwards [eventually_ge_atTop 1] with q hq
  have hw : (0:ℝ)<window q := by exact_mod_cast window_pos q
  have hp : (0:ℝ)<2^q := by positivity
  have hh := mul_le_mul_of_nonneg_left (twice_window_lower hq) (show (0:ℝ)≤(q:ℝ)^k by positivity)
  apply (div_le_iff₀ hw).mpr
  have he : 2*((q:ℝ)^k/2^q)*(window q:ℝ) = ((q:ℝ)^k*(2*(window q:ℝ)))/2^q := by ring
  rw [he]
  exact (le_div_iff₀ hp).mpr hh

theorem window_tendsto : Tendsto window atTop atTop := by
  apply tendsto_atTop_atTop.mpr
  intro b
  refine ⟨max 1 b,fun q hq ↦ ?_⟩
  have hp := (q-1).lt_two_pow_self
  have he : q-1≤height q := by unfold height; omega
  have hh : 2^(q-1)≤window q := Nat.pow_le_pow_right (by omega) he
  omega

end
end PaperC.Prel8.PrimeWindowScales
