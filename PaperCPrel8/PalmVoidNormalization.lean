import PaperCPrel8.PalmDeficit
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Uniform normalization of a one-sided void deficit

The estimate needs no bound on the normalized void x. This avoids amplifying
a small absolute approximation by the reciprocal of a tiny void probability.
-/
namespace PaperC.Prel8.PalmVoidNormalization
open PaperC.Prel8.PalmDeficit
noncomputable section

theorem small_scale_deficit {b x : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) (hx : 0 ≤ x) :
    |max (1-b*x) 0-max (1-x) 0| ≤ 1-b := by
  have hbx : b*x ≤ x := mul_le_of_le_one_left hx hb1
  have hmax : max (1-x) 0 ≤ max (1-b*x) 0 := max_le_max (by linarith) le_rfl
  rw [abs_of_nonneg (sub_nonneg.mpr hmax)]
  by_cases h1 : 0 ≤ 1-x
  · rw [max_eq_left h1,max_eq_left (by linarith : 0 ≤ 1-b*x)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hb1) h1]
  · rw [max_eq_right (le_of_not_ge h1)]
    apply (sub_le_iff_le_add).mpr
    apply max_le
    · nlinarith [mul_nonneg hb (show 0 ≤ x-1 by linarith)]
    · linarith

/-- Literal logarithmic normalization bound from the proof of G.4. -/
theorem deficit_log_bound {b x : ℝ} (hb : 0 < b) (hx : 0 ≤ x) :
    |max (1-b*x) 0-max (1-x) 0| ≤ |Real.log b| := by
  by_cases hb1 : b ≤ 1
  · have h := small_scale_deficit hb.le hb1 hx
    have hl := Real.log_le_sub_one_of_pos hb
    rw [abs_of_nonpos (Real.log_nonpos hb.le hb1)]
    linarith
  · have hbi : b⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    have h := small_scale_deficit (inv_nonneg.mpr hb.le) hbi (mul_nonneg hb.le hx)
    rw [inv_mul_cancel_left₀ hb.ne'] at h
    rw [abs_sub_comm] at h
    have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hb)
    rw [Real.log_inv] at hl
    rw [abs_of_nonneg (Real.log_nonneg (by linarith))]
    linarith

/-- Normalizing by exp(mu)*(1-p)^(g-k) costs its log error, not its size. -/
theorem bernoulli_void_normalization {p mu x : ℝ} {g k : ℕ}
    (hp : p < 1) (hx : 0 ≤ x) :
    |max (1-Real.exp mu*(1-p)^(g-k)*x) 0-max (1-x) 0| ≤
      |mu+(g-k:ℕ)*Real.log (1-p)| := by
  have h := deficit_log_bound (b := Real.exp mu*(1-p)^(g-k)) (by positivity) hx
  rwa [Real.log_mul (Real.exp_ne_zero _) (by positivity),Real.log_exp,Real.log_pow] at h

/-- A quantitative elementary log remainder, sufficient for the paper's O(g*p^2) term. -/
theorem log_one_sub_remainder {p : ℝ} (hp : 0 ≤ p) (hp1 : p < 1) :
    |Real.log (1-p)+p| ≤ p^2/(1-p) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := p) (by simpa [abs_of_nonneg hp,add_comm] using hp1) 1
  simpa [abs_of_nonneg hp,add_comm] using h

/-- Uniform over all plants of size at most g, with an explicit harmless constant. -/
theorem bernoulli_log_error {p : ℝ} {g k : ℕ} (hp : 0 ≤ p) (hp1 : p < 1) (hk : k ≤ g) :
    |(g:ℝ)*p+(g-k:ℕ)*Real.log (1-p)| ≤ (k:ℝ)*p+(g:ℝ)*p^2/(1-p) := by
  have he : (g:ℝ)*p+(g-k:ℕ)*Real.log (1-p)=
      (k:ℝ)*p+(g-k:ℕ)*(Real.log (1-p)+p) := by rw [Nat.cast_sub hk]; ring
  rw [he]
  calc
    _ ≤ |(k:ℝ)*p|+|(g-k:ℕ)*(Real.log (1-p)+p)| := abs_add_le _ _
    _ = (k:ℝ)*p+(g-k:ℕ)*|Real.log (1-p)+p| := by simp only [abs_mul,Nat.abs_cast,abs_of_nonneg hp]
    _ ≤ (k:ℝ)*p+(g:ℝ)*(p^2/(1-p)) := by gcongr; exact_mod_cast Nat.sub_le g k; exact log_one_sub_remainder hp hp1
    _ = _ := by ring

end
end PaperC.Prel8.PalmVoidNormalization
