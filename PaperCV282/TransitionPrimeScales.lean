import PaperCV282.MediumIncidenceAsymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Real.Sqrt

/-! # Prime-count scales for the transition minor

Fixed endpoint shifts and the square-root cutoff are negligible relative
to pi(B). All estimates retain inclusive counting conventions.
-/

namespace PaperC.V282.TransitionPrimeScales

open Filter PrimeEulerPNT PrimeEulerAbel MediumPrimeScaling MediumIncidenceAsymptotics
open PostQuadraticPrimeBounds
open scoped Topology

noncomputable section

/-- Adding k integers adds at most k prime species. -/
theorem primeCounting_add_le (n k : ℕ) : Nat.primeCounting (n + k) ≤ Nat.primeCounting n + k := by
  unfold Nat.primeCounting Nat.primeCounting'
  rw [show n + k + 1 = (n + 1) + k by omega,Nat.count_add]
  exact Nat.add_le_add_left (Nat.count_le _) _

theorem primeCounting_le_succ (n : ℕ) : Nat.primeCounting n ≤ n + 1 := Nat.count_le _

/-- Doubling B doubles its prime count asymptotically. -/
theorem doubled_prime_count_ratio (hPNT : PrimeNumberTheoremRemainder) :
    Tendsto (fun B : ℕ => (Nat.primeCounting (2 * B) : ℝ) / Nat.primeCounting B)
      atTop (𝓝 2) := by
  have h := (primeCountingReal_div_ratio hPNT (by norm_num : (0 : ℝ) < 1 / 2)).comp
    tendsto_natCast_atTop_atTop
  have heq : (fun B : ℕ => primeCountingReal ((B : ℝ) / (1 / 2)) / primeCountingReal B) =
      (fun B : ℕ => (Nat.primeCounting (2 * B) : ℝ) / Nat.primeCounting B) := by
    funext B
    have harg : (B : ℝ) / (1 / 2) = ((2 * B : ℕ) : ℝ) := by push_cast; ring
    simp only [primeCountingReal,harg,Nat.floor_natCast]
  simpa only [Function.comp_def,heq,one_div_div,div_one] using h

/-- The logarithm is negligible compared with the square root. -/
theorem sqrt_log_over_self_tendsto_zero :
    Tendsto (fun B : ℕ => Real.sqrt B * Real.log B / B) atTop (𝓝 0) := by
  have h : Tendsto (fun B : ℕ => Real.log B / Real.sqrt B) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow,Function.comp_def] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero.comp
        tendsto_natCast_atTop_atTop
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with B hB
  have hBp : (0 : ℝ) < B := by exact_mod_cast hB
  have hs : 0 < Real.sqrt (B : ℝ) := Real.sqrt_pos.mpr hBp
  have he := Real.sq_sqrt hBp.le
  apply (div_eq_div_iff hs.ne' hBp.ne').mpr
  nlinarith [congrArg (fun z : ℝ => Real.log B * z) he]

/-- Even the number of all integers up to the square-root cutoff is negligible. -/
theorem sqrt_cutoff_over_prime_count (hPNT : PrimeNumberTheoremRemainder) :
    Tendsto (fun B : ℕ => (2 * Real.sqrt B + 3) / Nat.primeCounting B) atTop (𝓝 0) := by
  have hs : Tendsto (fun B : ℕ => Real.sqrt B / Nat.primeCounting B) atTop (𝓝 0) := by
    have h := sqrt_log_over_self_tendsto_zero.div
      (primeCounting_normalized_tendsto_one hPNT) (by norm_num : (1 : ℝ) ≠ 0)
    apply (show Tendsto (fun B : ℕ => (Real.sqrt B * Real.log B / B) /
        ((Nat.primeCounting B : ℝ) * Real.log B / B)) atTop (𝓝 0) by
      simpa only [zero_div,Pi.div_def] using h).congr'
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with B hB
    have hBp : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
    have hlog : Real.log (B : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hB : (1 : ℝ) < B)).ne'
    field_simp
  have hz : Tendsto (fun B : ℕ => 3 / (Nat.primeCounting B : ℝ)) atTop (𝓝 0) := by
    simpa only [prime_count_eq_nat] using (tendsto_const_nhds (x := (3 : ℝ))).div_atTop prime_count_tendsto_atTop
  simpa only [add_div,mul_div_assoc,mul_zero,add_zero] using (hs.const_mul 2).add hz

/-- The literal rounded cutoff from companion E.1. -/
def transitionCutoff (B : ℕ) : ℕ := 2 * Nat.sqrt B + 2

theorem transitionCutoff_square_ge (B : ℕ) : B ≤ (transitionCutoff B) ^ 2 := by
  have h := Nat.lt_succ_sqrt' B
  dsimp [transitionCutoff]
  nlinarith

/-- The cutoff's prime species have asymptotic density zero relative to pi(B). -/
theorem transition_cutoff_prime_ratio (hPNT : PrimeNumberTheoremRemainder) :
    Tendsto (fun B : ℕ => (Nat.primeCounting (transitionCutoff B) : ℝ) / Nat.primeCounting B)
      atTop (𝓝 0) := by
  apply squeeze_zero (fun B => by positivity) _ (sqrt_cutoff_over_prime_count hPNT)
  intro B
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h := primeCounting_le_succ (transitionCutoff B)
  have hr : (Nat.primeCounting (transitionCutoff B) : ℝ) ≤ 2 * (Nat.sqrt B : ℝ) + 3 := by
    have hc : (Nat.primeCounting (transitionCutoff B) : ℝ) ≤ (transitionCutoff B : ℝ) + 1 := by exact_mod_cast h
    simp only [transitionCutoff,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hc ⊢
    linarith
  have hs := Real.nat_sqrt_le_real_sqrt (a := B)
  linarith

end
end PaperC.V282.TransitionPrimeScales
