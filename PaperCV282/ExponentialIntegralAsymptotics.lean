import PaperCV282.ExponentialIntegral
import Mathlib.Analysis.Asymptotics.Defs

/-!
# A proved two-term expansion of the exponential integral

The remainder after exp(u)/u + exp(u)/u^2 is eventually at most
5 exp(u)/u^3 in absolute value. The proof compares derivatives on [6,infinity);
it uses no asymptotic formula as an input.
-/

namespace PaperC.V282.ExponentialIntegralAsymptotics

open Set Filter Topology ExponentialIntegral

noncomputable section

def exponentialIntegralRemainder (u : ℝ) : ℝ :=
  exponentialIntegral u - Real.exp u / u - Real.exp u / u ^ 2

theorem hasDerivAt_exp_div_sq {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.exp t / t ^ 2)
      (Real.exp u * (u - 2) / u ^ 3) u := by
  exact ((Real.hasDerivAt_exp u).div ((hasDerivAt_id u).pow 2) (pow_ne_zero _ hu)).congr_deriv
    (by dsimp; field_simp)

theorem hasDerivAt_exp_div_cube {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.exp t / t ^ 3)
      (Real.exp u * (u - 3) / u ^ 4) u := by
  exact ((Real.hasDerivAt_exp u).div ((hasDerivAt_id u).pow 3) (pow_ne_zero _ hu)).congr_deriv
    (by dsimp; field_simp)

theorem hasDerivAt_exponentialIntegralRemainder {u : ℝ} (hu : 0 < u) :
    HasDerivAt exponentialIntegralRemainder (2 * Real.exp u / u ^ 3) u := by
  have hfirst := (Real.hasDerivAt_exp u).div (hasDerivAt_id u) (ne_of_gt hu)
  change HasDerivAt
    (fun t => exponentialIntegral t - Real.exp t / t - Real.exp t / t ^ 2) _ u
  exact (((hasDerivAt_exponentialIntegral hu).sub hfirst).sub
    (hasDerivAt_exp_div_sq (ne_of_gt hu))).congr_deriv
    (by dsimp; field_simp [ne_of_gt hu]; ring)

def exponentialIntegralUpperControl (u : ℝ) : ℝ :=
  4 * (Real.exp u / u ^ 3) - exponentialIntegralRemainder u

theorem hasDerivAt_exponentialIntegralUpperControl {u : ℝ} (hu : 0 < u) :
    HasDerivAt exponentialIntegralUpperControl
      (2 * Real.exp u * (u - 6) / u ^ 4) u := by
  change HasDerivAt (fun t => 4 * (Real.exp t / t ^ 3) - exponentialIntegralRemainder t) _ u
  exact (((hasDerivAt_exp_div_cube (ne_of_gt hu)).const_mul 4).sub
    (hasDerivAt_exponentialIntegralRemainder hu)).congr_deriv
    (by field_simp [ne_of_gt hu]; ring)

theorem strictMonoOn_exponentialIntegralRemainder :
    StrictMonoOn exponentialIntegralRemainder (Ici 6) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 6)
  · intro u hu
    exact (hasDerivAt_exponentialIntegralRemainder
      (by linarith [show 6 ≤ u from hu])).continuousAt.continuousWithinAt
  · intro u hu
    have hu6 : 6 < u := by simpa only [interior_Ici, mem_Ioi] using hu
    rw [(hasDerivAt_exponentialIntegralRemainder (by linarith)).deriv]
    positivity

theorem strictMonoOn_exponentialIntegralUpperControl :
    StrictMonoOn exponentialIntegralUpperControl (Ici 6) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 6)
  · intro u hu
    exact (hasDerivAt_exponentialIntegralUpperControl
      (by linarith [show 6 ≤ u from hu])).continuousAt.continuousWithinAt
  · intro u hu
    have hu6 : 6 < u := by simpa only [interior_Ici, mem_Ioi] using hu
    rw [(hasDerivAt_exponentialIntegralUpperControl (by linarith)).deriv]
    exact div_pos (mul_pos (by positivity) (by linarith)) (by positivity)

theorem exponentialIntegralRemainder_bound {u : ℝ} (hu : 6 ≤ u) :
    |exponentialIntegralRemainder u| ≤
      |exponentialIntegralRemainder 6| + 4 * (Real.exp u / u ^ 3) := by
  have hlo := strictMonoOn_exponentialIntegralRemainder.monotoneOn
    (show (6 : ℝ) ∈ Ici 6 by simp) hu hu
  have hup := strictMonoOn_exponentialIntegralUpperControl.monotoneOn
    (show (6 : ℝ) ∈ Ici 6 by simp) hu hu
  unfold exponentialIntegralUpperControl at hup
  have hzero : 0 ≤ 4 * (Real.exp u / u ^ 3) := by positivity
  have hsix : 0 ≤ 4 * (Real.exp 6 / (6 : ℝ) ^ 3) := by positivity
  exact abs_le.2 ⟨by linarith [neg_abs_le (exponentialIntegralRemainder 6)],
    by linarith [le_abs_self (exponentialIntegralRemainder 6)]⟩

theorem exponentialIntegralRemainder_bound_eventually :
    ∀ᶠ u : ℝ in atTop,
      |exponentialIntegralRemainder u| ≤ 5 * (Real.exp u / u ^ 3) := by
  filter_upwards [eventually_ge_atTop 6,
    (Real.tendsto_exp_div_pow_atTop 3).eventually
      (eventually_ge_atTop |exponentialIntegralRemainder 6|)] with u hu hlarge
  have h := exponentialIntegralRemainder_bound hu
  linarith

theorem exponentialIntegral_two_term_expansion :
    (fun u => exponentialIntegral u - Real.exp u / u - Real.exp u / u ^ 2)
      =O[atTop] (fun u : ℝ => Real.exp u / u ^ 3) := by
  apply Asymptotics.IsBigO.of_bound 5
  filter_upwards [exponentialIntegralRemainder_bound_eventually, eventually_ge_atTop (1 : ℝ)]
    with u hu hupos
  simpa only [exponentialIntegralRemainder, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ Real.exp u / u ^ 3 by positivity)] using hu

end

end PaperC.V282.ExponentialIntegralAsymptotics
