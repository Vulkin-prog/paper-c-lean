import PaperCV282.PoissonResolvedTarget
import Mathlib.Analysis.SpecialFunctions.Stirling

/-! # An effective, intensity-uniform local Poisson approximation

The remainder is derived from mathlib's Robbins stepwise bound; no local-limit
estimate is introduced as a hypothesis.
-/
namespace PaperC.V282.PoissonStirlingBounds

open Filter Real Stirling
open scoped Topology

noncomputable section

def stirlingLogError (n : ℕ) : ℝ := log (stirlingSeq n) - log (sqrt π)

theorem stirlingLogError_nonneg {n : ℕ} (hn : 0 < n) : 0 ≤ stirlingLogError n := by
  exact sub_nonneg.mpr (log_le_log (by positivity) (sqrt_pi_le_stirlingSeq (by omega)))

/-- Telescoping Robbins' bound and taking the Stirling limit yields the explicit remainder. -/
theorem stirlingLogError_le {n : ℕ} (hn : 0 < n) :
    stirlingLogError n ≤ 1 / (12 * n) := by
  let f (k : ℕ) := log (stirlingSeq (n + k))
  let g (k : ℕ) : ℝ := 1 / (12 * (n + k))
  have hstep (k : ℕ) : f k - f (k + 1) ≤ g k - g (k + 1) := by
    have hp : (0 : ℝ) < n + k := by positivity
    have hid : (1 : ℝ) / (12 * (n + k) * (n + k + 1)) =
        1 / (12 * (n + k)) - 1 / (12 * (n + (k + 1))) := by
      field_simp
      ring
    have h := log_stirlingSeq_sdiff_le (n + k)
    push_cast at h
    simpa only [f, g, Nat.add_assoc, Nat.cast_add, Nat.cast_one, hid] using h
  have hbound (k : ℕ) : f 0 ≤ f k + g 0 := by
    have h := Finset.sum_le_sum (s := Finset.range k) (fun j _ => hstep j)
    rw [Finset.sum_range_sub', Finset.sum_range_sub'] at h
    have hg : 0 ≤ g k := by positivity
    linarith
  have hlim : Tendsto f atTop (𝓝 (log (sqrt π))) := by
    exact (tendsto_stirlingSeq_sqrt_pi.comp (by simpa [Nat.add_comm] using tendsto_add_atTop_nat n)).log (by positivity)
  have h := ge_of_tendsto (hlim.add_const (g 0)) (Filter.Eventually.of_forall hbound)
  simpa only [f, g, Nat.add_zero, Nat.cast_zero, add_zero, stirlingLogError, sub_le_iff_le_add, add_comm] using h

/-- The Poisson large-deviation entropy. -/
def poissonEntropy (u : ℝ) : ℝ := u * log u - u + 1

def poissonLocalApprox (rate : ℝ) (n : ℕ) : ℝ :=
  exp (-rate * poissonEntropy (n / rate)) / sqrt (2 * π * n)

theorem poisson_entropy_identity {rate : ℝ} (hr : 0 < rate) {n : ℕ} (hn : 0 < n) :
    rate * poissonEntropy (n / rate) = n * log n - n + rate - n * log rate := by
  rw [poissonEntropy, log_div (by positivity) hr.ne']
  field_simp
  ring

theorem log_factorial_eq {n : ℕ} (hn : 0 < n) :
    log (n.factorial : ℝ) = n * log n - n + log (sqrt (2 * π * n)) +
      stirlingLogError n := by
  unfold stirlingLogError
  rw [log_stirlingSeq_formula, log_div (by positivity) (by positivity), log_exp,
    log_sqrt (by positivity), log_sqrt (by positivity),
    log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
    log_mul (by positivity) (by positivity)]
  ring

/-- The relative correction depends only on n, not on the positive intensity. -/
theorem poisson_local_exact {rate : ℝ} (hr : 0 < rate) {n : ℕ} (hn : 0 < n) :
    exp (-rate) * rate ^ n / n.factorial =
      exp (-stirlingLogError n) * poissonLocalApprox rate n := by
  apply log_injOn_pos (by change (0 : ℝ) < _; positivity)
    (by change (0 : ℝ) < _; unfold poissonLocalApprox; positivity)
  rw [log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity),
    log_exp, log_pow, log_factorial_eq hn]
  rw [log_mul (by positivity) (by unfold poissonLocalApprox; positivity)]
  unfold poissonLocalApprox
  rw [log_exp, log_div (by positivity) (by positivity), log_exp]
  rw [show -rate * poissonEntropy (n / rate) =
      -(rate * poissonEntropy (n / rate)) by ring, poisson_entropy_identity hr hn]
  ring

/-- A global two-sided local estimate, uniform over every rate > 0. -/
theorem poisson_local_bounds {rate : ℝ} (hr : 0 < rate) {n : ℕ} (hn : 0 < n) :
    exp (-(1 / (12 * n))) * poissonLocalApprox rate n ≤
        exp (-rate) * rate ^ n / n.factorial ∧
      exp (-rate) * rate ^ n / n.factorial ≤ poissonLocalApprox rate n := by
  rw [poisson_local_exact hr hn]
  have hpos : 0 ≤ poissonLocalApprox rate n := by unfold poissonLocalApprox; positivity
  constructor
  · exact mul_le_mul_of_nonneg_right (exp_le_exp.mpr (neg_le_neg (stirlingLogError_le hn))) hpos
  · exact mul_le_of_le_one_left hpos (exp_le_one_iff.mpr (neg_nonpos.mpr (stirlingLogError_nonneg hn)))

/-- The printed 1+O(1/n) has the effective absolute relative error 1/(12n). -/
theorem poisson_local_relative_error {rate : ℝ} (hr : 0 < rate) {n : ℕ} (hn : 0 < n) :
    |(exp (-rate) * rate ^ n / n.factorial) / poissonLocalApprox rate n - 1| ≤
      1 / (12 * n) := by
  have hp : 0 < poissonLocalApprox rate n := by unfold poissonLocalApprox; positivity
  rw [poisson_local_exact hr hn, mul_div_cancel_right₀ _ hp.ne']
  have he := stirlingLogError_nonneg hn
  have hle : exp (-stirlingLogError n) ≤ 1 := exp_le_one_iff.mpr (by linarith)
  rw [abs_of_nonpos (by linarith)]
  have h := add_one_le_exp (-stirlingLogError n)
  have hu := stirlingLogError_le hn
  linarith

end
end PaperC.V282.PoissonStirlingBounds
