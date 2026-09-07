import PaperCV282.PoissonStirlingBounds
import PaperCV282.AggregateCutoffRemainder

/-! # Explicit local costs for resolving a Poisson count -/
namespace PaperC.V282.PoissonResolutionBudget

open Real PoissonStirlingBounds
open Filter Topology SaddleParameters SaddleScales AggregateCutoffRemainder

noncomputable section

def poissonLocalCost (rate : ℝ) (n : ℕ) : ℝ :=
  log n / 2 + rate * poissonEntropy (n / rate)

def poissonStirlingConstant : ℝ := sqrt (2 * π) * exp (1 / 12)

def resolvedInformationCost (I rate : ℝ) (n : ℕ) : ℝ :=
  I + max 0 (log rate) + log (1 + max 0 (log (2 * rate))) + poissonLocalCost rate n

theorem poissonEntropy_nonneg {u : ℝ} (hu : 0 < u) : 0 ≤ poissonEntropy u := by
  have h := mul_le_mul_of_nonneg_left (one_sub_inv_le_log_of_pos hu) hu.le
  rw [mul_sub, mul_one, mul_inv_cancel₀ hu.ne'] at h
  unfold poissonEntropy
  linarith

theorem poissonLocalCost_nonneg {rate : ℝ} (hr : 0 < rate) {n : ℕ} (hn : 0 < n) :
    0 ≤ poissonLocalCost rate n := by
  have hlog : 0 ≤ log (n : ℝ) := log_nonneg (by exact_mod_cast hn)
  exact add_nonneg (div_nonneg hlog (by norm_num))
    (mul_nonneg hr.le (poissonEntropy_nonneg (by positivity)))

theorem poissonStirlingConstant_pos : 0 < poissonStirlingConstant := by
  unfold poissonStirlingConstant
  positivity

theorem poisson_atom_reciprocal_eq {rate : ℝ} (hr : 0 < rate) {n : ℕ} (hn : 0 < n) :
    (exp (-rate) * rate ^ n / n.factorial)⁻¹ =
      sqrt (2 * π) * exp (poissonLocalCost rate n + stirlingLogError n) := by
  apply log_injOn_pos (by change (0 : ℝ) < _; positivity)
    (by change (0 : ℝ) < _; positivity)
  rw [log_inv, log_div (by positivity) (by positivity),
    log_mul (by positivity) (by positivity), log_exp, log_pow,
    log_factorial_eq hn, log_mul (by positivity) (by positivity), log_exp]
  unfold poissonLocalCost
  rw [poisson_entropy_identity hr hn, log_sqrt (by positivity), log_sqrt (by positivity),
    log_mul (by positivity) (by positivity)]
  ring

/-- An actual atom reciprocal, bounded by its local entropy cost. -/
theorem poisson_atom_reciprocal_le {rate : ℝ} (hr : 0 < rate) {n : ℕ} (hn : 0 < n) :
    (exp (-rate) * rate ^ n / n.factorial)⁻¹ ≤
      poissonStirlingConstant * exp (poissonLocalCost rate n) := by
  have he : stirlingLogError n ≤ (1 : ℝ) / 12 := by
    refine (stirlingLogError_le hn).trans ?_
    apply one_div_le_one_div_of_le (by norm_num)
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [poisson_atom_reciprocal_eq hr hn, exp_add]
  unfold poissonStirlingConstant
  have h := mul_le_mul_of_nonneg_left (exp_le_exp.mpr he)
    (show 0 ≤ sqrt (2 * π) * exp (poissonLocalCost rate n) by positivity)
  nlinarith

theorem localCost_le_resolvedInformationCost {I rate : ℝ} (hI : 0 ≤ I) (n : ℕ) :
    poissonLocalCost rate n ≤ resolvedInformationCost I rate n := by
  have hl : 0 ≤ log (1 + max 0 (log (2 * rate))) := log_nonneg (by linarith [le_max_left 0 (log (2 * rate))])
  unfold resolvedInformationCost
  linarith [le_max_left 0 (log rate)]

theorem poisson_resolved_leading_bound {I rate V nu c eta K : ℝ} {n : ℕ}
    (hr : 0 < rate) (hn : 0 < n) (hK : 0 ≤ K)
    (hb : resolvedInformationCost I rate n ≤ V - c * nu) :
    (K * exp I * rate * (1 + max 0 (log (2 * rate))) * exp (-V + eta * nu)) /
      (exp (-rate) * rate ^ n / n.factorial) ≤
        K * poissonStirlingConstant * exp (-(c - eta) * nu) := by
  have hf : 0 < 1 + max 0 (log (2 * rate)) := by linarith [le_max_left 0 (log (2 * rate))]
  have hw : exp I * rate * (1 + max 0 (log (2 * rate))) *
      exp (poissonLocalCost rate n) ≤ exp (resolvedInformationCost I rate n) := by
    have hrate : rate ≤ exp (max 0 (log rate)) := by
      nth_rw 1 [← exp_log hr]
      exact exp_le_exp.mpr (le_max_right _ _)
    have h := mul_le_mul_of_nonneg_left hrate (exp_nonneg I)
    have h' := mul_le_mul_of_nonneg_right h hf.le
    have h'' := mul_le_mul_of_nonneg_right h' (exp_nonneg (poissonLocalCost rate n))
    calc
      _ ≤ exp I * exp (max 0 (log rate)) * (1 + max 0 (log (2 * rate))) *
          exp (poissonLocalCost rate n) := h''
      _ = exp (resolvedInformationCost I rate n) := by
        rw [resolvedInformationCost, exp_add, exp_add, exp_add, exp_log hf]
  have hb' := exp_le_exp.mpr hb
  have hp := poisson_atom_reciprocal_le hr hn
  rw [div_eq_mul_inv]
  calc
    _ ≤ (K * exp I * rate * (1 + max 0 (log (2 * rate))) * exp (-V + eta * nu)) *
        (poissonStirlingConstant * exp (poissonLocalCost rate n)) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = K * poissonStirlingConstant *
        (exp I * rate * (1 + max 0 (log (2 * rate))) * exp (poissonLocalCost rate n)) *
        exp (-V + eta * nu) := by ring
    _ ≤ K * poissonStirlingConstant * exp (V - c * nu) * exp (-V + eta * nu) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hw.trans hb')
        (mul_nonneg hK poissonStirlingConstant_pos.le)) (exp_nonneg _)
    _ = _ := by rw [mul_assoc, ← exp_add]; congr 2; ring

/-- The reciprocal atom remains subpolynomial under the full resolution budget. -/
theorem poisson_resolved_polynomial_bound_eventually (c epsilon : ℝ)
    (hc : 0 ≤ c) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ I rate : ℝ, ∀ n : ℕ, 0 ≤ I → 0 < rate → 0 < n →
      resolvedInformationCost I rate n ≤
        saddleCutoff 1 (log N) - c * saddleNu 1 (log N) →
      (N : ℝ)^(-(1/3 : ℝ)+epsilon/2) /
        (exp (-rate) * rate ^ n / n.factorial) ≤ (N : ℝ)^(-(1/3 : ℝ)+epsilon) := by
  have hlog : Tendsto (fun N : ℕ => log N) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [constant_exp_saddle_le_power_eventually poissonStirlingConstant 1 (epsilon/2)
      poissonStirlingConstant_pos (by linarith),
    hlog.eventually (eventually_ge_atTop (saddleThreshold 1)),
    eventually_ge_atTop (2 : ℕ)] with N hp hN hnN
  intro I rate n hI hr hn hb
  have hV := saddleCutoff_pos (a := 1) (by norm_num) hN
  have hnu : 0 ≤ saddleNu 1 (log N) := div_nonneg
    (log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) hV.le
  have hlocal : poissonLocalCost rate n ≤ saddleCutoff 1 (log N) := by
    have h := localCost_le_resolvedInformationCost (rate := rate) hI n
    nlinarith [mul_nonneg hc hnu]
  have hinv : (exp (-rate) * rate ^ n / n.factorial)⁻¹ ≤ (N : ℝ)^(epsilon/2) := by
    refine (poisson_atom_reciprocal_le hr hn).trans ?_
    apply le_trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr hlocal)
      poissonStirlingConstant_pos.le)
    simpa only [one_mul] using hp
  rw [div_eq_mul_inv]
  calc
    _ ≤ (N : ℝ)^(-(1/3 : ℝ)+epsilon/2) * (N : ℝ)^(epsilon/2) :=
      mul_le_mul_of_nonneg_left hinv (rpow_nonneg (Nat.cast_nonneg N) _)
    _ = _ := by rw [← rpow_add (by positivity : (0 : ℝ) < N)]; congr 1; ring

end
end PaperC.V282.PoissonResolutionBudget
