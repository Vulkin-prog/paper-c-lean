import PaperCV282.SaddlePoissonScales

/-!
# Numerical convergence regimes for the hard and soft saddle rates

These are limits of the explicit numerical profiles, with no probability
distance asserted here. The parameter ell in the soft profile can later be
instantiated with log-positive intensity. Every smallness threshold precedes
the choice of ell or of a bounded intensity.
-/

namespace PaperC.V282.SaddleRateConvergence

open Set Filter Topology SaddleParameters SaddleScales SaddlePoissonScales
open PrimeEulerSaddle

noncomputable section

/-- The polynomial remainder vanishes for the exact range epsilon < 1/3. -/
theorem polynomial_error_nat_tendsto_zero (epsilon : ℝ) (hepsilon : epsilon < 1 / 3) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 / 3 : ℝ) + epsilon)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (by linarith : 0 < (1 / 3 : ℝ) - epsilon)).comp
    tendsto_natCast_atTop_atTop
  have heq : -((1 / 3 : ℝ) - epsilon) = -(1 / 3 : ℝ) + epsilon := by ring
  simpa only [Function.comp_def, heq] using h

/-- A fixed c*nu margin absorbs every eta*nu error with eta < c/2. -/
theorem margin_exponential_nat_tendsto_zero (a c eta : ℝ)
    (ha : 0 < a) (heta : eta < c / 2) :
    Tendsto (fun N : ℕ => Real.exp (-(c / 2 - eta) * saddleNu a (Real.log N)))
      atTop (𝓝 0) := by
  have hnu := (tendsto_saddleNu_atTop ha).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  exact Real.tendsto_exp_atBot.comp (hnu.const_mul_atTop_of_neg (by linarith))

/-- Uniform smallness of the complete soft numerical rate, before ell is chosen. -/
theorem soft_rate_le_eventually (a c eta epsilon delta : ℝ)
    (ha : 0 < a) (heta : eta < c / 2) (hepsilon : epsilon < 1 / 3)
    (hdelta : 0 < delta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ ell : ℝ,
      ell ≤ saddleCutoff a (Real.log N) - c * saddleNu a (Real.log N) →
      Real.exp (-(saddleCutoff a (Real.log N) - ell) / 2 + eta * saddleNu a (Real.log N)) +
        (N : ℝ) ^ (-(1 / 3 : ℝ) + epsilon) ≤ delta := by
  have hlim := (margin_exponential_nat_tendsto_zero a c eta ha heta).add
    (polynomial_error_nat_tendsto_zero epsilon hepsilon)
  obtain ⟨Nzero, hNzero⟩ := eventually_atTop.1
    (hlim.eventually (gt_mem_nhds (by simpa using hdelta)))
  refine ⟨Nzero, fun N hN ell hell => ?_⟩
  have hexp : Real.exp (-(saddleCutoff a (Real.log N) - ell) / 2 + eta * saddleNu a (Real.log N)) ≤
      Real.exp (-(c / 2 - eta) * saddleNu a (Real.log N)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact (add_le_add hexp le_rfl).trans (hNzero N hN).le

/-- The same uniform estimate yields convergence along arbitrary varying ell. -/
theorem soft_rate_tendsto_zero_of_margin (a c eta epsilon : ℝ) (ell : ℕ → ℝ)
    (ha : 0 < a) (heta : eta < c / 2) (hepsilon : epsilon < 1 / 3)
    (hell : ∀ᶠ N in atTop,
      ell N ≤ saddleCutoff a (Real.log N) - c * saddleNu a (Real.log N)) :
    Tendsto (fun N : ℕ =>
      Real.exp (-(saddleCutoff a (Real.log N) - ell N) / 2 + eta * saddleNu a (Real.log N)) +
        (N : ℝ) ^ (-(1 / 3 : ℝ) + epsilon)) atTop (𝓝 0) := by
  apply squeeze_zero' (g := fun N : ℕ =>
    Real.exp (-(c / 2 - eta) * saddleNu a (Real.log N)) +
      (N : ℝ) ^ (-(1 / 3 : ℝ) + epsilon)) (Eventually.of_forall fun N =>
    add_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (Nat.cast_nonneg N) _))
  · filter_upwards [hell] with N hN
    apply add_le_add _ le_rfl
    apply Real.exp_le_exp.mpr
    nlinarith
  · simpa only [add_zero] using
      (margin_exponential_nat_tendsto_zero a c eta ha heta).add
        (polynomial_error_nat_tendsto_zero epsilon hepsilon)

/-- Uniform hard-rate smallness for every intensity in a fixed bounded interval. -/
theorem hard_rate_le_eventually (K eta epsilon delta : ℝ)
    (hepsilon : epsilon < 1 / 3) (hdelta : 0 < delta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ lambda : ℝ, 0 ≤ lambda → lambda ≤ K →
      lambda * (Real.exp (-saddleCutoff 1 (Real.log N) + eta * saddleNu 1 (Real.log N)) +
        (N : ℝ) ^ (-(1 / 3 : ℝ) + epsilon)) ≤ delta := by
  have hlim := ((saddle_exponential_nat_tendsto_zero 1 1 eta (by norm_num) (by norm_num)).add
    (polynomial_error_nat_tendsto_zero epsilon hepsilon)).const_mul K
  simp only [one_mul, neg_mul, add_zero, mul_zero] at hlim
  obtain ⟨Nzero, hNzero⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds hdelta))
  refine ⟨Nzero, fun N hN lambda _ hlambda => ?_⟩
  exact (mul_le_mul_of_nonneg_right hlambda
    (add_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (Nat.cast_nonneg N) _))).trans
      (hNzero N hN).le

/-- The hard numerical rate tends to zero for an arbitrary bounded intensity sequence. -/
theorem hard_rate_tendsto_zero_of_bounded (K eta epsilon : ℝ) (lambda : ℕ → ℝ)
    (hepsilon : epsilon < 1 / 3)
    (hlambda : ∀ᶠ N in atTop, 0 ≤ lambda N ∧ lambda N ≤ K) :
    Tendsto (fun N : ℕ =>
      lambda N * (Real.exp (-saddleCutoff 1 (Real.log N) + eta * saddleNu 1 (Real.log N)) +
        (N : ℝ) ^ (-(1 / 3 : ℝ) + epsilon))) atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards [hlambda] with N hN
    exact mul_nonneg hN.1
      (add_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (Nat.cast_nonneg N) _))
  · filter_upwards [hlambda] with N hN
    exact mul_le_mul_of_nonneg_right hN.2
      (add_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (Nat.cast_nonneg N) _))
  · simpa only [one_mul, neg_mul, add_zero, mul_zero] using
      ((saddle_exponential_nat_tendsto_zero 1 1 eta (by norm_num) (by norm_num)).add
        (polynomial_error_nat_tendsto_zero epsilon hepsilon)).const_mul K

/-- The soft-hard gap, even after any fixed additive loss, dominates nu_soft. -/
theorem soft_hard_gap_div_nu_tendsto_atTop (K : ℝ) :
    Tendsto (fun H => (saddleCutoff 2 H - saddleCutoff 1 H - K) / saddleNu 2 H)
      atTop atTop := by
  have hsqrt : 1 < Real.sqrt 2 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hp := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  have hratio : Tendsto (fun H => saddleCutoff 1 H / saddleCutoff 2 H)
      atTop (𝓝 (1 / Real.sqrt 2)) := by
    rw [one_div]
    apply (tendsto_soft_div_hard_saddle.inv₀ (by positivity)).congr
    intro H
    rw [inv_div]
  have hK : Tendsto (fun H => K / saddleCutoff 2 H) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_saddleCutoff_atTop (by norm_num))
  have hcoef : Tendsto (fun H => 1 - saddleCutoff 1 H / saddleCutoff 2 H - K / saddleCutoff 2 H)
      atTop (𝓝 (1 - 1 / Real.sqrt 2)) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub hratio).sub hK
  have hpos : 0 < 1 - 1 / Real.sqrt 2 := by
    have := (div_lt_one (by positivity : 0 < Real.sqrt 2)).mpr hsqrt
    linarith
  apply (hcoef.pos_mul_atTop hpos (tendsto_saddleCutoff_div_nu (a := 2) (by norm_num))).congr'
  filter_upwards [eventually_ge_atTop (saddleThreshold 2)] with H hH
  have hw := saddleCutoff_pos (by norm_num : (0 : ℝ) < 2) hH
  field_simp [hw.ne']

/-- The whole hard endpoint ell <= V_hard+K lies below every fixed soft margin. -/
theorem hard_endpoint_le_soft_margin_eventually (K c : ℝ) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ ell : ℝ,
      ell ≤ saddleCutoff 1 (Real.log N) + K →
      ell ≤ saddleCutoff 2 (Real.log N) - c * saddleNu 2 (Real.log N) := by
  have hnatlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hgap := ((soft_hard_gap_div_nu_tendsto_atTop K).comp hnatlog).eventually
    (eventually_ge_atTop c)
  have hnu := ((tendsto_saddleNu_atTop (by norm_num : (0 : ℝ) < 2)).comp hnatlog).eventually
    (eventually_gt_atTop 0)
  obtain ⟨Nzero, hNzero⟩ := eventually_atTop.1 (hgap.and hnu)
  refine ⟨Nzero, fun N hN ell hell => ?_⟩
  have h := (le_div_iff₀ (hNzero N hN).2).mp (hNzero N hN).1
  simp only [Function.comp_def] at h
  linarith

/-- In particular, log-positive intensity at the hard endpoint is in the soft convergence regime.
No distance or conditioning statement is inferred from this numerical fact alone. -/
theorem soft_rate_tendsto_zero_at_hard_endpoint (K eta epsilon : ℝ) (ell : ℕ → ℝ)
    (hepsilon : epsilon < 1 / 3)
    (hell : ∀ᶠ N in atTop, ell N ≤ saddleCutoff 1 (Real.log N) + K) :
    Tendsto (fun N : ℕ =>
      Real.exp (-(saddleCutoff 2 (Real.log N) - ell N) / 2 + eta * saddleNu 2 (Real.log N)) +
        (N : ℝ) ^ (-(1 / 3 : ℝ) + epsilon)) atTop (𝓝 0) := by
  obtain ⟨Nzero, hNzero⟩ := hard_endpoint_le_soft_margin_eventually K (2 * eta + 2)
  apply soft_rate_tendsto_zero_of_margin 2 (2 * eta + 2) eta epsilon ell
    (by norm_num) (by linarith) hepsilon
  filter_upwards [eventually_ge_atTop Nzero, hell] with N hN hellN
  exact hNzero N hN (ell N) hellN

end
end PaperC.V282.SaddleRateConvergence
