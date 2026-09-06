import PaperCV282.HardPoissonRates
import PaperCV282.SoftRateAssembly
import PaperCV282.SaddleRateConvergence

/-!
# Convergence of the true Poisson laws in the stated intensity regimes

The numerical saddle estimates are now applied to the source count and
its conditional laws. A fixed positive margin c*nu is retained; no
convergence at the exact soft boundary is asserted.
-/

namespace PaperC.V282.PoissonRateConvergence

open Filter Topology ScalarSteinInput PrimeEulerPNT SaddleParameters SaddleScales
open AllStartSoftPoisson DyadicPoissonDistance HardPoissonRates SoftRateAssembly
open SaddleRateConvergence

noncomputable section

/-- A conditional comparison tending to zero also controls the actual source law. -/
theorem countDistance_tendsto_zero_of_conditional (L Y : ℕ → ℕ)
    (h : Tendsto (fun N => conditionalDistance N (L N) (Y N)) atTop (𝓝 0)) :
    Tendsto (fun N => countDistance N (L N)) atTop (𝓝 0) :=
  squeeze_zero (fun N => countDistance_nonneg N (L N))
    (fun N => countDistance_le_conditionalDistance N (L N) (Y N)) h

/-- Bounded intensity on a fixed logarithmic band gives both hard-cutoff and source convergence. -/
theorem hard_convergence_of_bounded_intensity
    (hStein : ScalarSteinFactorsStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax K : ℝ) (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (L : ℕ → ℕ)
    (hband : ∀ᶠ N : ℕ in atTop,
      betaMin * Real.log N ≤ (L N + 1 : ℝ) ∧ (L N + 1 : ℝ) ≤ betaMax * Real.log N)
    (hintensity : ∀ᶠ N : ℕ in atTop, (fullRate N (L N) : ℝ) ≤ K) :
    Tendsto (fun N => conditionalDistance N (L N) (hardCutoff N)) atTop (𝓝 0) ∧
      Tendsto (fun N => countDistance N (L N)) atTop (𝓝 0) := by
  obtain ⟨Nzero,hzero⟩ := hard_conditional_rate_eventually
    hStein hPNT betaMin betaMax (1 / 6) 1 hbetaMin hbeta (by norm_num) (by norm_num)
  have hlim := hard_rate_tendsto_zero_of_bounded K 1 (1 / 6)
    (fun N => (fullRate N (L N) : ℝ)) (by norm_num)
    (hintensity.mono fun N hN => ⟨(fullRate N (L N)).coe_nonneg,hN⟩)
  have hc : Tendsto (fun N => conditionalDistance N (L N) (hardCutoff N)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun N => conditionalDistance_nonneg N (L N) _)
    · filter_upwards [eventually_ge_atTop Nzero,hband] with N hN hb
      exact (hzero N hN (L N) hb.1 hb.2).2
    · simpa only [hardRate,mul_zero] using hlim.const_mul 20
  exact ⟨hc, countDistance_tendsto_zero_of_conditional L hardCutoff hc⟩

/-- A positive c*nu margin gives both soft-cutoff and unconditional convergence. -/
theorem soft_convergence_of_margin
    (hStein : ScalarSteinFactorsStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax c : ℝ) (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax) (hc : 0 < c)
    (L : ℕ → ℕ)
    (hband : ∀ᶠ N : ℕ in atTop,
      betaMin * Real.log N ≤ (L N + 1 : ℝ) ∧ (L N + 1 : ℝ) ≤ betaMax * Real.log N)
    (hmargin : ∀ᶠ N : ℕ in atTop,
      max 0 (Real.log (fullRate N (L N) : ℝ)) ≤
        saddleCutoff 2 (Real.log N) - c * saddleNu 2 (Real.log N)) :
    Tendsto (fun N => conditionalDistance N (L N) (softCutoff N)) atTop (𝓝 0) ∧
      Tendsto (fun N => countDistance N (L N)) atTop (𝓝 0) := by
  obtain ⟨Nzero,hzero⟩ := soft_conditional_rate_eventually
    hStein hPNT betaMin betaMax (1 / 6) (c / 4) hbetaMin hbeta (by norm_num) (by positivity)
  have hlim := soft_rate_tendsto_zero_of_margin 2 c (c / 4) (1 / 6)
    (fun N => max 0 (Real.log (fullRate N (L N) : ℝ))) (by norm_num) (by linarith)
    (by norm_num) hmargin
  have hcond : Tendsto (fun N => conditionalDistance N (L N) (softCutoff N)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun N => conditionalDistance_nonneg N (L N) _)
    · filter_upwards [eventually_ge_atTop Nzero,hband] with N hN hb
      exact ((hzero N hN (L N) hb.1 hb.2).2).trans
        (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num))
    · simpa only [softRate,mul_zero] using hlim.const_mul 6
  exact ⟨hcond, countDistance_tendsto_zero_of_conditional L softCutoff hcond⟩

/-- In particular, the old hard endpoint lies strictly inside the new soft convergence regime. -/
theorem soft_convergence_at_hard_endpoint
    (hStein : ScalarSteinFactorsStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax K : ℝ) (hbetaMin : 0 < betaMin) (hbeta : betaMin < betaMax)
    (L : ℕ → ℕ)
    (hband : ∀ᶠ N : ℕ in atTop,
      betaMin * Real.log N ≤ (L N + 1 : ℝ) ∧ (L N + 1 : ℝ) ≤ betaMax * Real.log N)
    (hendpoint : ∀ᶠ N : ℕ in atTop,
      max 0 (Real.log (fullRate N (L N) : ℝ)) ≤ saddleCutoff 1 (Real.log N) + K) :
    Tendsto (fun N => conditionalDistance N (L N) (softCutoff N)) atTop (𝓝 0) ∧
      Tendsto (fun N => countDistance N (L N)) atTop (𝓝 0) := by
  obtain ⟨Nzero,hzero⟩ := hard_endpoint_le_soft_margin_eventually K 1
  apply soft_convergence_of_margin hStein hPNT betaMin betaMax 1 hbetaMin hbeta (by norm_num) L hband
  filter_upwards [eventually_ge_atTop Nzero,hendpoint] with N hN he
  exact hzero N hN _ he

end
end PaperC.V282.PoissonRateConvergence
