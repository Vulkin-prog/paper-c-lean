import PaperCV282.TransitionPrimeScales

/-! # Absorbing the microscopic number of sites into a prime-scale margin

The at most 2L^2 interior starts cost only a vanishing fraction of pi(L)
in the exponent. The loss is quantified before summing their probabilities.
-/

namespace PaperC.V282.MicroscopicExponentialScale

open Filter TransitionPrimeScales MediumIncidenceAsymptotics PostQuadraticPrimeBounds
open PrimeEulerPNT
open scoped Topology

noncomputable section

/-- Logarithmic site-count costs are negligible relative to the prime count. -/
theorem log_over_prime_count_tendsto_zero (hPNT : PrimeNumberTheoremRemainder) :
    Tendsto (fun L : ℕ => Real.log L / Nat.primeCounting L) atTop (𝓝 0) := by
  have hsmall : Tendsto (fun L : ℕ => Real.log L / Real.sqrt L) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow,Function.comp_def] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero.comp
        tendsto_natCast_atTop_atTop
  have hbound : ∀ᶠ L : ℕ in atTop,
      Real.log L / Nat.primeCounting L ≤ (2 * Real.sqrt L + 3) / Nat.primeCounting L := by
    filter_upwards [hsmall.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      eventually_ge_atTop (1 : ℕ)] with L hs hL
    have hLp : (0 : ℝ) < L := by exact_mod_cast hL
    have hroot : 0 < Real.sqrt (L : ℝ) := Real.sqrt_pos.mpr hLp
    have hlog : Real.log L < Real.sqrt L := (div_lt_one hroot).mp hs
    exact div_le_div_of_nonneg_right (by linarith [Real.sqrt_nonneg (L : ℝ)]) (by positivity)
  apply squeeze_zero' _ hbound (sqrt_cutoff_over_prime_count hPNT)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with L hL
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hL)) (by positivity)

/-- The logarithm of the full 2L^2 prefactor has zero prime-normalized limit. -/
theorem site_cost_ratio_tendsto_zero (hPNT : PrimeNumberTheoremRemainder) :
    Tendsto (fun L : ℕ => (Real.log 2 + 2 * Real.log L) / Nat.primeCounting L)
      atTop (𝓝 0) := by
  have hc : Tendsto (fun L : ℕ => Real.log 2 / (Nat.primeCounting L : ℝ)) atTop (𝓝 0) := by
    simpa only [prime_count_eq_nat] using
      (tendsto_const_nhds (x := Real.log 2)).div_atTop prime_count_tendsto_atTop
  simpa only [add_div,mul_div_assoc,mul_zero,add_zero] using
    hc.add ((log_over_prime_count_tendsto_zero hPNT).const_mul 2)

/-- Every positive fixed prime-scale margin absorbs all microscopic sites. -/
theorem microscopic_prefactor_le_eventually (hPNT : PrimeNumberTheoremRemainder)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ L : ℕ in atTop, 2 * (L : ℝ) ^ 2 ≤ (2 : ℝ) ^ (epsilon * Nat.primeCounting L) := by
  have hlogtwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hbound := (site_cost_ratio_tendsto_zero hPNT).eventually
    (gt_mem_nhds (mul_pos hepsilon hlogtwo))
  have hpos : ∀ᶠ L : ℕ in atTop, (0 : ℝ) < Nat.primeCounting L := by
    simpa only [prime_count_eq_nat] using prime_count_tendsto_atTop.eventually_gt_atTop 0
  filter_upwards [hbound,hpos,eventually_ge_atTop (1 : ℕ)] with L hL hp hLone
  have hLp : (0 : ℝ) < L := by exact_mod_cast hLone
  have hx := (div_lt_iff₀ hp).mp hL
  have hcost : Real.log (2 * (L : ℝ) ^ 2) ≤ Real.log 2 * (epsilon * Nat.primeCounting L) := by
    rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith
  have he := Real.exp_le_exp.mpr hcost
  rwa [Real.exp_log (by positivity),← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)] at he

/-- Decay on any positive prime scale tends to zero. -/
theorem prime_exponential_tendsto_zero {delta : ℝ} (hdelta : 0 < delta) :
    Tendsto (fun L : ℕ => (2 : ℝ) ^ (-delta * Nat.primeCounting L)) atTop (𝓝 0) := by
  have hneg := tendsto_neg_atTop_atBot.comp
    (prime_count_tendsto_atTop.const_mul_atTop hdelta)
  have he := Real.tendsto_exp_atBot.comp
    (hneg.const_mul_atBot (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
  simpa only [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),Function.comp_def,
    prime_count_eq_nat,neg_mul] using he

end
end PaperC.V282.MicroscopicExponentialScale
