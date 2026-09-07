import PaperCV282.PrimeEulerPNT
import PaperCV282.ExponentialIntegralAsymptotics
import PaperC.Arithmetic.PrimeNumberTheoremInput
import PaperC.Asymptotics.PrefixBoundaryProbability

/-! # Prime counting from the already declared PNT remainder

The normalization by Ei(log x) and the sequential prime-number theorem
are connected by the proved expansion of Ei. No second PNT is assumed.
-/
namespace PaperC.V282.PostQuadraticPrimeBounds

open Filter ExponentialIntegral ExponentialIntegralAsymptotics PrimeEulerPNT
open PrimeEulerAbel
open scoped Topology

noncomputable section

/-- The normalized exponential integral tends to one. -/
theorem exponentialIntegral_normalized_tendsto_one :
    Tendsto (fun u : ℝ => exponentialIntegral u * u / Real.exp u) atTop (𝓝 1) := by
  have hbound : ∀ᶠ u : ℝ in atTop,
      |exponentialIntegral u * u / Real.exp u - 1| ≤ 5 / u ^ 2 + 1 / u := by
    filter_upwards [exponentialIntegralRemainder_bound_eventually,
      eventually_ge_atTop (1 : ℝ)] with u hu huone
    have hup : 0 < u := by linarith
    have hep := Real.exp_pos u
    have heq : exponentialIntegral u * u / Real.exp u - 1 =
        exponentialIntegralRemainder u * (u / Real.exp u) + 1 / u := by
      unfold exponentialIntegralRemainder
      field_simp
      ring
    rw [heq]
    calc
      _ ≤ |exponentialIntegralRemainder u| * (u / Real.exp u) + 1 / u := by
        simpa only [abs_mul, abs_of_pos (div_pos hup hep), abs_of_pos (one_div_pos.mpr hup)]
          using abs_add_le (exponentialIntegralRemainder u * (u / Real.exp u)) (1 / u)
      _ ≤ (5 * (Real.exp u / u ^ 3)) * (u / Real.exp u) + 1 / u :=
        add_le_add (mul_le_mul_of_nonneg_right hu (div_nonneg hup.le hep.le)) le_rfl
      _ = _ := by field_simp
  have hi : Tendsto (fun u : ℝ => 1 / u) atTop (𝓝 0) := by simpa only [one_div] using tendsto_inv_atTop_zero
  have henv : Tendsto (fun u : ℝ => 5 / u ^ 2 + 1 / u) atTop (𝓝 0) := by
    have h := (hi.pow 2).const_mul 5 |>.add hi
    simpa [div_eq_mul_inv, inv_pow] using h
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using squeeze_zero'
    (Eventually.of_forall fun u => abs_nonneg (exponentialIntegral u * u / Real.exp u - 1))
    hbound henv

/-- The existing remainder hypothesis gives a vanishing normalized prime error. -/
theorem normalized_prime_remainder_tendsto_zero (hPNT : PrimeNumberTheoremRemainder) :
    Tendsto (fun n : ℕ => primeCountingRemainder n * Real.log n / n) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro epsilon hepsilon
  obtain ⟨A, _hA, hrem⟩ := hPNT (epsilon / 2) (by positivity)
  obtain ⟨Nzero, hNzero⟩ := exists_nat_gt (max A 2)
  refine ⟨Nzero, ?_⟩
  intro n hn
  have hnreal : max A 2 < (n : ℝ) := hNzero.trans_le (by exact_mod_cast hn)
  have hnp : 0 < (n : ℝ) := by have := le_max_right A 2; linarith
  have hnlog : 0 < Real.log (n : ℝ) := Real.log_pos (by have := le_max_right A 2; linarith)
  have hb := hrem n ((le_max_left A 2).trans hnreal.le)
  have hnormalized : |primeCountingRemainder n * Real.log n / n| ≤ epsilon / 2 := by
    rw [abs_div, abs_mul, abs_of_pos hnlog, abs_of_pos hnp]
    calc
      _ ≤ (epsilon / 2 * (n : ℝ) / Real.log n) * Real.log n / n :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hb hnlog.le) hnp.le
      _ = _ := by field_simp
  simpa only [Real.dist_eq, sub_zero] using hnormalized.trans_lt (by linarith)

/-- The exact library prime-count normalization implied by the existing PNT. -/
theorem primeCounting_normalized_tendsto_one (hPNT : PrimeNumberTheoremRemainder) :
    Tendsto (fun n : ℕ => (Nat.primeCounting n : ℝ) * Real.log n / n) atTop (𝓝 1) := by
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hEi := exponentialIntegral_normalized_tendsto_one.comp hlog
  have hE : Tendsto (fun n : ℕ => logIntegral n * Real.log n / n) atTop (𝓝 1) := by
    apply hEi.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [Function.comp_apply, logIntegral, Real.exp_log (by positivity : 0 < (n : ℝ))]
  have hs := (normalized_prime_remainder_tendsto_zero hPNT).add hE
  convert hs using 1
  · ext n
    simp only [primeCountingRemainder, primeCountingReal, Nat.floor_natCast]
    ring
  · norm_num

/-- Inclusive prime counts in the historical and library models agree. -/
theorem prime_count_eq_nat (n : ℕ) : PrimesUpTo.count n = Nat.primeCounting n := by
  exact PrefixBoundaryProbability.card_primeUpTo_eq_primeCounting n

/-- The old sequential PNT is derived, not added as a new premise. -/
theorem primeNumberTheorem_of_remainder (hPNT : PrimeNumberTheoremRemainder) :
    PrimeNumberTheoremInput.PrimeNumberTheoremStatement := by
  simpa only [PrimeNumberTheoremInput.PrimeNumberTheoremStatement, prime_count_eq_nat]
    using primeCounting_normalized_tendsto_one hPNT

end
end PaperC.V282.PostQuadraticPrimeBounds
