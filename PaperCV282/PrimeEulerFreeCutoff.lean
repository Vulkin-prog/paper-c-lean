import PaperCV282.PrimeEulerFreeScales

/-!
# Weighted Euler estimates with a threshold before the free cutoff

The cutoff w is arbitrary throughout each fixed positive band around
sqrt(H log H). The only prime-distribution premise is the ordinary PNT.
The floor(exp w) is retained exactly in both finite prime sums.
-/

namespace PaperC.V282.PrimeEulerFreeCutoff

open Set Filter Topology PrimeEulerPNT PrimeEulerRankin PrimeEulerUniform
open PrimeEulerFreeScales SaddleBranch ExponentialIntegral

noncomputable section

/-- Both genuine Euler errors are uniformly o(H/w) on the broad power band. -/
theorem euler_errors_power_band_of_pnt (hPNT : PrimeNumberTheoremRemainder)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Hzero : ℝ, ∀ H ≥ Hzero, ∀ w : ℝ,
      H ^ (1 / 4 : ℝ) ≤ w → w ≤ H ^ (3 / 4 : ℝ) →
      |rankinPrimeSum ⌊Real.exp w⌋₊ (freeCutoffTilt H w) - exponentialIntegral (upperSaddleBranch (H / w))| ≤
        epsilon * (H / w) ∧
      |rankinLogSum ⌊Real.exp w⌋₊ (freeCutoffTilt H w) - exponentialIntegral (upperSaddleBranch (H / w))| ≤
        epsilon * (H / w) := by
  let P := {p : ℝ × ℝ // p.1 ^ (1 / 4 : ℝ) ≤ p.2 ∧ p.2 ≤ p.1 ^ (3 / 4 : ℝ)}
  let H : P → ℝ := fun p => p.val.1
  let w : P → ℝ := fun p => p.val.2
  let l : Filter P := Filter.comap H atTop
  have hH : Tendsto H l atTop := tendsto_comap
  have hband : ∀ᶠ p in l, H p ^ (1 / 4 : ℝ) ≤ w p ∧ w p ≤ H p ^ (3 / 4 : ℝ) :=
    Eventually.of_forall fun p => p.property
  obtain ⟨hw, hnu, hz, hzpos, hlog⟩ := power_band_scale_conditions hH hband
  have hlink : ∀ᶠ p in l, freeCutoffTilt (H p) (w p) * w p = upperSaddleBranch (H p / w p) := by
    filter_upwards [hw.eventually (eventually_gt_atTop (0 : ℝ))] with p hp
    exact div_mul_cancel₀ _ hp.ne'
  have hprime := weighted_prime_sum_normalized_error_of_pnt hPNT hw hnu hz hzpos hlog hlink
  have heuler := log_euler_normalized_error_of_pnt hPNT hw hnu hz hzpos hlog hlink
  have hpSmall := hprime.abs.eventually (gt_mem_nhds (show |(0 : ℝ)| < epsilon by simpa using hepsilon))
  have heSmall := heuler.abs.eventually (gt_mem_nhds (show |(0 : ℝ)| < epsilon by simpa using hepsilon))
  have hall : ∀ᶠ p in l,
      |rankinPrimeSum ⌊Real.exp (w p)⌋₊ (freeCutoffTilt (H p) (w p)) -
        exponentialIntegral (upperSaddleBranch (H p / w p))| ≤ epsilon * (H p / w p) ∧
      |rankinLogSum ⌊Real.exp (w p)⌋₊ (freeCutoffTilt (H p) (w p)) -
        exponentialIntegral (upperSaddleBranch (H p / w p))| ≤ epsilon * (H p / w p) := by
    filter_upwards [hpSmall, heSmall, hnu.eventually (eventually_gt_atTop (0 : ℝ))] with p hp he hn
    simp only [abs_div, abs_of_pos hn] at hp he
    exact ⟨(div_le_iff₀ hn).mp hp.le, (div_le_iff₀ hn).mp he.le⟩
  obtain ⟨s, hs, hsub⟩ := Filter.mem_comap.1 hall
  obtain ⟨Hzero, hzero⟩ := eventually_atTop.1 hs
  refine ⟨Hzero, ?_⟩
  intro h hh v hlo hhi
  exact hsub (a := (⟨(h, v), hlo, hhi⟩ : P)) (hzero h hh)

/-- Companion B.1's genuinely free cutoff quantifier: the threshold precedes w
throughout every fixed positive square-root band. -/
theorem euler_errors_sqrt_log_band_of_pnt (hPNT : PrimeNumberTheoremRemainder)
    (c C epsilon : ℝ) (hc : 0 < c) (hC : 0 < C) (hepsilon : 0 < epsilon) :
    ∃ Hzero : ℝ, ∀ H ≥ Hzero, ∀ w : ℝ,
      c * Real.sqrt (H * Real.log H) ≤ w →
      w ≤ C * Real.sqrt (H * Real.log H) →
      |rankinPrimeSum ⌊Real.exp w⌋₊ (freeCutoffTilt H w) - exponentialIntegral (upperSaddleBranch (H / w))| ≤
        epsilon * (H / w) ∧
      |rankinLogSum ⌊Real.exp w⌋₊ (freeCutoffTilt H w) - exponentialIntegral (upperSaddleBranch (H / w))| ≤
        epsilon * (H / w) := by
  obtain ⟨Hband, hband⟩ := sqrt_log_band_eventually_in_power_band c C hc hC
  obtain ⟨Heuler, heuler⟩ := euler_errors_power_band_of_pnt hPNT epsilon hepsilon
  refine ⟨max Hband Heuler, ?_⟩
  intro H hH w hlo hhi
  obtain ⟨hpLo, hpHi⟩ := hband H ((le_max_left _ _).trans hH) w hlo hhi
  exact heuler H ((le_max_right _ _).trans hH) w hpLo hpHi

end
end PaperC.V282.PrimeEulerFreeCutoff
