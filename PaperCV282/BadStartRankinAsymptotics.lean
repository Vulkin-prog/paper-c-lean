import PaperCV282.BadStartRankin
import PaperCV282.PrimeEulerSaddle

/-!
# Actual deletion costs at the proved cutoff saddles

From the ordinary PNT premise, the Rankin count and the weighted-prime
calculation give exp(-D(nu)+o(nu)) for actual defective integers and every
masked whole-support bad-start population. The final threshold precedes
the window length and arbitrary mask. No distribution assumption on masks
or conditional bad-site probabilities is used.
-/

namespace PaperC.V282.BadStartRankinAsymptotics

open Set Filter Topology DefectiveRankinCount PrimeEulerRankin PrimeEulerPNT PrimeEulerSaddle
open BadStartRankin MaskedArithmeticGeometry SaddleParameters SaddleScales SaddleBranch ExponentialIntegral

noncomputable section

/-- The finite deletion exponent contains the exact Euler remainder at the genuine saddle. -/
theorem normalized_fullBadMask_le_actual_saddle_remainder
    {a : ℝ} (ha : 0 < a) {N L : ℕ} (hN : 2 ≤ N) (hL : L ≤ N)
    (hH : saddleThreshold a ≤ Real.log N) (mask : Finset ℕ)
    (hzetaHalf : saddleTilt a (Real.log N) ≤ 1 / 2) :
    ((fullBadMask N L ⌊Real.exp (saddleCutoff a (Real.log N))⌋₊ mask).card : ℝ) / N ≤
      Real.exp (-saddleCost (saddleNu a (Real.log N)) + Real.log (3 * (L + 1 : ℝ)) +
        (rankinLogSum ⌊Real.exp (saddleCutoff a (Real.log N))⌋₊ (saddleTilt a (Real.log N)) -
          exponentialIntegral (upperSaddleBranch (saddleNu a (Real.log N))))) := by
  have hfinite := normalized_fullBadMask_le_exp
    (Y := ⌊Real.exp (saddleCutoff a (Real.log N))⌋₊) hN hL mask hzetaHalf
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog3N : Real.log (3 * N : ℕ) = Real.log 3 + Real.log N := by
    push_cast
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hNpos.ne']
  have hmain : saddleTilt a (Real.log N) * Real.log N =
      saddleNu a (Real.log N) * upperSaddleBranch (saddleNu a (Real.log N)) := by
    rw [saddleNu, upperSaddleBranch_div_saddleCutoff ha hH, saddleTilt]
    ring
  have hdiscard : 0 ≤ saddleTilt a (Real.log N) * Real.log 3 :=
    mul_nonneg (saddleTilt_pos ha hH).le (Real.log_nonneg (by norm_num))
  apply hfinite.trans
  apply Real.exp_le_exp.mpr
  rw [hlog3N]
  simp only [mul_add]
  rw [hmain]
  unfold saddleCost
  linarith

/-- The genuine defective-integer population has the Rankin saddle cost, under ordinary PNT. -/
theorem normalized_defectiveValues_saddle_le_eventually
    (hPNT : PrimeNumberTheoremRemainder) {a : ℝ} (ha : 0 < a)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Xzero : ℕ, ∀ X ≥ Xzero,
      ((defectiveValues X ⌊Real.exp (saddleCutoff a (Real.log X))⌋₊).card : ℝ) / X ≤
        Real.exp (-saddleCost (saddleNu a (Real.log X)) + epsilon * saddleNu a (Real.log X)) := by
  have hnatlog : Tendsto (fun X : ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have heuler := (log_euler_saddle_error_of_pnt hPNT ha).comp hnatlog
  have hsmall := heuler.eventually (gt_mem_nhds hepsilon)
  have hhalf := (tendsto_saddleTilt_zero ha).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hevent : ∀ᶠ X : ℕ in atTop,
      ((defectiveValues X ⌊Real.exp (saddleCutoff a (Real.log X))⌋₊).card : ℝ) / X ≤
        Real.exp (-saddleCost (saddleNu a (Real.log X)) + epsilon * saddleNu a (Real.log X)) := by
    filter_upwards [hsmall, hnatlog.eventually hhalf,
      hnatlog.eventually (eventually_ge_atTop (saddleThreshold a)),
      eventually_ge_atTop (1 : ℕ)] with X hsmall hhalf hH hX
    have hXpos : 0 < X := by omega
    have hnupos : 0 < saddleNu a (Real.log X) :=
      (Real.exp_pos 1).trans_le (saddleCutoff_domain ha hH)
    have hupper : rankinLogSum ⌊Real.exp (saddleCutoff a (Real.log X))⌋₊ (saddleTilt a (Real.log X)) -
        exponentialIntegral (upperSaddleBranch (saddleNu a (Real.log X))) ≤
        epsilon * saddleNu a (Real.log X) := by
      exact (div_le_iff₀ hnupos).mp hsmall.le
    have hfinite := normalized_defectiveValues_le_exp_logSum hXpos
      ⌊Real.exp (saddleCutoff a (Real.log X))⌋₊ hhalf.le
    have hmain : saddleTilt a (Real.log X) * Real.log X =
        saddleNu a (Real.log X) * upperSaddleBranch (saddleNu a (Real.log X)) := by
      rw [saddleNu, upperSaddleBranch_div_saddleCutoff ha hH, saddleTilt]
      ring
    apply hfinite.trans
    apply Real.exp_le_exp.mpr
    unfold saddleCost
    linarith
  exact eventually_atTop.1 hevent

/-- Under ordinary PNT, every whole-support bad mask has exp(-D(nu)+o(nu)) ambient cost.
The chosen window and mask come after the threshold; only the logarithmic upper band is needed. -/
theorem normalized_fullBadMask_saddle_le_eventually
    (hPNT : PrimeNumberTheoremRemainder) {a : ℝ} (ha : 0 < a)
    (betaMax epsilon : ℝ) (hbeta : 0 < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      (L + 1 : ℝ) ≤ betaMax * Real.log N → ∀ mask : Finset ℕ,
      ((fullBadMask N L ⌊Real.exp (saddleCutoff a (Real.log N))⌋₊ mask).card : ℝ) / N ≤
        Real.exp (-saddleCost (saddleNu a (Real.log N)) + epsilon * saddleNu a (Real.log N)) := by
  have hnatlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have heuler := (log_euler_saddle_error_of_pnt hPNT ha).comp hnatlog
  have hsmall := heuler.eventually (gt_mem_nhds (show (0 : ℝ) < epsilon / 2 by positivity))
  have hhalf := (tendsto_saddleTilt_zero ha).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hfactor : Tendsto (fun H => (Real.log (3 * betaMax) + Real.log H) / saddleNu a H)
      atTop (𝓝 0) := by
    simpa only [add_div, add_zero] using
      ((tendsto_const_nhds (x := Real.log (3 * betaMax))).div_atTop (tendsto_saddleNu_atTop ha)).add
        (tendsto_log_div_saddleNu ha)
  have hfactorSmall := (hfactor.comp hnatlog).eventually
    (gt_mem_nhds (show (0 : ℝ) < epsilon / 2 by positivity))
  have hlength : ∀ᶠ H : ℝ in atTop, betaMax * H ≤ Real.exp H := by
    filter_upwards [(Real.tendsto_exp_div_pow_atTop 1).eventually (eventually_ge_atTop betaMax),
      eventually_gt_atTop (0 : ℝ)] with H hratio hH
    simp only [pow_one] at hratio
    exact (le_div_iff₀ hH).mp hratio
  have hevent : ∀ᶠ N : ℕ in atTop, ∀ L : ℕ,
      (L + 1 : ℝ) ≤ betaMax * Real.log N → ∀ mask : Finset ℕ,
      ((fullBadMask N L ⌊Real.exp (saddleCutoff a (Real.log N))⌋₊ mask).card : ℝ) / N ≤
        Real.exp (-saddleCost (saddleNu a (Real.log N)) + epsilon * saddleNu a (Real.log N)) := by
    filter_upwards [hsmall, hfactorSmall, hnatlog.eventually hhalf, hnatlog.eventually hlength,
      hnatlog.eventually (eventually_ge_atTop (saddleThreshold a)),
      hnatlog.eventually (eventually_gt_atTop (0 : ℝ)), eventually_ge_atTop (2 : ℕ)]
      with N hsmall hfactorSmall hhalf hlength hH hlogN hN
    intro L hL mask
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hLN : L ≤ N := by
      rw [Real.exp_log hNpos] at hlength
      have hh := hL.trans hlength
      have hh' : (L : ℝ) ≤ N := by linarith
      exact_mod_cast hh'
    have hnupos : 0 < saddleNu a (Real.log N) :=
      (Real.exp_pos 1).trans_le (saddleCutoff_domain ha hH)
    have he : rankinLogSum ⌊Real.exp (saddleCutoff a (Real.log N))⌋₊ (saddleTilt a (Real.log N)) -
        exponentialIntegral (upperSaddleBranch (saddleNu a (Real.log N))) ≤
        (epsilon / 2) * saddleNu a (Real.log N) :=
      (div_le_iff₀ hnupos).mp hsmall.le
    have hf : Real.log (3 * betaMax) + Real.log (Real.log N) ≤
        (epsilon / 2) * saddleNu a (Real.log N) :=
      (div_le_iff₀ hnupos).mp hfactorSmall.le
    have hlogB : Real.log (3 * (L + 1 : ℝ)) ≤ Real.log (3 * betaMax) + Real.log (Real.log N) := by
      rw [← Real.log_mul (by positivity : (3 * betaMax : ℝ) ≠ 0) hlogN.ne']
      apply Real.log_le_log (by positivity)
      nlinarith
    apply (normalized_fullBadMask_le_actual_saddle_remainder ha hN hLN hH mask hhalf.le).trans
    apply Real.exp_le_exp.mpr
    linarith
  exact eventually_atTop.1 hevent

end
end PaperC.V282.BadStartRankinAsymptotics
