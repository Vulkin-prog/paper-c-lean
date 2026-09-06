import PaperCV282.BadStartRankin
import PaperCV282.PrimeEulerFreeCutoff
import PaperCV282.SaddleParameters

/-!
# Rankin deletion bounds on the full free-cutoff band

The fixed band constants precede the threshold. Then the cutoff w, the
window length and an arbitrary deterministic mask can all be chosen freely.
Only the ordinary PNT remainder is a premise; all actual counts and Euler
weights are derived from it. The complete support includes the left root.
-/

namespace PaperC.V282.BadStartRankinFreeCutoff

open Set Filter Topology PrimeEulerPNT PrimeEulerRankin PrimeEulerFreeScales PrimeEulerFreeCutoff
open BadStartRankin DefectiveRankinCount MaskedArithmeticGeometry SaddleParameters SaddleBranch ExponentialIntegral

noncomputable section

/-- A finite whole-support mask bound at any genuine positive free cutoff. -/
theorem normalized_fullBadMask_le_free_remainder
    {N L : ℕ} (hN : 2 ≤ N) (hL : L ≤ N) (mask : Finset ℕ)
    {w : ℝ} (hw : 0 < w) (hnu : Real.exp 1 ≤ Real.log N / w)
    (hzetaHalf : freeCutoffTilt (Real.log N) w ≤ 1 / 2) :
    ((fullBadMask N L ⌊Real.exp w⌋₊ mask).card : ℝ) / N ≤
      Real.exp (-saddleCost (Real.log N / w) + Real.log (3 * (L + 1 : ℝ)) +
        (rankinLogSum ⌊Real.exp w⌋₊ (freeCutoffTilt (Real.log N) w) -
          exponentialIntegral (upperSaddleBranch (Real.log N / w)))) := by
  have hfinite := normalized_fullBadMask_le_exp (Y := ⌊Real.exp w⌋₊) hN hL mask hzetaHalf
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog3N : Real.log (3 * N : ℕ) = Real.log 3 + Real.log N := by
    push_cast
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hNpos.ne']
  have hmain : freeCutoffTilt (Real.log N) w * Real.log N =
      (Real.log N / w) * upperSaddleBranch (Real.log N / w) := by unfold freeCutoffTilt; ring
  have hdiscard : 0 ≤ freeCutoffTilt (Real.log N) w * Real.log 3 :=
    mul_nonneg (div_pos (upperSaddleBranch_pos hnu) hw).le (Real.log_nonneg (by norm_num))
  apply hfinite.trans
  apply Real.exp_le_exp.mpr
  rw [hlog3N]
  simp only [mul_add]
  rw [hmain]
  unfold saddleCost
  linarith

/-- Companion B.1 for actual defective integers, uniformly before the free cutoff. -/
theorem normalized_defectiveValues_free_cutoff_le_eventually
    (hPNT : PrimeNumberTheoremRemainder)
    (c C epsilon : ℝ) (hc : 0 < c) (hC : 0 < C) (hepsilon : 0 < epsilon) :
    ∃ Xzero : ℕ, ∀ X ≥ Xzero, ∀ w : ℝ,
      c * Real.sqrt (Real.log X * Real.log (Real.log X)) ≤ w →
      w ≤ C * Real.sqrt (Real.log X * Real.log (Real.log X)) →
      ((defectiveValues X ⌊Real.exp w⌋₊).card : ℝ) / X ≤
        Real.exp (-saddleCost (Real.log X / w) + epsilon * (Real.log X / w)) := by
  obtain ⟨Hband, hband⟩ := sqrt_log_band_eventually_in_power_band c C hc hC
  obtain ⟨Hdomain, hdomain⟩ := power_band_eventually_rankin_domain
  obtain ⟨Heuler, heuler⟩ := euler_errors_power_band_of_pnt hPNT epsilon hepsilon
  have hnatlog : Tendsto (fun X : ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Xzero, hzero⟩ := eventually_atTop.1
    (hnatlog.eventually (eventually_ge_atTop (max Hband (max Hdomain Heuler))))
  refine ⟨max Xzero 1, ?_⟩
  intro X hX w hlo hhi
  have hH := hzero X (by omega)
  obtain ⟨hpLo, hpHi⟩ := hband (Real.log X) (by order) w hlo hhi
  obtain ⟨_, _, _, _, _, hhalf⟩ := hdomain (Real.log X) (by order) w hpLo hpHi
  have he := (heuler (Real.log X) (by order) w hpLo hpHi).2
  have hfinite := normalized_defectiveValues_le_exp_logSum (show 0 < X by omega) ⌊Real.exp w⌋₊ hhalf
  have hmain : freeCutoffTilt (Real.log X) w * Real.log X =
      (Real.log X / w) * upperSaddleBranch (Real.log X / w) := by unfold freeCutoffTilt; ring
  apply hfinite.trans
  apply Real.exp_le_exp.mpr
  unfold saddleCost
  linarith [le_abs_self (rankinLogSum ⌊Real.exp w⌋₊ (freeCutoffTilt (Real.log X) w) -
    exponentialIntegral (upperSaddleBranch (Real.log X / w)))]

/-- Uniform ambient deletion cost for every actual full-support bad mask.
The threshold precedes w, L and the mask throughout the manuscript's entire free band. -/
theorem normalized_fullBadMask_free_cutoff_le_eventually
    (hPNT : PrimeNumberTheoremRemainder)
    (c C betaMax epsilon : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hbeta : 0 < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ w : ℝ,
      c * Real.sqrt (Real.log N * Real.log (Real.log N)) ≤ w →
      w ≤ C * Real.sqrt (Real.log N * Real.log (Real.log N)) →
      ∀ L : ℕ, (L + 1 : ℝ) ≤ betaMax * Real.log N → ∀ mask : Finset ℕ,
      ((fullBadMask N L ⌊Real.exp w⌋₊ mask).card : ℝ) / N ≤
        Real.exp (-saddleCost (Real.log N / w) + epsilon * (Real.log N / w)) := by
  obtain ⟨Hband, hband⟩ := sqrt_log_band_eventually_in_power_band c C hc hC
  obtain ⟨Hdomain, hdomain⟩ := power_band_eventually_rankin_domain
  obtain ⟨Heuler, heuler⟩ := euler_errors_power_band_of_pnt hPNT (epsilon / 2) (by positivity)
  have hfactor : Tendsto (fun H : ℝ => (|Real.log (3 * betaMax)| + Real.log H) / H ^ (1 / 4 : ℝ))
      atTop (𝓝 0) := by
    simpa only [add_div, add_zero] using
      ((tendsto_const_nhds (x := |Real.log (3 * betaMax)|)).div_atTop
        (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4))).add
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).tendsto_div_nhds_zero
  obtain ⟨Hfactor, hfactor⟩ := eventually_atTop.1
    (hfactor.eventually (gt_mem_nhds (show (0 : ℝ) < epsilon / 2 by positivity)))
  have hlength : ∀ᶠ H : ℝ in atTop, betaMax * H ≤ Real.exp H := by
    filter_upwards [(Real.tendsto_exp_div_pow_atTop 1).eventually (eventually_ge_atTop betaMax),
      eventually_gt_atTop (0 : ℝ)] with H hratio hH
    simp only [pow_one] at hratio
    exact (le_div_iff₀ hH).mp hratio
  obtain ⟨Hlength, hlength⟩ := eventually_atTop.1 hlength
  have hnatlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Nzero, hzero⟩ := eventually_atTop.1
    (hnatlog.eventually (eventually_ge_atTop (max Hband (max Hdomain (max Heuler (max Hfactor Hlength))))))
  refine ⟨max Nzero 2, ?_⟩
  intro N hN w hlo hhi L hL mask
  have hH := hzero N (by omega)
  obtain ⟨hpLo, hpHi⟩ := hband (Real.log N) (by order) w hlo hhi
  obtain ⟨hHone, hw, _, hnu, _, hhalf⟩ := hdomain (Real.log N) (by order) w hpLo hpHi
  have hb := power_band_bounds hHone hpLo hpHi
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hHpos : 0 < Real.log N := by linarith
  have hnupos : 0 < Real.log N / w := (Real.exp_pos 1).trans_le hnu
  have hLN : L ≤ N := by
    have hlen := hlength (Real.log N) (by order)
    rw [Real.exp_log hNpos] at hlen
    have hh := hL.trans hlen
    have hh' : (L : ℝ) ≤ N := by linarith
    exact_mod_cast hh'
  have he := (heuler (Real.log N) (by order) w hpLo hpHi).2
  have hf := hfactor (Real.log N) (by order)
  have hlogB : Real.log (3 * (L + 1 : ℝ)) ≤ |Real.log (3 * betaMax)| + Real.log (Real.log N) := by
    have hh : Real.log (3 * (L + 1 : ℝ)) ≤ Real.log (3 * betaMax) + Real.log (Real.log N) := by
      rw [← Real.log_mul (by positivity : (3 * betaMax : ℝ) ≠ 0) hHpos.ne']
      apply Real.log_le_log (by positivity)
      nlinarith
    linarith [le_abs_self (Real.log (3 * betaMax))]
  have hpref : Real.log (3 * (L + 1 : ℝ)) ≤ (epsilon / 2) * (Real.log N / w) := by
    have hupper : (|Real.log (3 * betaMax)| + Real.log (Real.log N)) / (Real.log N / w) ≤
        (|Real.log (3 * betaMax)| + Real.log (Real.log N)) / (Real.log N) ^ (1 / 4 : ℝ) :=
      div_le_div_of_nonneg_left (add_nonneg (abs_nonneg _) (Real.log_nonneg hHone))
        (Real.rpow_pos_of_pos hHpos _) hb.2.2.2.1
    exact hlogB.trans ((div_le_iff₀ hnupos).mp (hupper.trans hf.le))
  apply (normalized_fullBadMask_le_free_remainder (by omega) hLN mask hw hnu hhalf).trans
  apply Real.exp_le_exp.mpr
  linarith [le_abs_self (rankinLogSum ⌊Real.exp w⌋₊ (freeCutoffTilt (Real.log N) w) -
    exponentialIntegral (upperSaddleBranch (Real.log N / w)))]

end
end PaperC.V282.BadStartRankinFreeCutoff
