import PaperCV282.PrimeEulerFreeScales
import PaperC.Model.FiniteRademacher

/-!
# Every cutoff in the free band observes the whole small-prime field

The lower edge of the band dominates logarithmic window lengths after
exponentiation; the upper edge stays below N. All thresholds precede the
moving real cutoff and the natural run length.
-/

namespace PaperC.V282.FreeCutoffAdmissibility

open Set Filter Topology PrimeEulerFreeScales

noncomputable section

/-- The literal rounded free cutoff is adequate for every window in the fixed band. -/
theorem free_cutoff_admissible_eventually (c C betaMax : ℝ)
    (hc : 0 < c) (hC : 0 < C) (hbeta : 0 < betaMax) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ w : ℝ,
      c * Real.sqrt (Real.log N * Real.log (Real.log N)) ≤ w →
      w ≤ C * Real.sqrt (Real.log N * Real.log (Real.log N)) →
      ∀ L : ℕ, (L + 1 : ℝ) ≤ betaMax * Real.log N →
      0 < w ∧ 2 * L ≤ ⌊Real.exp w⌋₊ ∧ ⌊Real.exp w⌋₊ ≤ dyadicCutoff N L := by
  obtain ⟨Hband,hband⟩ := sqrt_log_band_eventually_in_power_band c C hc hC
  have hfactor : Tendsto (fun H : ℝ =>
      (|Real.log (2 * betaMax)| + Real.log H) / H ^ (1 / 4 : ℝ)) atTop (𝓝 0) := by
    simpa only [add_div, add_zero] using
      ((tendsto_const_nhds (x := |Real.log (2 * betaMax)|)).div_atTop
        (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4))).add
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).tendsto_div_nhds_zero
  obtain ⟨Hfactor,hfactor⟩ := eventually_atTop.1
    (hfactor.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  have hnatlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Nzero,hzero⟩ := eventually_atTop.1
    (hnatlog.eventually (eventually_ge_atTop (max Hband (max Hfactor 1))))
  refine ⟨max Nzero 2, ?_⟩
  intro N hN w hlo hhi L hL
  have hh := hzero N (by omega)
  have hH : 1 ≤ Real.log N := by order
  have hHpos : 0 < Real.log N := by linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨hpLo,hpHi⟩ := hband (Real.log N) (by order) w hlo hhi
  obtain ⟨hw,_,hwH,_,_⟩ := power_band_bounds hH hpLo hpHi
  have hlogle : Real.log (2 * betaMax) + Real.log (Real.log N) ≤ w := by
    have hf := (div_le_iff₀ (Real.rpow_pos_of_pos hHpos (1 / 4 : ℝ))).mp
      (hfactor (Real.log N) (by order)).le
    linarith [le_abs_self (Real.log (2 * betaMax))]
  have hlow : 2 * betaMax * Real.log N ≤ Real.exp w := by
    have he := Real.exp_le_exp.mpr hlogle
    simpa only [Real.exp_add, Real.exp_log (mul_pos (by norm_num : (0 : ℝ) < 2) hbeta),
      Real.exp_log hHpos] using he
  have hfloor : ⌊Real.exp w⌋₊ ≤ N := by
    have hh := (Nat.floor_le (Real.exp_nonneg w)).trans
      (by simpa only [Real.exp_log hNpos] using Real.exp_le_exp.mpr hwH)
    exact_mod_cast hh
  refine ⟨hw, ?_, ?_⟩
  · apply (Nat.le_floor_iff (Real.exp_nonneg w)).mpr
    push_cast
    nlinarith
  · unfold dyadicCutoff
    omega

end
end PaperC.V282.FreeCutoffAdmissibility
