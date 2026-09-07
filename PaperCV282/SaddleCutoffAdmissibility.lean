import PaperCV282.PrimeEulerSaddle
import PaperC.Model.FiniteRademacher

/-!
# Admissibility of the literal integer cutoffs at either saddle

For every fixed a>0, the cutoff lies above every logarithmic window and
below the event cylinder. The natural-number threshold precedes the window.
All statements use the actual implicitly defined saddle, without PNT.
-/

namespace PaperC.V282.SaddleCutoffAdmissibility

open Set Filter Topology SaddleParameters SaddleScales SaddleAsymptotics SaddleExpansion
open PrimeEulerSaddle

noncomputable section

/-- The prime cutoff exponent grows faster than log H. -/
theorem tendsto_log_div_saddleCutoff {a : ℝ} (ha : 0 < a) :
    Tendsto (fun H => Real.log H / saddleCutoff a H) atTop (𝓝 0) := by
  apply (show Tendsto (fun H =>
    (Real.log H / saddleParameter a H) * saddleTilt a H) atTop (𝓝 0) by
      simpa only [mul_zero] using (tendsto_log_div_saddleParameter ha).mul (tendsto_saddleTilt_zero ha)).congr'
  filter_upwards [eventually_ge_atTop (saddleThreshold a)] with H hH
  have hu : saddleParameter a H ≠ 0 := by
    linarith [(saddleParameter_spec ha hH).1, saddleParameterBase_ge_two]
  unfold saddleTilt
  field_simp [hu]

/-- Equivalent growth form, available before composing H=log N. -/
theorem tendsto_saddleCutoff_div_log {a : ℝ} (ha : 0 < a) :
    Tendsto (fun H => saddleCutoff a H / Real.log H) atTop atTop := by
  have hpos : ∀ᶠ H : ℝ in atTop, 0 < Real.log H / saddleCutoff a H := by
    filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_ge_atTop (saddleThreshold a)] with H hH hth
    exact div_pos (Real.log_pos hH) (saddleCutoff_pos ha hth)
  have hgt : Tendsto (fun H => Real.log H / saddleCutoff a H) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_log_div_saddleCutoff ha, hpos⟩
  apply hgt.inv_tendsto_nhdsGT_zero.congr
  intro H
  change (Real.log H / saddleCutoff a H)⁻¹ = _
  rw [inv_div]

/-- The cutoff exponent is o(H), so its exponential is eventually below exp H. -/
theorem tendsto_saddleCutoff_div_height {a : ℝ} (ha : 0 < a) :
    Tendsto (fun H => saddleCutoff a H / H) atTop (𝓝 0) := by
  apply (tendsto_saddleNu_atTop ha).inv_tendsto_atTop.congr
  intro H
  change (H / saddleCutoff a H)⁻¹ = _
  rw [inv_div]

/-- Every actual saddle lies in a fixed positive square-root band. -/
theorem saddleCutoff_sqrt_log_band_eventually {a : ℝ} (ha : 0 < a) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ Hzero : ℝ, ∀ H ≥ Hzero,
      c * Real.sqrt (H * Real.log H) ≤ saddleCutoff a H ∧
      saddleCutoff a H ≤ C * Real.sqrt (H * Real.log H) := by
  let s := Real.sqrt (a / 2)
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have h := tendsto_saddleCutoff_normalized ha
  have hl := h.eventually (lt_mem_nhds (show s / 2 < Real.sqrt (a / 2) by dsimp [s] at *; linarith))
  have hu := h.eventually (gt_mem_nhds (show Real.sqrt (a / 2) < 2 * s by dsimp [s] at *; linarith))
  have hevent : ∀ᶠ H : ℝ in atTop,
      (s / 2) * Real.sqrt (H * Real.log H) ≤ saddleCutoff a H ∧
      saddleCutoff a H ≤ (2 * s) * Real.sqrt (H * Real.log H) := by
    filter_upwards [hl, hu, eventually_gt_atTop (1 : ℝ)] with H hlo hhi hH
    have hroot : 0 < Real.sqrt (H * Real.log H) := Real.sqrt_pos.mpr (mul_pos (by linarith) (Real.log_pos hH))
    exact ⟨(le_div_iff₀ hroot).mp hlo.le, (div_le_iff₀ hroot).mp hhi.le⟩
  exact ⟨s / 2, 2 * s, by positivity, by positivity, eventually_atTop.1 hevent⟩

/-- The actual rounded saddle cutoff is admissible uniformly before every logarithmic window. -/
theorem saddleCutoff_nat_admissible_eventually (a betaMax : ℝ)
    (ha : 0 < a) (hbeta : 0 < betaMax) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      (L + 1 : ℝ) ≤ betaMax * Real.log N →
      saddleThreshold a ≤ Real.log N ∧ 0 < saddleCutoff a (Real.log N) ∧
      2 * L ≤ ⌊Real.exp (saddleCutoff a (Real.log N))⌋₊ ∧
      ⌊Real.exp (saddleCutoff a (Real.log N))⌋₊ ≤ dyadicCutoff N L := by
  have hcost : Tendsto (fun H => (|Real.log (2 * betaMax)| + Real.log H) / saddleCutoff a H)
      atTop (𝓝 0) := by
    simpa only [add_div, add_zero] using
      ((tendsto_const_nhds (x := |Real.log (2 * betaMax)|)).div_atTop (tendsto_saddleCutoff_atTop ha)).add
        (tendsto_log_div_saddleCutoff ha)
  have hupper := (tendsto_saddleCutoff_div_height ha).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hlower := hcost.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hnatlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ N : ℕ in atTop, ∀ L : ℕ,
      (L + 1 : ℝ) ≤ betaMax * Real.log N →
      saddleThreshold a ≤ Real.log N ∧ 0 < saddleCutoff a (Real.log N) ∧
      2 * L ≤ ⌊Real.exp (saddleCutoff a (Real.log N))⌋₊ ∧
      ⌊Real.exp (saddleCutoff a (Real.log N))⌋₊ ≤ dyadicCutoff N L := by
    filter_upwards [hnatlog.eventually hupper, hnatlog.eventually hlower,
      hnatlog.eventually (eventually_ge_atTop (saddleThreshold a)),
      hnatlog.eventually (eventually_gt_atTop (0 : ℝ)), eventually_ge_atTop (1 : ℕ)]
      with N hupper hlower hH hlogN hN
    intro L hL
    have hw := saddleCutoff_pos ha hH
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hwH : saddleCutoff a (Real.log N) ≤ Real.log N := by
      simpa only [one_mul] using (div_le_iff₀ hlogN).mp hupper.le
    have hlogle : Real.log (2 * betaMax) + Real.log (Real.log N) ≤ saddleCutoff a (Real.log N) := by
      have hh := (div_le_iff₀ hw).mp hlower.le
      linarith [le_abs_self (Real.log (2 * betaMax))]
    have hsmall : 2 * betaMax * Real.log N ≤ Real.exp (saddleCutoff a (Real.log N)) := by
      have hh := Real.exp_le_exp.mpr hlogle
      simpa only [Real.exp_add, Real.exp_log (mul_pos (by norm_num : (0 : ℝ) < 2) hbeta),
        Real.exp_log hlogN] using hh
    have htwoL : 2 * L ≤ ⌊Real.exp (saddleCutoff a (Real.log N))⌋₊ := by
      apply (Nat.le_floor_iff (Real.exp_nonneg _)).mpr
      push_cast
      nlinarith
    have hfloor : (⌊Real.exp (saddleCutoff a (Real.log N))⌋₊ : ℝ) ≤ N :=
      (Nat.floor_le (Real.exp_nonneg _)).trans (by simpa only [Real.exp_log hNpos] using Real.exp_le_exp.mpr hwH)
    have hfloorNat : ⌊Real.exp (saddleCutoff a (Real.log N))⌋₊ ≤ N := by exact_mod_cast hfloor
    refine ⟨hH, hw, htwoL, ?_⟩
    unfold dyadicCutoff
    omega
  exact eventually_atTop.1 hevent

end
end PaperC.V282.SaddleCutoffAdmissibility
