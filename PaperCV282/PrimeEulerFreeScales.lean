import PaperCV282.PrimeEulerUniform
import PaperCV282.SaddleBranchAsymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Scalar estimates uniformly across a free cutoff band

No saddle equation is imposed. A broad polynomial band already forces all
scale hypotheses needed by weighted partial summation. It will contain every
fixed compact positive band around sqrt(H log H).
-/

namespace PaperC.V282.PrimeEulerFreeScales

open Set Filter Topology SaddleBranch SaddleBranchAsymptotics

noncomputable section

def freeCutoffTilt (H w : ℝ) : ℝ := upperSaddleBranch (H / w) / w

/-- A broad free-cutoff band gives positive cutoffs and polynomially large ratios. -/
theorem power_band_bounds {H w : ℝ} (hH : 1 ≤ H)
    (hlo : H ^ (1 / 4 : ℝ) ≤ w) (hhi : w ≤ H ^ (3 / 4 : ℝ)) :
    0 < w ∧ 1 ≤ w ∧ w ≤ H ∧ H ^ (1 / 4 : ℝ) ≤ H / w ∧ H / w ≤ H := by
  have hHpos : 0 < H := by linarith
  have hpowone : 1 ≤ H ^ (1 / 4 : ℝ) := Real.one_le_rpow hH (by norm_num)
  have hwone := hpowone.trans hlo
  have hwpos : 0 < w := by linarith
  have hpowle : H ^ (3 / 4 : ℝ) ≤ H := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hH (by norm_num : (3 / 4 : ℝ) ≤ 1)
  have hproduct : H ^ (1 / 4 : ℝ) * H ^ (3 / 4 : ℝ) = H := by
    rw [← Real.rpow_add hHpos]
    norm_num
  have hnulo : H ^ (1 / 4 : ℝ) ≤ H / w := by
    apply (le_div_iff₀ hwpos).mpr
    calc
      _ ≤ H ^ (1 / 4 : ℝ) * H ^ (3 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left hhi (Real.rpow_nonneg hHpos.le _)
      _ = _ := hproduct
  have hnuhi : H / w ≤ H := (div_le_iff₀ hwpos).mpr (by nlinarith)
  exact ⟨hwpos, hwone, hhi.trans hpowle, hnulo, hnuhi⟩

/-- Every moving cutoff in the broad power band satisfies the scalar hypotheses,
uniformly over the choice of cutoff; no weighted-prime estimate is assumed. -/
theorem power_band_scale_conditions
    {alpha : Type*} {l : Filter alpha} {H w : alpha → ℝ}
    (hH : Tendsto H l atTop)
    (hband : ∀ᶠ i in l, H i ^ (1 / 4 : ℝ) ≤ w i ∧ w i ≤ H i ^ (3 / 4 : ℝ)) :
    Tendsto w l atTop ∧ Tendsto (fun i => H i / w i) l atTop ∧
      Tendsto (fun i => freeCutoffTilt (H i) (w i)) l (𝓝 0) ∧
      (∀ᶠ i in l, 0 < freeCutoffTilt (H i) (w i)) ∧
      Tendsto (fun i => |Real.log (freeCutoffTilt (H i) (w i))| / (H i / w i)) l (𝓝 0) := by
  have hpow : Tendsto (fun i => H i ^ (1 / 4 : ℝ)) l atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp hH
  have hb : ∀ᶠ i in l, 0 < w i ∧ 1 ≤ w i ∧ w i ≤ H i ∧
      H i ^ (1 / 4 : ℝ) ≤ H i / w i ∧ H i / w i ≤ H i := by
    filter_upwards [hband, hH.eventually (eventually_ge_atTop (1 : ℝ))] with i hi hHi
    exact power_band_bounds hHi hi.1 hi.2
  have hw : Tendsto w l atTop := tendsto_atTop_mono' l (hband.mono fun _ h => h.1) hpow
  have hnu : Tendsto (fun i => H i / w i) l atTop :=
    tendsto_atTop_mono' l (hb.mono fun _ h => h.2.2.2.1) hpow
  have hzpos : ∀ᶠ i in l, 0 < freeCutoffTilt (H i) (w i) := by
    filter_upwards [hb, hnu.eventually (eventually_ge_atTop (Real.exp 1))] with i hi hni
    exact div_pos (upperSaddleBranch_pos hni) hi.1
  have hratio : Tendsto (fun i => Real.log (H i) / H i ^ (1 / 4 : ℝ)) l (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).tendsto_div_nhds_zero.comp hH
  have hupper : ∀ᶠ i in l, freeCutoffTilt (H i) (w i) ≤
      2 * (Real.log (H i) / H i ^ (1 / 4 : ℝ)) := by
    filter_upwards [hb, hband, hnu.eventually upperSaddleBranch_le_two_log_eventually,
      hnu.eventually (eventually_gt_atTop (1 : ℝ)), hH.eventually (eventually_ge_atTop (1 : ℝ))]
      with i hi hbandi hu hn hHi
    have hlog := Real.log_le_log (by linarith : 0 < H i / w i) hi.2.2.2.2
    have hlogH : 0 ≤ Real.log (H i) := Real.log_nonneg hHi
    have hpowpos : 0 < H i ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    calc
      _ ≤ 2 * Real.log (H i) / w i := by
        apply div_le_div_of_nonneg_right _ hi.1.le
        linarith
      _ ≤ 2 * Real.log (H i) / H i ^ (1 / 4 : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) hpowpos hbandi.1
      _ = _ := by ring
  have hz : Tendsto (fun i => freeCutoffTilt (H i) (w i)) l (𝓝 0) := by
    apply squeeze_zero' (hzpos.mono fun _ h => h.le) hupper
    simpa only [mul_zero] using hratio.const_mul 2
  have hlogbound : ∀ᶠ i in l,
      |Real.log (freeCutoffTilt (H i) (w i))| / (H i / w i) ≤
        Real.log (H i) / H i ^ (1 / 4 : ℝ) := by
    filter_upwards [hb, hzpos, hz.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      hnu.eventually (eventually_ge_atTop (Real.exp 1)),
      hH.eventually (eventually_ge_atTop (1 : ℝ))] with i hi hzi hzsmall hn hHi
    have hupos : 0 < upperSaddleBranch (H i / w i) := upperSaddleBranch_pos hn
    have huone := (upperSaddleBranch_spec hn).1
    have hlogz : |Real.log (freeCutoffTilt (H i) (w i))| ≤ Real.log (H i) := by
      rw [abs_of_nonpos (Real.log_nonpos hzi.le hzsmall.le)]
      rw [freeCutoffTilt, Real.log_div hupos.ne' hi.1.ne']
      have hwH := Real.log_le_log hi.1 hi.2.2.1
      linarith [Real.log_nonneg huone]
    have hnpos : 0 < H i / w i := (Real.exp_pos 1).trans_le hn
    have hpowpos : 0 < H i ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    calc
      _ ≤ Real.log (H i) / (H i / w i) := div_le_div_of_nonneg_right hlogz hnpos.le
      _ ≤ _ := div_le_div_of_nonneg_left (Real.log_nonneg hHi) hpowpos hi.2.2.2.1
  have hlog : Tendsto (fun i => |Real.log (freeCutoffTilt (H i) (w i))| / (H i / w i)) l (𝓝 0) := by
    apply squeeze_zero' _ hlogbound hratio
    filter_upwards [hnu.eventually (eventually_gt_atTop (0 : ℝ))] with i hi
    positivity
  exact ⟨hw, hnu, hz, hzpos, hlog⟩

/-- The broad band eventually lies in the genuine Rankin and upper-branch domains,
with a threshold preceding the free cutoff. -/
theorem power_band_eventually_rankin_domain :
    ∃ Hzero : ℝ, ∀ H ≥ Hzero, ∀ w : ℝ,
      H ^ (1 / 4 : ℝ) ≤ w → w ≤ H ^ (3 / 4 : ℝ) →
      1 ≤ H ∧ 0 < w ∧ w ≤ H ∧ Real.exp 1 ≤ H / w ∧
        0 < freeCutoffTilt H w ∧ freeCutoffTilt H w ≤ 1 / 2 := by
  let P := {p : ℝ × ℝ // p.1 ^ (1 / 4 : ℝ) ≤ p.2 ∧ p.2 ≤ p.1 ^ (3 / 4 : ℝ)}
  let H : P → ℝ := fun p => p.val.1
  let w : P → ℝ := fun p => p.val.2
  let l : Filter P := Filter.comap H atTop
  have hH : Tendsto H l atTop := tendsto_comap
  have hband : ∀ᶠ p in l, H p ^ (1 / 4 : ℝ) ≤ w p ∧ w p ≤ H p ^ (3 / 4 : ℝ) :=
    Eventually.of_forall fun p => p.property
  obtain ⟨hw, hnu, hz, hzpos, _hlog⟩ := power_band_scale_conditions hH hband
  have hall : ∀ᶠ p in l,
      1 ≤ H p ∧ 0 < w p ∧ w p ≤ H p ∧ Real.exp 1 ≤ H p / w p ∧
        0 < freeCutoffTilt (H p) (w p) ∧ freeCutoffTilt (H p) (w p) ≤ 1 / 2 := by
    filter_upwards [hH.eventually (eventually_ge_atTop (1 : ℝ)),
      hnu.eventually (eventually_ge_atTop (Real.exp 1)), hzpos,
      hz.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with p hHp hn hp hz
    have hb := power_band_bounds hHp p.property.1 p.property.2
    exact ⟨hHp, hb.1, hb.2.2.1, hn, hp, hz.le⟩
  obtain ⟨s, hs, hsub⟩ := Filter.mem_comap.1 hall
  obtain ⟨Hzero, hzero⟩ := eventually_atTop.1 hs
  refine ⟨Hzero, ?_⟩
  intro h hh v hlo hhi
  exact hsub (a := (⟨(h, v), hlo, hhi⟩ : P)) (hzero h hh)

/-- Every fixed positive square-root band is contained in the broad power band,
with its threshold selected before the free cutoff. -/
theorem sqrt_log_band_eventually_in_power_band (c C : ℝ) (hc : 0 < c) (_hC : 0 < C) :
    ∃ Hzero : ℝ, ∀ H ≥ Hzero, ∀ w : ℝ,
      c * Real.sqrt (H * Real.log H) ≤ w →
      w ≤ C * Real.sqrt (H * Real.log H) →
      H ^ (1 / 4 : ℝ) ≤ w ∧ w ≤ H ^ (3 / 4 : ℝ) := by
  have hlo : ∀ᶠ H : ℝ in atTop, 1 ≤ c * H ^ (1 / 4 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).const_mul_atTop hc).eventually
      (eventually_ge_atTop 1)
  have hratio : Tendsto (fun H : ℝ => C ^ 2 * (Real.log H / H ^ (1 / 2 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero.const_mul (C ^ 2)
  have hevent : ∀ᶠ H : ℝ in atTop, ∀ w : ℝ,
      c * Real.sqrt (H * Real.log H) ≤ w →
      w ≤ C * Real.sqrt (H * Real.log H) →
      H ^ (1 / 4 : ℝ) ≤ w ∧ w ≤ H ^ (3 / 4 : ℝ) := by
    filter_upwards [hlo, hratio.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
      eventually_gt_atTop (0 : ℝ)] with H hlo hhi hlog hH
    intro w hwlo hwhi
    have hpowpos : 0 < H ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hH _
    have hpowhalf : H ^ (1 / 4 : ℝ) * H ^ (1 / 4 : ℝ) = Real.sqrt H := by
      rw [← Real.rpow_add hH, Real.sqrt_eq_rpow]
      norm_num
    have hrootlo : Real.sqrt H ≤ Real.sqrt (H * Real.log H) :=
      Real.sqrt_le_sqrt (by nlinarith)
    have hlow : H ^ (1 / 4 : ℝ) ≤ c * Real.sqrt (H * Real.log H) := by
      have hp := mul_le_mul_of_nonneg_right hlo hpowpos.le
      rw [mul_assoc, hpowhalf, one_mul] at hp
      exact hp.trans (mul_le_mul_of_nonneg_left hrootlo hc.le)
    have hhalfpos : 0 < H ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hH _
    have hineq : C ^ 2 * Real.log H ≤ H ^ (1 / 2 : ℝ) := by
      have hh : (C ^ 2 * Real.log H) / H ^ (1 / 2 : ℝ) ≤ 1 := by
        simpa only [mul_div_assoc] using hhi.le
      simpa only [one_mul] using (div_le_iff₀ hhalfpos).mp hh
    have hthree : (H ^ (3 / 4 : ℝ)) ^ 2 = H * H ^ (1 / 2 : ℝ) := by
      rw [pow_two, ← Real.rpow_add hH]
      calc
        _ = H ^ (1 + 1 / 2 : ℝ) := by congr 1; norm_num
        _ = H ^ (1 : ℝ) * H ^ (1 / 2 : ℝ) := Real.rpow_add hH _ _
        _ = _ := by rw [Real.rpow_one]
    have hrootsq := Real.sq_sqrt (show 0 ≤ H * Real.log H by positivity)
    have hupper : C * Real.sqrt (H * Real.log H) ≤ H ^ (3 / 4 : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hineq hH.le
      have hp : 0 ≤ H ^ (3 / 4 : ℝ) := Real.rpow_nonneg hH.le _
      nlinarith [Real.sqrt_nonneg (H * Real.log H)]
    exact ⟨hlow.trans hwlo, hwhi.trans hupper⟩
  exact eventually_atTop.1 hevent

end
end PaperC.V282.PrimeEulerFreeScales
