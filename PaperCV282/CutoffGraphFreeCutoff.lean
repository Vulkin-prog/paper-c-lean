import PaperCV282.CutoffGraphScale
import PaperCV282.PrimeEulerFreeScales

/-!
# Unconditional degree costs on the full free-cutoff band

Only elementary scalar estimates are used after the finite all-site graph
count. In particular these theorems have no PNT premise. The actual rounded
cutoff, every bad site and every deterministic mask remain in the graph.
-/

namespace PaperC.V282.CutoffGraphFreeCutoff

open Set Filter Topology PrimeEulerFreeScales CutoffGraphDegree CutoffGraphScale MaskedPairGeometry

noncomputable section

/-- The elementary graph envelope has cost exp(-w+o(H/w)), uniformly before w and B. -/
theorem graph_envelope_power_band_eventually (betaMax epsilon : ℝ)
    (hbeta : 0 < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Hzero : ℝ, ∀ H ≥ Hzero, ∀ w : ℝ,
      H ^ (1 / 4 : ℝ) ≤ w → w ≤ H ^ (3 / 4 : ℝ) →
      Real.log 4 ≤ w ∧ betaMax * H ≤ Real.exp w ∧ betaMax * H ≤ Real.exp H ∧
      ∀ B : ℝ, 0 ≤ B → B ≤ betaMax * H →
      B ^ 2 * ((Real.log 3 + H) / (w - Real.log 2)) * (2 * Real.exp (-w) + Real.exp (-H)) ≤
        Real.exp (-w + epsilon * (H / w)) := by
  have hpow : Tendsto (fun H : ℝ => H ^ (1 / 4 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hlog : Tendsto (fun H : ℝ => Real.log H / H ^ (1 / 4 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).tendsto_div_nhds_zero
  have hlength : Tendsto (fun H : ℝ => (|Real.log betaMax| + Real.log H) / H ^ (1 / 4 : ℝ))
      atTop (𝓝 0) := by
    simpa only [add_div, add_zero] using
      ((tendsto_const_nhds (x := |Real.log betaMax|)).div_atTop hpow).add hlog
  have hfactor : Tendsto (fun H : ℝ => (|Real.log (6 * betaMax ^ 2)| + 3 * Real.log H) /
      H ^ (1 / 4 : ℝ)) atTop (𝓝 0) := by
    simpa only [add_div, mul_div_assoc, add_zero, mul_zero] using
      ((tendsto_const_nhds (x := |Real.log (6 * betaMax ^ 2)|)).div_atTop hpow).add (hlog.const_mul 3)
  have hevent : ∀ᶠ H : ℝ in atTop, ∀ w : ℝ,
      H ^ (1 / 4 : ℝ) ≤ w → w ≤ H ^ (3 / 4 : ℝ) →
      Real.log 4 ≤ w ∧ betaMax * H ≤ Real.exp w ∧ betaMax * H ≤ Real.exp H ∧
      ∀ B : ℝ, 0 ≤ B → B ≤ betaMax * H →
      B ^ 2 * ((Real.log 3 + H) / (w - Real.log 2)) * (2 * Real.exp (-w) + Real.exp (-H)) ≤
        Real.exp (-w + epsilon * (H / w)) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (Real.log 3),
      hpow.eventually (eventually_ge_atTop (Real.log 4)),
      hpow.eventually (eventually_ge_atTop (1 + Real.log 2)),
      hlength.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      hfactor.eventually (gt_mem_nhds hepsilon)] with H hHone hHthree hwfour hwgap hlen hfac
    intro w hlo hhi
    have hb := power_band_bounds hHone hlo hhi
    have hHpos : 0 < H := by linarith
    have hpowpos : 0 < H ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hHpos _
    have hgap : 1 ≤ w - Real.log 2 := by linarith
    have hlengthPow : betaMax * H ≤ Real.exp (H ^ (1 / 4 : ℝ)) := by
      have hlogle : Real.log betaMax + Real.log H ≤ H ^ (1 / 4 : ℝ) := by
        have hh := (div_le_iff₀ hpowpos).mp hlen.le
        linarith [le_abs_self (Real.log betaMax)]
      have hh := Real.exp_le_exp.mpr hlogle
      simpa only [Real.exp_add, Real.exp_log hbeta, Real.exp_log hHpos] using hh
    have hlengthW := hlengthPow.trans (Real.exp_le_exp.mpr hlo)
    refine ⟨hwfour.trans hlo, hlengthW, hlengthW.trans (Real.exp_le_exp.mpr hb.2.2.1), ?_⟩
    intro B hB hBupper
    have hratio : (Real.log 3 + H) / (w - Real.log 2) ≤ 2 * H := by
      apply (div_le_iff₀ (show 0 < w - Real.log 2 by linarith)).mpr
      nlinarith
    have hratioNonneg : 0 ≤ (Real.log 3 + H) / (w - Real.log 2) :=
      div_nonneg (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ 3 by norm_num)]) (by linarith)
    have hexp : Real.exp (-H) ≤ Real.exp (-w) := Real.exp_le_exp.mpr (by linarith [hb.2.2.1])
    have hfinite : B ^ 2 * ((Real.log 3 + H) / (w - Real.log 2)) *
        (2 * Real.exp (-w) + Real.exp (-H)) ≤ 6 * betaMax ^ 2 * H ^ 3 * Real.exp (-w) := by
      calc
        _ ≤ (betaMax * H) ^ 2 * (2 * H) * (3 * Real.exp (-w)) := by
          gcongr
          nlinarith
        _ = _ := by ring
    have hcost : Real.log (6 * betaMax ^ 2) + 3 * Real.log H ≤ epsilon * (H / w) := by
      have hf : |Real.log (6 * betaMax ^ 2)| + 3 * Real.log H ≤ epsilon * H ^ (1 / 4 : ℝ) :=
        (div_le_iff₀ hpowpos).mp hfac.le
      have hh := mul_le_mul_of_nonneg_left hb.2.2.2.1 hepsilon.le
      linarith [le_abs_self (Real.log (6 * betaMax ^ 2))]
    have hprod : 6 * betaMax ^ 2 * H ^ 3 = Real.exp (Real.log (6 * betaMax ^ 2) + 3 * Real.log H) := by
      have hlogpow : Real.log (H ^ 3) = 3 * Real.log H := by simp [Real.log_pow]
      rw [← hlogpow, ← Real.log_mul (by positivity : (6 * betaMax ^ 2 : ℝ) ≠ 0)
        (pow_ne_zero 3 hHpos.ne'), Real.exp_log (by positivity)]
    apply hfinite.trans
    rw [hprod, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  exact eventually_atTop.1 hevent

/-- The maximal degree and all ordered support edges have exponential cutoff cost.
This is unconditional and uniform before w, the window length and every mask. -/
theorem normalized_degree_and_edges_free_cutoff_le_eventually
    (c C betaMax epsilon : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hbeta : 0 < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ w : ℝ,
      c * Real.sqrt (Real.log N * Real.log (Real.log N)) ≤ w →
      w ≤ C * Real.sqrt (Real.log N * Real.log (Real.log N)) →
      ∀ L : ℕ, (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ mask : Finset ℕ, mask ⊆ dyadicBlock N →
      (cutoffMaxDegree L ⌊Real.exp w⌋₊ mask : ℝ) / N ≤
        Real.exp (-w + epsilon * (Real.log N / w)) ∧
      ((maskedSupportEdges L ⌊Real.exp w⌋₊ mask).card : ℝ) / (N : ℝ) ^ 2 ≤
        Real.exp (-w + epsilon * (Real.log N / w)) := by
  obtain ⟨Hband, hband⟩ := sqrt_log_band_eventually_in_power_band c C hc hC
  obtain ⟨Henv, henv⟩ := graph_envelope_power_band_eventually betaMax epsilon hbeta hepsilon
  have hnatlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Nzero, hzero⟩ := eventually_atTop.1
    (hnatlog.eventually (eventually_ge_atTop (max Hband Henv)))
  refine ⟨max Nzero 2, ?_⟩
  intro N hN w hlo hhi L hL mask hmask
  have hH := hzero N (by omega)
  obtain ⟨hpLo, hpHi⟩ := hband (Real.log N) (by order) w hlo hhi
  obtain ⟨hw, hlengthW, hlengthN, hbound⟩ := henv (Real.log N) (by order) w hpLo hpHi
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLN : L ≤ N := by
    rw [Real.exp_log hNpos] at hlengthN
    have hh := hL.trans hlengthN
    have hh' : (L : ℝ) ≤ N := by linarith
    exact_mod_cast hh'
  have hLY : L ≤ ⌊Real.exp w⌋₊ := by
    apply (Nat.le_floor_iff (Real.exp_nonneg w)).mpr
    have hh := hL.trans hlengthW
    linarith
  have hlog3N : Real.log (3 * N : ℕ) = Real.log 3 + Real.log N := by
    push_cast
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hNpos.ne']
  have hinv : (1 : ℝ) / N = Real.exp (-Real.log N) := by rw [Real.exp_neg, Real.exp_log hNpos, one_div]
  have hb := hbound (L + 1 : ℝ) (by positivity) hL
  constructor
  · apply (normalized_cutoffMaxDegree_floor_exp_le (by omega) hLN hw hLY hmask).trans
    simpa only [hlog3N, hinv] using hb
  · apply (normalized_maskedSupportEdges_floor_exp_le (by omega) hLN hw hLY hmask).trans
    simpa only [hlog3N, hinv] using hb

end
end PaperC.V282.CutoffGraphFreeCutoff
