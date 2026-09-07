import PaperCV282.MacroscopicGraphBounds
import PaperCV282.MacroscopicBadBounds

/-! # Common free-cutoff and saddle costs on arbitrary bounded populations -/
namespace PaperC.V282.MacroscopicCutoffBounds

open Set Filter Topology PrimeEulerFreeScales CutoffGraphDegree MaskedPairGeometry
open CutoffGraphScale CutoffGraphFreeCutoff PrimeEulerCutoff
open MacroscopicMaskGeometry SaddleParameters SaddleScales SaddleCutoffAdmissibility PrimeEulerPNT

noncomputable section

/-- Companion (B.3) at the exact discretized cutoff, normalized by the ambient population. -/
theorem normalized_cutoffMaxDegree_floor_exp_le {N L : ℕ} (hN : 2 ≤ N) (hL : L ≤ N)
    {w : ℝ} (hw : Real.log 4 ≤ w) (hLY : L ≤ ⌊Real.exp w⌋₊)
    {mask : Finset ℕ} (hmask : mask ⊆ Finset.Icc 2 N) :
    (cutoffMaxDegree L ⌊Real.exp w⌋₊ mask : ℝ) / N ≤
      (L + 1 : ℝ) ^ 2 * (Real.log (3 * N : ℕ) / (w - Real.log 2)) *
        (2 * Real.exp (-w) + 1 / N) := by
  have hY : 1 < ⌊Real.exp w⌋₊ := by have := (floor_exp_bounds hw).1; omega
  exact (MacroscopicGraphBounds.normalized_cutoffMaxDegree_le hN hL hLY hY hmask).trans (floor_cutoff_envelope_le hN hw)

/-- The identical cutoff envelope for the ordered edges on every mask. -/
theorem normalized_maskedSupportEdges_floor_exp_le {N L : ℕ} (hN : 2 ≤ N) (hL : L ≤ N)
    {w : ℝ} (hw : Real.log 4 ≤ w) (hLY : L ≤ ⌊Real.exp w⌋₊)
    {mask : Finset ℕ} (hmask : mask ⊆ Finset.Icc 2 N) :
    ((maskedSupportEdges L ⌊Real.exp w⌋₊ mask).card : ℝ) / (N : ℝ) ^ 2 ≤
      (L + 1 : ℝ) ^ 2 * (Real.log (3 * N : ℕ) / (w - Real.log 2)) *
        (2 * Real.exp (-w) + 1 / N) := by
  have hY : 1 < ⌊Real.exp w⌋₊ := by have := (floor_exp_bounds hw).1; omega
  exact (MacroscopicGraphBounds.normalized_maskedSupportEdges_le hN hL hLY hY hmask).trans (floor_cutoff_envelope_le hN hw)


/-- The maximal degree and all ordered support edges have exponential cutoff cost.
This is unconditional and uniform before w, the window length and every mask. -/
theorem normalized_degree_and_edges_free_cutoff_le_eventually
    (c C betaMax epsilon : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hbeta : 0 < betaMax) (hepsilon : 0 < epsilon) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ w : ℝ,
      c * Real.sqrt (Real.log N * Real.log (Real.log N)) ≤ w →
      w ≤ C * Real.sqrt (Real.log N * Real.log (Real.log N)) →
      ∀ L : ℕ, (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ mask : Finset ℕ, mask ⊆ Finset.Icc 2 N →
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


/-- Both actual all-site graph budgets at the true saddle, with no PNT premise. -/
theorem normalized_degree_and_edges_saddle_le_eventually
    (a betaMax eta : ℝ) (ha : 0 < a) (hbeta : 0 < betaMax) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ mask : Finset ℕ, mask ⊆ Finset.Icc 2 N →
      (cutoffMaxDegree L ⌊Real.exp (saddleCutoff a (Real.log N))⌋₊ mask : ℝ) / N ≤
        Real.exp (-saddleCutoff a (Real.log N) + eta * saddleNu a (Real.log N)) ∧
      ((maskedSupportEdges L ⌊Real.exp (saddleCutoff a (Real.log N))⌋₊ mask).card : ℝ) / (N : ℝ) ^ 2 ≤
        Real.exp (-saddleCutoff a (Real.log N) + eta * saddleNu a (Real.log N)) := by
  obtain ⟨c, C, hc, hC, Hband, hband⟩ := saddleCutoff_sqrt_log_band_eventually ha
  obtain ⟨Ngraph, hgraph⟩ := normalized_degree_and_edges_free_cutoff_le_eventually
    c C betaMax eta hc hC hbeta heta
  have hnatlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Nband, hNband⟩ := eventually_atTop.1 (hnatlog.eventually (eventually_ge_atTop Hband))
  refine ⟨max Ngraph Nband, ?_⟩
  intro N hN L hL mask hmask
  obtain ⟨hlo, hhi⟩ := hband (Real.log N) (hNband N (by omega))
  exact hgraph N (by omega) (saddleCutoff a (Real.log N)) hlo hhi L hL mask hmask


/-- The actual bad-support fraction at the saddle, before every bounded population. -/
theorem normalized_badMask_saddle_le_eventually
    (hPNT : PrimeNumberTheoremRemainder) (a betaMax eta : ℝ)
    (ha : 0 < a) (hbeta : 0 < betaMax) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ mask : Finset ℕ, mask ⊆ Finset.Icc 2 N →
      ((badMask L ⌊Real.exp (saddleCutoff a (Real.log N))⌋₊ mask).card : ℝ) / N ≤
        Real.exp (-saddleCutoff a (Real.log N) / a + eta * saddleNu a (Real.log N)) := by
  obtain ⟨c, C, hc, hC, Hband, hband⟩ := saddleCutoff_sqrt_log_band_eventually ha
  obtain ⟨Nbad, hbad⟩ := MacroscopicBadBounds.normalized_badMask_free_cutoff_le_eventually
    hPNT c C betaMax eta hc hC hbeta heta
  have hnatlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Nband, hNband⟩ := eventually_atTop.1
    (hnatlog.eventually (eventually_ge_atTop (max Hband (saddleThreshold a))))
  refine ⟨max Nbad Nband, ?_⟩
  intro N hN L hL mask hmask
  have hH := hNband N (by omega)
  obtain ⟨hlo, hhi⟩ := hband (Real.log N) (by order)
  have hcost : saddleCost (saddleNu a (Real.log N)) = saddleCutoff a (Real.log N) / a := by
    have h := saddleCutoff_equation ha (show saddleThreshold a ≤ Real.log N by order)
    change saddleCutoff a (Real.log N) = a * saddleCost (saddleNu a (Real.log N)) at h
    rw [h]
    field_simp [ha.ne']
  have h := hbad N (by omega) (saddleCutoff a (Real.log N)) hlo hhi L hL mask hmask
  change _ ≤ Real.exp (-saddleCost (saddleNu a (Real.log N)) + eta * saddleNu a (Real.log N)) at h
  simpa only [hcost, neg_div] using h

end
end PaperC.V282.MacroscopicCutoffBounds
