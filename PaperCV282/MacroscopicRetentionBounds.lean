import PaperCV282.MacroscopicCutoffBounds

/-! # Retention on dense bounded populations at a common saddle -/
namespace PaperC.V282.MacroscopicRetentionBounds

open Filter Topology MacroscopicMaskGeometry MacroscopicGeometry MacroscopicCutoffBounds
open SaddleParameters SaddleScales SaddlePoissonScales PrimeEulerPNT

noncomputable section

/-- Every population of ambient density at least one half retains density at least one quarter. -/
theorem card_goodMask_ge_quarter_eventually
    (hPNT : PrimeNumberTheoremRemainder) (a betaMax : ℝ) (ha : 0 < a) (hbeta : 0 < betaMax) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ mask : Finset ℕ, mask ⊆ Finset.Icc 2 N → (N : ℝ) / 2 ≤ mask.card →
      (N : ℝ) / 4 ≤ (goodMask L ⌊Real.exp (saddleCutoff a (Real.log N))⌋₊ mask).card := by
  obtain ⟨Nbad, hbad⟩ := normalized_badMask_saddle_le_eventually hPNT a betaMax 1 ha hbeta (by norm_num)
  obtain ⟨Nsmall, hsmall⟩ := saddle_exponential_le_eventually a (1 / a) 1 (1 / 4)
    ha (by positivity) (by norm_num)
  refine ⟨max Nbad (max Nsmall 1), ?_⟩
  intro N hN L hL mask hmask hcard
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hb := hbad N (by omega) L hL mask hmask
  have hs := hsmall N (by omega)
  have hexp : Real.exp (-saddleCutoff a (Real.log N) / a + 1 * saddleNu a (Real.log N)) ≤ 1 / 4 := by
    convert hs using 1; ring
  have hd := (div_le_iff₀ hn).mp (hb.trans hexp)
  have heq : ((goodMask L ⌊Real.exp (saddleCutoff a (Real.log N))⌋₊ mask).card : ℝ) +
      (badMask L ⌊Real.exp (saddleCutoff a (Real.log N))⌋₊ mask).card = mask.card := by
    exact_mod_cast card_good_add_bad L ⌊Real.exp (saddleCutoff a (Real.log N))⌋₊ mask
  linarith

/-- The literal half-open macroscopic interval has density at least one half eventually. -/
theorem card_macroscopicStarts_ge_half_eventually (delta : ℝ) (hdelta : delta < 1) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero,
      (N : ℝ) / 2 ≤ (macroscopicStarts N delta).card := by
  have hp : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 - delta))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - delta)).comp tendsto_natCast_atTop_atTop
  obtain ⟨Np, hp⟩ := eventually_atTop.1 (hp.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)))
  refine ⟨max Np 4, ?_⟩
  intro N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNfour : (4 : ℝ) ≤ N := by exact_mod_cast (show 4 ≤ N by omega)
  have hpow : (N : ℝ) ^ delta / N ≤ 1 / 4 := by
    calc
      _ = (N : ℝ) ^ (-(1 - delta)) := by rw [neg_sub, Real.rpow_sub hn, Real.rpow_one]
      _ ≤ _ := (hp N (by omega)).le
  have hpquarter := (div_le_iff₀ hn).mp hpow
  have hceil := Nat.ceil_lt_add_one (Real.rpow_nonneg hn.le delta)
  have hceilhalf : (⌈(N : ℝ) ^ delta⌉₊ : ℝ) ≤ (N : ℝ) / 2 := by linarith
  have hceilN : ⌈(N : ℝ) ^ delta⌉₊ ≤ N := by
    exact_mod_cast (show (⌈(N : ℝ) ^ delta⌉₊ : ℝ) ≤ (N : ℝ) by linarith)
  simp only [macroscopicStarts, Nat.card_Ico, Nat.cast_sub hceilN]
  linarith

/-- Retention for the actual macroscopic population, without a separate density hypothesis. -/
theorem card_good_macroscopic_ge_quarter_eventually
    (hPNT : PrimeNumberTheoremRemainder) (a betaMax delta : ℝ)
    (ha : 0 < a) (hbeta : 0 < betaMax) (hdelta : 0 < delta) (hdeltaOne : delta < 1) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      (L + 1 : ℝ) ≤ betaMax * Real.log N →
      (N : ℝ) / 4 ≤ (goodMask L ⌊Real.exp (saddleCutoff a (Real.log N))⌋₊
        (macroscopicStarts N delta)).card := by
  obtain ⟨Nr, hr⟩ := card_goodMask_ge_quarter_eventually hPNT a betaMax ha hbeta
  obtain ⟨Nc, hc⟩ := card_macroscopicStarts_ge_half_eventually delta hdeltaOne
  refine ⟨max Nr (max Nc 2), ?_⟩
  intro N hN L hL
  apply hr N (by omega) L hL _ _ (hc N (by omega))
  intro x hx
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hx
  exact Finset.mem_Icc.mpr ⟨(two_le_macroscopic_lowerEndpoint (by omega) hdelta).trans hlo, hhi.le⟩

end
end PaperC.V282.MacroscopicRetentionBounds
