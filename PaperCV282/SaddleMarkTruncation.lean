import PaperCV282.ExactMarkedCritical
import PaperCV282.SaddleCutoffAdmissibility

/-!
# The actual growing excess cutoff at the critical saddle

The rounded cutoff is chosen before the run length. Its geometric tail has
the required exponential rate and its support enlargement is o(log N).
-/
namespace PaperC.V282.SaddleMarkTruncation

open Filter Topology SaddleParameters SaddleScales SaddlePoissonScales
open SaddleCutoffAdmissibility CriticalRunWindow ExactMarkedCritical
open ConditionalStartProbability AllStartSoftPoisson

noncomputable section

/-- The integer cutoff printed after (5.16). -/
def criticalMarkCutoff (N : ℕ) : ℕ :=
  ⌈saddleCutoff 1 (Real.log N) / Real.log 2⌉₊

theorem criticalMarkCutoff_cost (N : ℕ) :
    saddleCutoff 1 (Real.log N) ≤ (criticalMarkCutoff N : ℝ) * Real.log 2 := by
  have h := Nat.le_ceil (saddleCutoff 1 (Real.log N) / Real.log 2)
  exact (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp h

/-- Rounding upwards preserves the exact exponential tail upper bound. -/
theorem criticalMarkCutoff_geometric_tail (N : ℕ) :
    1 / (2 : ℝ)^(criticalMarkCutoff N + 1) ≤
      Real.exp (-saddleCutoff 1 (Real.log N)) := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hcost := criticalMarkCutoff_cost N
  have hpow : (2 : ℝ)^(criticalMarkCutoff N+1) =
      Real.exp (((criticalMarkCutoff N+1 : ℕ) : ℝ)*Real.log 2) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]
  rw [hpow,one_div,← Real.exp_neg]
  apply Real.exp_le_exp.mpr
  push_cast
  linarith

/-- The total enlargement, including its terminal vertex, is negligible on the logarithmic scale. -/
theorem criticalMarkCutoff_div_log_tendsto_zero :
    Tendsto (fun N : ℕ => ((criticalMarkCutoff N : ℝ)+1)/Real.log N) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ =>
      (saddleCutoff 1 (Real.log N)/Real.log N)/Real.log 2+2/Real.log N)
      atTop (𝓝 0) := by
    simpa using ((tendsto_saddleCutoff_div_height (a := 1) (by norm_num)).comp hlog).div_const
      (Real.log 2) |>.add (tendsto_const_nhds.div_atTop hlog)
  apply squeeze_zero' _ _ hlim
  · filter_upwards [hlog.eventually (eventually_gt_atTop (0 : ℝ))] with N hN
    positivity
  · filter_upwards [hlog.eventually (eventually_ge_atTop (saddleThreshold 1)),
      hlog.eventually (eventually_gt_atTop (0 : ℝ))] with N hN hn
    have hv := saddleCutoff_pos (a := 1) (by norm_num) hN
    have hc := (Nat.ceil_lt_add_one (div_nonneg hv.le
      (Real.log_pos (by norm_num : (1 : ℝ)<2)).le)).le
    change (criticalMarkCutoff N : ℝ) ≤ saddleCutoff 1 (Real.log N)/Real.log 2+1 at hc
    calc
      _ ≤ (saddleCutoff 1 (Real.log N)/Real.log 2+2)/Real.log N := by
        apply div_le_div_of_nonneg_right _ hn.le
        linarith
      _ = _ := by ring

/-- One full logarithmic band covers all critical lengths and the growing cutoff. -/
theorem critical_growing_mark_band_eventually (C : ℝ) (hC : 0 ≤ C) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ, InRunLengthWindow C N L →
      1 ≤ L ∧ lowerConstant*Real.log N ≤ (L+1 : ℝ) ∧
      (L+criticalMarkCutoff N+2 : ℝ) ≤ (2*upperConstant)*Real.log N ∧
      (fullRate N L : ℝ) ≤ balanceConstant C := by
  obtain ⟨Nb,hb⟩ := firstMomentWindow_eventually hC
  have hu : 0 < upperConstant := lowerConstant_pos.trans lowerConstant_lt_upperConstant
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Ne,he⟩ := eventually_atTop.1 (criticalMarkCutoff_div_log_tendsto_zero.eventually
    (gt_mem_nhds hu))
  obtain ⟨Np,hp⟩ := eventually_atTop.1 (hlog.eventually (eventually_gt_atTop (0 : ℝ)))
  refine ⟨max Nb (max Ne Np),?_⟩
  intro N hN L hw
  obtain ⟨hband,hL,hint⟩ := hb N (by omega) L hw
  have hlow := hband.2.2.1
  have hhigh := hband.2.2.2
  have hE := (div_lt_iff₀ (hp N (by omega))).mp (he N (by omega))
  refine ⟨hL,by exact_mod_cast hlow,?_,?_⟩
  · push_cast at hhigh ⊢
    nlinarith
  · simpa only [fullRate_coe] using hint

end
end PaperC.V282.SaddleMarkTruncation
