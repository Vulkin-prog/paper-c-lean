import PaperCV282.SaddleMarkTruncation

/-!
# A common growing cutoff for the labelled information budget

Three times the critical cutoff removes both tails after any information
cost admitted by the labelled hard budget. This cutoff stays o(log N).
-/
namespace PaperC.V282.GrowingMarkedTruncation

open Filter Topology SaddleMarkTruncation SaddleParameters SaddleScales

noncomputable section

def growingMarkCutoff (N : ℕ) : ℕ := 3*criticalMarkCutoff N

theorem growingMarkCutoff_cost (N : ℕ) :
    3*saddleCutoff 1 (Real.log N) ≤ (growingMarkCutoff N : ℝ)*Real.log 2 := by
  have h := criticalMarkCutoff_cost N
  unfold growingMarkCutoff
  push_cast
  linarith

theorem growingMarkCutoff_geometric_tail (N : ℕ) :
    1/(2 : ℝ)^(growingMarkCutoff N+1) ≤ Real.exp (-3*saddleCutoff 1 (Real.log N)) := by
  have hcost := growingMarkCutoff_cost N
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hpow : (2 : ℝ)^(growingMarkCutoff N+1) =
      Real.exp (((growingMarkCutoff N+1 : ℕ) : ℝ)*Real.log 2) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]
  rw [hpow,one_div,← Real.exp_neg]
  apply Real.exp_le_exp.mpr
  push_cast
  linarith

theorem growingMarkCutoff_div_log_tendsto_zero :
    Tendsto (fun N : ℕ => ((growingMarkCutoff N : ℝ)+1)/Real.log N) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h := (criticalMarkCutoff_div_log_tendsto_zero.const_mul 3).sub
    (tendsto_const_nhds.div_atTop hlog : Tendsto (fun N : ℕ => (2 : ℝ)/Real.log N) atTop (𝓝 0))
  simp only [mul_zero,sub_zero] at h
  convert h using 1
  funext N
  unfold growingMarkCutoff
  push_cast
  ring

/-- The threshold for the enlarged band precedes the actual base length. -/
theorem growing_mark_band_eventually (beta : ℝ) (hbeta : 0 < beta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      (L+1 : ℝ) ≤ beta*Real.log N →
      (L+growingMarkCutoff N+2 : ℝ) ≤ (2*beta)*Real.log N := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Ne,he⟩ := eventually_atTop.1 (growingMarkCutoff_div_log_tendsto_zero.eventually (gt_mem_nhds hbeta))
  obtain ⟨Np,hp⟩ := eventually_atTop.1 (hlog.eventually (eventually_gt_atTop (0 : ℝ)))
  refine ⟨max Ne Np,?_⟩
  intro N hN L hL
  have hE := (div_lt_iff₀ (hp N (by omega))).mp (he N (by omega))
  linarith

end
end PaperC.V282.GrowingMarkedTruncation
