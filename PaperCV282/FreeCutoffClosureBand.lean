import PaperCV282.FreeCutoffClosureScales

/-! # Uniform square-root comparisons for the free Rankin scales -/
namespace PaperC.V282.FreeCutoffClosureBand

open Filter Topology Real PrimeEulerFreeScales SaddleBranch FreeCutoffClosureScales

noncomputable section

theorem root_scale_products {H : ℝ} (hH : 1<H) :
    sqrt (H*log H)*sqrt (H/log H)=H ∧
    sqrt (H*log H)*sqrt (log H/H)=log H := by
  have hh : 0<H := by linarith
  have hl := log_pos hH
  constructor
  · rw [← sqrt_mul (by positivity),show (H*log H)*(H/log H)=H^2 by field_simp,
      sqrt_sq_eq_abs,abs_of_pos hh]
  · rw [← sqrt_mul (by positivity),show (H*log H)*(log H/H)=(log H)^2 by field_simp,
      sqrt_sq_eq_abs,abs_of_pos hl]

theorem normalized_scale_identities {H w : ℝ} (hH : 1<H) (hw : 0<w) :
    (H/w)/sqrt (H/log H)=sqrt (H*log H)/w ∧
    freeCutoffTilt H w/sqrt (log H/H)=
      (upperSaddleBranch (H/w)/log H)*(sqrt (H*log H)/w) := by
  have hh : 0<H := by linarith
  have hl := log_pos hH
  obtain ⟨hp,hq⟩ := root_scale_products hH
  constructor
  · field_simp
    nlinarith only [hp]
  · unfold freeCutoffTilt
    field_simp
    linear_combination -upperSaddleBranch (H/w)*hq

/-- Explicit comparison constants are uniform over the entire fixed cutoff band. -/
theorem scale_comparisons {H w c C : ℝ} (hH : 1<H) (hc : 0<c) (hC : 0<C)
    (hlo : c*sqrt (H*log H)≤w) (hhi : w≤C*sqrt (H*log H))
    (hu : 1/4≤upperSaddleBranch (H/w)/log H ∧ upperSaddleBranch (H/w)/log H≤1) :
    (1/C)*sqrt (H/log H)≤H/w ∧ H/w≤(1/c)*sqrt (H/log H) ∧
    (1/(4*C))*sqrt (log H/H)≤freeCutoffTilt H w ∧
      freeCutoffTilt H w≤(1/c)*sqrt (log H/H) := by
  have hh : 0<H := by linarith
  have hl := log_pos hH
  have hs : 0<sqrt (H*log H) := by positivity
  have hw : 0<w := (mul_pos hc hs).trans_le hlo
  have hlo' : 1/C≤sqrt (H*log H)/w := by
    apply (le_div_iff₀ hw).mpr
    have ht : w/C≤sqrt (H*log H) := (div_le_iff₀ hC).mpr (by linarith)
    simpa only [div_eq_mul_inv,mul_comm,one_mul,mul_one] using ht
  have hhi' : sqrt (H*log H)/w≤1/c := by
    apply (div_le_iff₀ hw).mpr
    have ht : sqrt (H*log H)≤w/c := (le_div_iff₀ hc).mpr (by linarith)
    simpa only [div_eq_mul_inv,mul_comm,one_mul,mul_one] using ht
  obtain ⟨hn,hz⟩ := normalized_scale_identities hH hw
  have hnl : (1/C)*sqrt (H/log H)≤H/w :=
    (le_div_iff₀ (by positivity)).mp (hn ▸ hlo')
  have hnu : H/w≤(1/c)*sqrt (H/log H) :=
    (div_le_iff₀ (by positivity)).mp (hn ▸ hhi')
  have hzl : 1/(4*C)≤freeCutoffTilt H w/sqrt (log H/H) := by
    rw [hz]
    have he := mul_le_mul hu.1 hlo' (by positivity : (0 : ℝ)≤1/C) (by linarith [hu.1])
    rw [show (1/4 : ℝ)*(1/C)=1/(4*C) by ring] at he
    exact he
  have hzu : freeCutoffTilt H w/sqrt (log H/H)≤1/c := by
    rw [hz]
    exact (mul_le_mul hu.2 hhi' (by positivity) (by norm_num)).trans (by simp)
  exact ⟨hnl,hnu,(le_div_iff₀ (by positivity)).mp hzl,(div_le_iff₀ (by positivity)).mp hzu⟩

/-- All displayed auxiliary B.1 scales, with a threshold preceding the arbitrary cutoff.
The epsilon estimate states u~(log H)/2 and log H=o(nu); the other two scales
have explicit positive comparison constants. No prime-distribution hypothesis is used. -/
theorem companion_B1_auxiliary_scales (c C epsilon : ℝ) (hc : 0<c) (hC : 0<C) (hepsilon : 0<epsilon) :
    ∃ H0 : ℝ, ∀ H≥H0, ∀ w : ℝ,
      c*sqrt (H*log H)≤w → w≤C*sqrt (H*log H) →
      |upperSaddleBranch (H/w)/log H-1/2|≤epsilon ∧
      log H≤epsilon*(H/w) ∧
      (1/C)*sqrt (H/log H)≤H/w ∧ H/w≤(1/c)*sqrt (H/log H) ∧
      (1/(4*C))*sqrt (log H/H)≤freeCutoffTilt H w ∧
        freeCutoffTilt H w≤(1/c)*sqrt (log H/H) := by
  let P := {p : ℝ×ℝ // c*sqrt (p.1*log p.1)≤p.2 ∧ p.2≤C*sqrt (p.1*log p.1)}
  let H : P→ℝ := fun p => p.val.1
  let w : P→ℝ := fun p => p.val.2
  let l : Filter P := Filter.comap H atTop
  have hH : Tendsto H l atTop := tendsto_comap
  have hb : ∀ᶠ p in l,c*sqrt (H p*log (H p))≤w p ∧ w p≤C*sqrt (H p*log (H p)) :=
    Eventually.of_forall fun p => p.property
  have hu := parameter_div_log_tendsto H w c C hc hC hH hb
  have hn := log_div_nu_tendsto_zero H w c C hc hC hH hb
  have he : ∀ᶠ p in l, |upperSaddleBranch (H p/w p)/log (H p)-1/2|≤epsilon := by
    filter_upwards [(Metric.tendsto_nhds.mp hu) epsilon hepsilon] with p hp
    exact (by simpa only [Real.dist_eq] using hp.le)
  have hall : ∀ᶠ p in l,
      |upperSaddleBranch (H p/w p)/log (H p)-1/2|≤epsilon ∧
      log (H p)≤epsilon*(H p/w p) ∧
      (1/C)*sqrt (H p/log (H p))≤H p/w p ∧ H p/w p≤(1/c)*sqrt (H p/log (H p)) ∧
      (1/(4*C))*sqrt (log (H p)/H p)≤freeCutoffTilt (H p) (w p) ∧
        freeCutoffTilt (H p) (w p)≤(1/c)*sqrt (log (H p)/H p) := by
    filter_upwards [he,hH.eventually (eventually_gt_atTop (1 : ℝ)),
      hu.eventually (lt_mem_nhds (by norm_num : (1/4 : ℝ)<1/2)),
      hu.eventually (gt_mem_nhds (by norm_num : (1/2 : ℝ)<1)),
      hn.eventually (gt_mem_nhds hepsilon)] with p hp hHp huL huU hnE
    have hh : 0<H p := by linarith
    have hl := log_pos hHp
    have hw : 0<w p := (mul_pos hc (by positivity)).trans_le p.property.1
    exact ⟨hp,(div_le_iff₀ (div_pos hh hw)).mp hnE.le,
      scale_comparisons hHp hc hC p.property.1 p.property.2 ⟨huL.le,huU.le⟩⟩
  obtain ⟨s,hs,hsub⟩ := Filter.mem_comap.1 hall
  obtain ⟨H0,h0⟩ := eventually_atTop.1 hs
  exact ⟨H0,fun h hh v hlo hhi => hsub (a := (⟨(h,v),hlo,hhi⟩ : P)) (h0 h hh)⟩

end
end PaperC.V282.FreeCutoffClosureBand
