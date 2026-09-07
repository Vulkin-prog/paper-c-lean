import PaperCV282.CrossoverUncapping
import PaperCV282.CrossoverMovingTarget

/-! # An assembly lemma removing the prime-clock cap from the actual comparison

Convergence of every capped comparison is an explicit premise of this assembly
lemma, to be supplied by the arithmetic and rare-event normalization modules.
This module alone is not Theorem 7.9.
-/
namespace PaperC.V282.CrossoverUncappingLimit

open MeasureTheory Filter Topology CrossoverUncapping CrossoverMovingTarget CrossoverSparseSource
open CrossoverMarkedModel CrossoverMarkedCandidate CrossoverMarkedTarget CrossoverConditioningTools SharpConditioning

noncomputable section

theorem targetLaw_cap_tv_le (M L K : ℕ) (delta : ℝ) :
    measureTotalVariation (targetLaw M L delta) ((targetLaw M L delta).map (capBorder K)) ≤
      1/(2 : ℝ)^(K+1) := by
  unfold targetLaw
  split_ifs with hs
  · exact mixedLaw_cap_tv_le _ hs L K
  · exact borderLaw_cap_tv_le K

theorem actualDistance_le_capped_add_tail {M L : ℕ} (delta : ℝ) (hLM : L≤M) (K : ℕ) :
    actualDistance M L delta ≤ cappedDistance M L K delta+2/(2 : ℝ)^(K+1) := by
  letI instProbabilitySource : IsProbabilityMeasure (conditionalGammaLaw M L delta) :=
    conditionalGammaLaw_probability delta hLM
  letI instProbabilityCapSource : IsProbabilityMeasure ((conditionalGammaLaw M L delta).map (capBorder K)) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  letI instProbabilityCapTarget : IsProbabilityMeasure ((targetLaw M L delta).map (capBorder K)) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  have h1 := variation_triangle (conditionalGammaLaw M L delta)
    ((conditionalGammaLaw M L delta).map (capBorder K)) (targetLaw M L delta)
  have h2 := variation_triangle ((conditionalGammaLaw M L delta).map (capBorder K))
    ((targetLaw M L delta).map (capBorder K)) (targetLaw M L delta)
  have hs := conditionalGamma_cap_tv_le delta hLM K
  have ht := targetLaw_cap_tv_le M L K delta
  rw [measureTotalVariation_comm (targetLaw M L delta)] at ht
  change measureTotalVariation (conditionalGammaLaw M L delta) (targetLaw M L delta) ≤ _
  unfold cappedDistance
  simp only [div_eq_mul_inv,one_mul] at hs ht ⊢
  linarith only [h1,h2,hs,ht]


/-- Fixed cap first, then cap to infinity; no nonempty-population premise is required. -/
theorem actualDistance_tendsto_of_capped
    (sizes lengths : ℕ→ℕ) (delta : ℝ) (hcontained : ∀ᶠ n in atTop, lengths n≤sizes n)
    (hcapped : ∀K : ℕ, Tendsto (fun n => cappedDistance (sizes n) (lengths n) K delta) atTop (𝓝 0)) :
    Tendsto (fun n => actualDistance (sizes n) (lengths n) delta) atTop (𝓝 0) := by
  have htail : Tendsto (fun K : ℕ => 2/(2 : ℝ)^(K+1)) atTop (𝓝 0) := by
    have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ)≤2⁻¹)
      (by norm_num : (2 : ℝ)⁻¹<1)
    convert ht using 1
    funext K
    rw [pow_succ,inv_pow]
    field_simp
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨K,hK⟩ := (htail.eventually (gt_mem_nhds (half_pos hepsilon))).exists
  have hev := (hcapped K).eventually (gt_mem_nhds (half_pos hepsilon))
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hcontained.and hev)
  refine ⟨N,fun n hn => ?_⟩
  obtain ⟨hc,hv⟩ := hN n hn
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (actualDistance_nonneg delta hc)]
  have hh := actualDistance_le_capped_add_tail delta hc K
  linarith

end
end PaperC.V282.CrossoverUncappingLimit
