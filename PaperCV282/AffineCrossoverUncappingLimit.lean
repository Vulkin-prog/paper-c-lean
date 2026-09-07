import PaperCV282.AffineCrossoverUncapping

/-! # Fixed-cap then infinite-cap assembly for affine marked laws

The exact conditional clock law is needed only eventually for each fixed
cap.  Initial indices may even fail to define probability source measures;
all such hypotheses are explicitly eventual.
-/
namespace PaperC.V282.AffineCrossoverUncappingLimit

open MeasureTheory ProbabilityTheory Filter Topology InfiniteRademacher
open CrossoverMarkedModel CrossoverPrimeClockStable MicroscopicBorderEvents
open AffineCrossoverUncapping SharpConditioning GeometricClusterTarget
open scoped NNReal

noncomputable section
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

theorem actualDistance_tendsto_of_capped
    (measures : ℕ→Measure InfiniteSample) (sizes lengths : ℕ→ℕ)
    (alphas : ℕ → ℝ≥0) (delta : ℝ)
    (hprob : ∀ᶠ n in atTop,IsProbabilityMeasure (measures n))
    (hcontained : ∀ᶠ n in atTop,lengths n≤sizes n)
    (hborder : ∀ᶠ n in atTop,0<(measures n).real (borderEvent (lengths n)))
    (hclock : ∀K : ℕ,∀ᶠ n in atTop,
      (cond (measures n) (borderEvent (lengths n))).map (actualClockRecord (lengths n) (K+1))=
        (geometricMeasure halfSuccess).map (fun j => (true,min j (K+1))))
    (hcapped : ∀K : ℕ,Tendsto (fun n =>
      AffineCrossoverModel.cappedDistance (measures n) (sizes n) (lengths n) K delta (alphas n)) atTop (𝓝 0)) :
    Tendsto (fun n => AffineCrossoverModel.actualDistance (measures n) (sizes n) (lengths n) delta (alphas n))
      atTop (𝓝 0) := by
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
  have hfinal : ∀ᶠ n in atTop,dist
      (AffineCrossoverModel.actualDistance (measures n) (sizes n) (lengths n) delta (alphas n)) 0<epsilon := by
    filter_upwards [hprob,hcontained,hborder,hclock K,hev] with n hp hc hb hk hv
    letI _instProbabilityMeasure := hp
    letI _instProbabilitySource := AffineCrossoverModel.sourceLaw_probability (measures n)
      (sizes n) (lengths n) delta (hit_probability_pos (measures n) hc hb)
    have hn : 0≤AffineCrossoverModel.actualDistance (measures n) (sizes n) (lengths n) delta (alphas n) :=
      measureTotalVariation_nonneg _ _
    rw [Real.dist_eq,sub_zero,abs_of_nonneg hn]
    have ht := actualDistance_le_capped_add_tail (measures n) delta (alphas n) hc hb K hk
    linarith
  exact eventually_atTop.mp hfinal

end
end PaperC.V282.AffineCrossoverUncappingLimit
