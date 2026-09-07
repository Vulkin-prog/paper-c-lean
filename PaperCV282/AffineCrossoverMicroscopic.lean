import PaperCV282.AffineCrossoverModel

/-! # Microscopic non-vacancy under the actual conditioned source

The error is relative to the affine border itself. This is stronger than
an error measured against the sum of the two rare sources.
-/
namespace PaperC.V282.AffineCrossoverMicroscopic

open MeasureTheory ProbabilityTheory Filter Topology Set InfiniteRademacher
open MicroscopicNonvacancy MicroscopicBorderEvents SharpConditioning ConditionedCountableLaw

noncomputable section

variable (mu : Measure InfiniteSample) [IsProbabilityMeasure mu]

theorem microscopic_ratio_error_le (L : ℕ) (ha : 0<mu.real (borderEvent L)) :
    |mu.real (microscopicEvent L)/mu.real (borderEvent L)-1| ≤
      mu.real (interiorEvent L)/mu.real (borderEvent L) := by
  have hlo : mu.real (borderEvent L)≤mu.real (microscopicEvent L) := measureReal_mono subset_union_left
  have hhi := measureReal_union_le (μ := mu) (borderEvent L) (interiorEvent L)
  have hd := div_le_div_of_nonneg_right hhi ha.le
  have hp : 1≤mu.real (microscopicEvent L)/mu.real (borderEvent L) :=
    (le_div_iff₀ ha).mpr (by simpa using hlo)
  rw [abs_of_nonneg (by linarith)]
  change mu.real (microscopicEvent L)/mu.real (borderEvent L)≤_ at hd
  rw [add_div,div_self ha.ne'] at hd
  linarith

theorem microscopic_conditional_tv_le (L : ℕ) (ha : 0<mu.real (borderEvent L)) :
    measureTotalVariation (cond mu (microscopicEvent L)) (cond mu (borderEvent L)) ≤
      mu.real (interiorEvent L)/mu.real (borderEvent L) := by
  have hle : mu.real (borderEvent L)≤mu.real (microscopicEvent L) := measureReal_mono subset_union_left
  have hpos := ha.trans_le hle
  have hm : mu.real (microscopicEvent L \ borderEvent L)≤mu.real (interiorEvent L) := by
    apply measureReal_mono (h₂ := measure_ne_top _ _)
    intro omega ho
    exact ho.1.resolve_left ho.2
  apply (nested_conditioning_le mu (borderEvent L) (microscopicEvent L)
    (measurableSet_borderEvent L) (measurableSet_microscopicEvent L) subset_union_left ha).trans
  exact (div_le_div_of_nonneg_right hm hpos.le).trans
    (div_le_div_of_nonneg_left measureReal_nonneg ha hle)

theorem conditional_unique_border_error_le (L : ℕ) (ha : 0<mu.real (borderEvent L)) :
    |(cond mu (microscopicEvent L)).real (uniqueBorderEvent L)-1| ≤
      mu.real (interiorEvent L)/mu.real (borderEvent L) := by
  have hle : mu.real (borderEvent L)≤mu.real (microscopicEvent L) := measureReal_mono subset_union_left
  have hpos := ha.trans_le hle
  have he : uniqueBorderEvent L=microscopicEvent L \ interiorEvent L := by
    ext omega
    simp only [uniqueBorderEvent,microscopicEvent,Set.mem_sdiff,Set.mem_union]
    tauto
  rw [cond_real_apply _ _ (measurableSet_microscopicEvent L),he,
    inter_eq_right.mpr sdiff_subset,
    measureReal_sdiff (show interiorEvent L⊆microscopicEvent L from subset_union_right)
      (measurableSet_interiorEvent L) (measure_ne_top _ _),sub_div,div_self hpos.ne']
  have hn : 0≤mu.real (interiorEvent L)/mu.real (microscopicEvent L) :=
    div_nonneg measureReal_nonneg hpos.le
  rw [show 1-mu.real (interiorEvent L)/mu.real (microscopicEvent L)-1=
    -(mu.real (interiorEvent L)/mu.real (microscopicEvent L)) by ring,abs_neg,abs_of_nonneg hn]
  exact div_le_div_of_nonneg_left measureReal_nonneg ha hle

/-- Both exact source conditionings become identical in total variation, while
the microscopic configuration contains only its border point with probability tending to one. -/
theorem microscopic_localization
    (mus : ℕ→Measure InfiniteSample) [∀ n,IsProbabilityMeasure (mus n)] (lengths : ℕ→ℕ)
    (ha : ∀ᶠ n in atTop,0<(mus n).real (borderEvent (lengths n)))
    (hi : Tendsto (fun n=>(mus n).real (interiorEvent (lengths n))/
      (mus n).real (borderEvent (lengths n))) atTop (𝓝 0)) :
    Tendsto (fun n=>(mus n).real (microscopicEvent (lengths n))/
      (mus n).real (borderEvent (lengths n))) atTop (𝓝 1) ∧
    Tendsto (fun n=>measureTotalVariation (cond (mus n) (microscopicEvent (lengths n)))
      (cond (mus n) (borderEvent (lengths n)))) atTop (𝓝 0) ∧
    Tendsto (fun n=>(cond (mus n) (microscopicEvent (lengths n))).real
      (uniqueBorderEvent (lengths n))) atTop (𝓝 1) := by
  refine ⟨?_,?_,?_⟩
  · apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) ?_ hi
    filter_upwards [ha] with n han
    simpa only [Real.norm_eq_abs] using microscopic_ratio_error_le (mus n) (lengths n) han
  · apply squeeze_zero' ?_ ?_ hi
    · filter_upwards [ha] with n han
      have hm : 0<(mus n).real (microscopicEvent (lengths n)) :=
        han.trans_le (measureReal_mono subset_union_left)
      letI instProbabilityMicro : IsProbabilityMeasure (cond (mus n) (microscopicEvent (lengths n))) :=
        cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hm)
      letI instProbabilityBorder : IsProbabilityMeasure (cond (mus n) (borderEvent (lengths n))) :=
        cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ han)
      exact measureTotalVariation_nonneg _ _
    · filter_upwards [ha] with n han
      exact microscopic_conditional_tv_le (mus n) (lengths n) han
  · apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) ?_ hi
    filter_upwards [ha] with n han
    simpa only [Real.norm_eq_abs] using conditional_unique_border_error_le (mus n) (lengths n) han

end
end PaperC.V282.AffineCrossoverMicroscopic
