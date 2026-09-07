import PaperCV282.AffineCrossoverModel
import PaperCV282.AffineCrossoverLocationProjection

/-! # Location transfer from the actual affine comparison with boundary clock erased

The finite inequalities use the actual `cappedDistance` at cap zero.  No
condition on the future prime coordinates is needed for a location statistic.
-/
namespace PaperC.V282.AffineCrossoverLocationTransfer

open MeasureTheory ProbabilityTheory Filter Topology InfiniteRademacher RarePrefixGeometry
open CrossoverMarkedModel CrossoverMarkedCandidate CrossoverLocationProjection
open CrossoverResolvedLocationSource CrossoverSourceCoupling CrossoverConditioningTools
open SharpConditioning SharpConditioningDiscrete ConditionedCountableLaw CountableExpectationTransfer
open AffineCrossoverLocationSource AffineCrossoverLocationProjection AffineCrossoverLocationTarget
open scoped NNReal ENNReal BoundedContinuousFunction

noncomputable section
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

theorem sourceLaw_probability {M L : ℕ} (delta : ℝ) {A : Set InfiniteSample}
    (hA : MeasurableSet A) (hpos : 0 < infiniteRademacherMeasure.real (A∩hitEvent M L)) :
    IsProbabilityMeasure (AffineCrossoverModel.sourceLaw (AffineCrossoverModel.conditionedMeasure A) M L delta) := by
  rw [AffineCrossoverModel.sourceLaw_conditioned A hA]
  letI _instProbabilityConditional : IsProbabilityMeasure (cond infiniteRademacherMeasure (A∩hitEvent M L)) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hpos)
  exact Measure.isProbabilityMeasure_map (measurable_gamma M L delta).aemeasurable

theorem capped_cemetery_mass (nu : Measure Record) (K : ℕ) :
    (nu.map (capBorder K)).real {none}=nu.real {none} := by
  rw [map_measureReal_apply (measurable_of_countable _) (measurableSet_singleton _)]
  congr 1
  ext r
  exact capBorder_eq_none K r

theorem source_cemetery_le {M L : ℕ} (delta : ℝ) (alpha : ℝ≥0) {A : Set InfiniteSample}
    (hA : MeasurableSet A) (hpos : 0 < infiniteRademacherMeasure.real (A∩hitEvent M L)) :
    (AffineCrossoverModel.sourceLaw (AffineCrossoverModel.conditionedMeasure A) M L delta).real {none}≤
      AffineCrossoverModel.cappedDistance (AffineCrossoverModel.conditionedMeasure A) M L 0 delta alpha := by
  letI _instProbabilitySource := sourceLaw_probability delta hA hpos
  letI _instProbabilityCappedSource := Measure.isProbabilityMeasure_map
    (μ := AffineCrossoverModel.sourceLaw (AffineCrossoverModel.conditionedMeasure A) M L delta)
    (measurable_of_countable (capBorder 0)).aemeasurable
  letI _instProbabilityCappedTarget := Measure.isProbabilityMeasure_map
    (μ := AffineCrossoverTarget.targetLaw M L delta alpha)
    (measurable_of_countable (capBorder 0)).aemeasurable
  have h := discrepancy_le
    ((AffineCrossoverModel.sourceLaw (AffineCrossoverModel.conditionedMeasure A) M L delta).map (capBorder 0))
    ((AffineCrossoverTarget.targetLaw M L delta alpha).map (capBorder 0)) {none} (measurableSet_singleton _)
  simpa only [capped_cemetery_mass,AffineCrossoverLocationProjection.targetLaw_cemetery_zero,
    sub_zero,abs_of_nonneg measureReal_nonneg,AffineCrossoverModel.cappedDistance] using h

/-- A generic statistic whose boundary clock has no effect.  Both exceptional
events are genuine subsets of the conditioned arithmetic source. -/
theorem statistic_tv_le {Beta : Type*} [MeasurableSpace Beta]
    {M L : ℕ} (delta : ℝ) (alpha : ℝ≥0) {A : Set InfiniteSample}
    (hA : MeasurableSet A) (hpos : 0 < infiniteRademacherMeasure.real (A∩hitEvent M L))
    (B : Set InfiniteSample) (g : InfiniteSample→Beta) (hg : Measurable g) (f : Record→Beta)
    (hcap : ∀r,f (capBorder 0 r)=f r)
    (hagree : ∀omega,omega∈hitEvent M L → omega∉B → gamma M L delta omega≠none →
      g omega=f (gamma M L delta omega)) :
    measureTotalVariation ((cond infiniteRademacherMeasure (A∩hitEvent M L)).map g)
      ((AffineCrossoverTarget.targetLaw M L delta alpha).map f)≤
        2*AffineCrossoverModel.cappedDistance (AffineCrossoverModel.conditionedMeasure A) M L 0 delta alpha+
          (cond infiniteRademacherMeasure (A∩hitEvent M L)).real B := by
  let mu := cond infiniteRademacherMeasure (A∩hitEvent M L)
  letI _instProbabilityConditional : IsProbabilityMeasure mu :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hpos)
  letI _instProbabilitySource := sourceLaw_probability delta hA hpos
  letI _instProbabilitySourceObserved := Measure.isProbabilityMeasure_map (μ := mu) hg.aemeasurable
  letI _instProbabilityMiddle := Measure.isProbabilityMeasure_map
    (μ := AffineCrossoverModel.sourceLaw (AffineCrossoverModel.conditionedMeasure A) M L delta)
    (measurable_of_countable f).aemeasurable
  letI _instProbabilityTargetObserved := Measure.isProbabilityMeasure_map
    (μ := AffineCrossoverTarget.targetLaw M L delta alpha) (measurable_of_countable f).aemeasurable
  letI _instProbabilityCappedSource := Measure.isProbabilityMeasure_map
    (μ := AffineCrossoverModel.sourceLaw (AffineCrossoverModel.conditionedMeasure A) M L delta)
    (measurable_of_countable (capBorder 0)).aemeasurable
  letI _instProbabilityCappedTarget := Measure.isProbabilityMeasure_map
    (μ := AffineCrossoverTarget.targetLaw M L delta alpha)
    (measurable_of_countable (capBorder 0)).aemeasurable
  have hc := map_tv_le_of_ae_eq_off mu ({omega | gamma M L delta omega=none}∪B) hg
    ((measurable_of_countable f).comp (measurable_gamma M L delta)) (by
      filter_upwards [ae_cond_mem (μ := infiniteRademacherMeasure) (hA.inter (measurableSet_hitEvent M L))] with omega hh
      intro ho
      exact hagree omega hh.2 (fun hb => ho (Or.inr hb)) (fun hn => ho (Or.inl hn)))
  have hp : mu.real {omega | gamma M L delta omega=none}=
      (AffineCrossoverModel.sourceLaw (AffineCrossoverModel.conditionedMeasure A) M L delta).real {none} := by
    rw [AffineCrossoverModel.sourceLaw_conditioned A hA,
      map_measureReal_apply (measurable_gamma M L delta) (measurableSet_singleton _)]
    rfl
  have hu : mu.real ({omega | gamma M L delta omega=none}∪B)≤
      AffineCrossoverModel.cappedDistance (AffineCrossoverModel.conditionedMeasure A) M L 0 delta alpha+mu.real B := by
    calc
      _≤mu.real {omega | gamma M L delta omega=none}+mu.real B := measureReal_union_le _ _
      _≤_ := by rw [hp];exact add_le_add (source_cemetery_le delta alpha hA hpos) le_rfl
  have he : mu.map (f ∘ gamma M L delta)=
      (AffineCrossoverModel.sourceLaw (AffineCrossoverModel.conditionedMeasure A) M L delta).map f := by
    rw [AffineCrossoverModel.sourceLaw_conditioned A hA,
      Measure.map_map (measurable_of_countable f) (measurable_gamma M L delta)]
  rw [he] at hc
  have hm := measureTotalVariation_map_le
    ((AffineCrossoverModel.sourceLaw (AffineCrossoverModel.conditionedMeasure A) M L delta).map (capBorder 0))
    ((AffineCrossoverTarget.targetLaw M L delta alpha).map (capBorder 0)) (measurable_of_countable f)
  change _≤AffineCrossoverModel.cappedDistance (AffineCrossoverModel.conditionedMeasure A) M L 0 delta alpha at hm
  rw [Measure.map_map (measurable_of_countable f) (measurable_of_countable (capBorder 0)),
    Measure.map_map (measurable_of_countable f) (measurable_of_countable (capBorder 0))] at hm
  simp only [Function.comp_def,hcap] at hm
  have ht := variation_triangle (mu.map g)
    ((AffineCrossoverModel.sourceLaw (AffineCrossoverModel.conditionedMeasure A) M L delta).map f)
    ((AffineCrossoverTarget.targetLaw M L delta alpha).map f)
  change _≤_+mu.real B
  linarith

theorem firstStartLaw_tv_le {M L : ℕ} (delta : ℝ) (d : ℕ) {A : Set InfiniteSample}
    (hA : MeasurableSet A) (hpos : 0 < infiniteRademacherMeasure.real (A∩hitEvent M L)) :
    measureTotalVariation (AffineCrossoverLocationSource.firstStartLaw M L A : Measure ℕ)
      (AffineCrossoverLocationProjection.targetStartLaw M L delta d : Measure ℕ)≤
        2*AffineCrossoverModel.cappedDistance (AffineCrossoverModel.conditionedMeasure A)
          M L 0 delta (((2 : ℝ≥0)⁻¹)^d) := by
  have h := statistic_tv_le delta (((2 : ℝ≥0)⁻¹)^d) hA hpos ∅
    (firstStart M L) (measurable_firstStart M L) recordStart (capBorder_recordStart 0)
    (fun _ _ _ hn => CrossoverLocationTransfer.firstStart_eq_recordStart hn)
  rw [← AffineCrossoverLocationSource.firstStartLaw_eq hpos] at h
  simpa only [AffineCrossoverLocationProjection.targetStartLaw,CountableWeakTransfer.imageProbabilityLaw,
    ProbabilityMeasure.coe_mk,measureReal_empty,add_zero] using h

theorem resolvedIntegerLaw_tv_le {M L : ℕ} (delta : ℝ) (d : ℕ) {A : Set InfiniteSample}
    (hA : MeasurableSet A) (hpos : 0 < infiniteRademacherMeasure.real (A∩hitEvent M L)) (hL : 1≤L) :
    measureTotalVariation (AffineCrossoverLocationSource.resolvedIntegerLaw M L A : Measure (Bool×ℕ))
      (targetResolvedIntegerLaw M L delta d : Measure (Bool×ℕ))≤
        2*AffineCrossoverModel.cappedDistance (AffineCrossoverModel.conditionedMeasure A)
          M L 0 delta (((2 : ℝ≥0)⁻¹)^d)+AffineCrossoverLocationSource.conditionalInteriorProbability M L A := by
  have h := statistic_tv_le delta (((2 : ℝ≥0)⁻¹)^d) hA hpos (MicroscopicNonvacancy.interiorEvent L)
    (resolvedInteger L ∘ firstStart M L)
    ((measurable_of_countable _).comp (measurable_firstStart M L)) recordInteger (capBorder_recordInteger 0)
    (fun _ hh hi hg => resolvedInteger_first_eq hL hh hi hg)
  rw [← AffineCrossoverLocationSource.resolvedIntegerLaw_eq hpos] at h
  exact h

theorem firstLocation_integral_error_le {M L : ℕ} (delta : ℝ) (d : ℕ) {A : Set InfiniteSample}
    (hA : MeasurableSet A) (hpos : 0 < infiniteRademacherMeasure.real (A∩hitEvent M L)) (F : ℝ→ᵇℝ) :
    |(∫ x,F x ∂(firstLocationLaw M L A : Measure ℝ))-
      (∫ x,F x ∂(physicalTargetLaw M L delta d : Measure ℝ))|≤
        4*‖F‖*AffineCrossoverModel.cappedDistance (AffineCrossoverModel.conditionedMeasure A)
          M L 0 delta (((2 : ℝ≥0)⁻¹)^d) := by
  rw [← AffineCrossoverLocationProjection.targetStartLaw_position M L delta d]
  change |(∫ x,F x ∂((AffineCrossoverLocationSource.firstStartLaw M L A : Measure ℕ).map
    (fun x : ℕ => (x : ℝ)/M)))-_|≤_
  rw [integral_map_of_stronglyMeasurable (measurable_of_countable _) F.continuous.measurable.stronglyMeasurable,
    integral_map_of_stronglyMeasurable (measurable_of_countable _) F.continuous.measurable.stronglyMeasurable]
  have h := integral_difference_le_tv (AffineCrossoverLocationSource.firstStartLaw M L A : Measure ℕ)
    (AffineCrossoverLocationProjection.targetStartLaw M L delta d : Measure ℕ)
    measurable_id measurable_id (fun x => F ((x : ℝ)/M)) ‖F‖
    (fun x => by simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm ((x : ℝ)/M))
  rw [← measureTotalVariation_eq_mass] at h
  exact h.trans (by
    calc
      _≤2*‖F‖*(2*AffineCrossoverModel.cappedDistance (AffineCrossoverModel.conditionedMeasure A)
        M L 0 delta (((2 : ℝ≥0)⁻¹)^d)) :=
          mul_le_mul_of_nonneg_left (firstStartLaw_tv_le delta d hA hpos) (by positivity)
      _=_ := by ring)

theorem resolvedSource_integral_error_le {M L : ℕ} (delta : ℝ) (d : ℕ) {A : Set InfiniteSample}
    (hA : MeasurableSet A) (hpos : 0 < infiniteRademacherMeasure.real (A∩hitEvent M L)) (hL : 1≤L)
    (F : (Bool×ℝ)→ᵇℝ) :
    |(∫ x,F x ∂(AffineCrossoverLocationSource.resolvedSourceLaw M L A : Measure (Bool×ℝ)))-
      (∫ x,F x ∂(AffineCrossoverLocationTarget.resolvedTargetLaw M L delta d : Measure (Bool×ℝ)))|≤
        2*‖F‖*(2*AffineCrossoverModel.cappedDistance (AffineCrossoverModel.conditionedMeasure A)
          M L 0 delta (((2 : ℝ≥0)⁻¹)^d)+AffineCrossoverLocationSource.conditionalInteriorProbability M L A) := by
  rw [← targetResolvedIntegerLaw_position M L delta d]
  change |(∫ x,F x ∂((AffineCrossoverLocationSource.resolvedIntegerLaw M L A : Measure (Bool×ℕ)).map
    (resolvedPosition M L)))-_|≤_
  rw [integral_map_of_stronglyMeasurable (measurable_of_countable _) F.continuous.measurable.stronglyMeasurable,
    integral_map_of_stronglyMeasurable (measurable_of_countable _) F.continuous.measurable.stronglyMeasurable]
  have h := integral_difference_le_tv (AffineCrossoverLocationSource.resolvedIntegerLaw M L A : Measure (Bool×ℕ))
    (targetResolvedIntegerLaw M L delta d : Measure (Bool×ℕ)) measurable_id measurable_id
    (fun x => F (resolvedPosition M L x)) ‖F‖
    (fun x => by simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm (resolvedPosition M L x))
  rw [← measureTotalVariation_eq_mass] at h
  exact h.trans (mul_le_mul_of_nonneg_left (resolvedIntegerLaw_tv_le delta d hA hpos hL) (by positivity))

end
end PaperC.V282.AffineCrossoverLocationTransfer
