import PaperCV282.CrossoverLocationProjection
import PaperCV282.CrossoverUncapping

/-! # From the actual marked comparison to the first contained departure

The final transfer lemma takes convergence of the genuine marked distance
as an explicit assembly input. It is not a substitute for proving (7.9).
The source law itself is the true first start conditioned on non-vacancy.
-/
namespace PaperC.V282.CrossoverLocationTransfer

open MeasureTheory ProbabilityTheory Filter Topology InfiniteRademacher RarePrefixGeometry
open CrossoverMarkedModel CrossoverMarkedTarget CrossoverMovingTarget CrossoverSparseSource
open CrossoverLocationProjection CrossoverLocationMixture CrossoverSourceCoupling CrossoverUncapping
open SharpConditioning SharpConditioningDiscrete CrossoverConditioningTools ConditionedCountableLaw
open CountableWeakTransfer CountableExpectationTransfer InfiniteMassCoupling
open scoped NNReal ENNReal BoundedContinuousFunction

noncomputable section
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- The record retains the exact first integer start whenever it is not the cemetery mark. -/
theorem firstStart_eq_recordStart {M L : ℕ} {delta : ℝ} {omega : InfiniteSample}
    (hg : gamma M L delta omega≠none) : firstStart M L omega=recordStart (gamma M L delta omega) := by
  unfold gamma recordFromValues at hg ⊢
  split_ifs with hx
  · simp only [hx,borderLabel,recordStart]
  · cases hp : pointAtSite (BulkMarkedGeometry.bulkStarts M L delta) (firstStart M L omega)
        (BulkMarkedSource.spatialMarkedSource _ L omega) with
    | none => simp [hp,hx] at hg
    | some j =>
      have hj := pointAtSite_some_property hp
      simpa only [hp,Option.map_some,recordStart] using hj.1.symm

/-- The harmless default only concerns initial indices where no length-L window fits. -/
def firstStartLaw (M L : ℕ) : ProbabilityMeasure ℕ :=
  if hLM : L≤M then
    letI _instProbabilityConditionalHit : IsProbabilityMeasure (cond infiniteRademacherMeasure (hitEvent M L)) :=
      cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ (hit_probability_pos hLM))
    imageProbabilityLaw (cond infiniteRademacherMeasure (hitEvent M L)) (firstStart M L) (measurable_firstStart M L)
  else ⟨Measure.dirac 0,inferInstance⟩

theorem firstStartLaw_eq {M L : ℕ} (hLM : L≤M) :
    (firstStartLaw M L : Measure ℕ)=(cond infiniteRademacherMeasure (hitEvent M L)).map (firstStart M L) := by
  letI instProbabilityConditional : IsProbabilityMeasure
      (cond infiniteRademacherMeasure (hitEvent M L)) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ (hit_probability_pos hLM))
  have he : firstStartLaw M L =
      imageProbabilityLaw (cond infiniteRademacherMeasure (hitEvent M L))
        (firstStart M L) (measurable_firstStart M L) := dif_pos hLM
  exact congrArg (fun nu : ProbabilityMeasure ℕ => (nu : Measure ℕ)) he

def firstLocationLaw (M L : ℕ) : ProbabilityMeasure ℝ :=
  imageProbabilityLaw (firstStartLaw M L : Measure ℕ) (fun x : ℕ => (x : ℝ)/M) (measurable_of_countable _)

/-- Literal conditional first-start distribution, not a projection with the border moved to zero. -/
theorem firstLocationLaw_eq {M L : ℕ} (hLM : L≤M) :
    (firstLocationLaw M L : Measure ℝ)=
      (cond infiniteRademacherMeasure (hitEvent M L)).map (fun omega => (firstStart M L omega : ℝ)/M) := by
  change (firstStartLaw M L : Measure ℕ).map (fun x : ℕ => (x : ℝ)/M)=_
  rw [firstStartLaw_eq hLM,Measure.map_map (measurable_of_countable _) (measurable_firstStart M L)]
  rfl

def targetStartLaw (M L : ℕ) (delta : ℝ) : ProbabilityMeasure ℕ :=
  imageProbabilityLaw (targetLaw M L delta) recordStart (measurable_of_countable _)

theorem targetStartLaw_position (M L : ℕ) (delta : ℝ) :
    (targetStartLaw M L delta : Measure ℕ).map (fun x : ℕ => (x : ℝ)/M)=
      (physicalLocationMixtureLaw M L delta : Measure ℝ) := by
  change ((targetLaw M L delta).map recordStart).map (fun x : ℕ => (x : ℝ)/M)=_
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  exact targetLaw_recordPosition M L delta

/-- Losing the cemetery label costs at most one additional copy of the actual marked TV. -/
theorem firstStartLaw_tv_le {M L : ℕ} (delta : ℝ) (hLM : L≤M) :
    measureTotalVariation (firstStartLaw M L : Measure ℕ) (targetStartLaw M L delta : Measure ℕ)≤
      2*actualDistance M L delta := by
  let mu := cond infiniteRademacherMeasure (hitEvent M L)
  letI instProbabilityConditional : IsProbabilityMeasure mu :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ (hit_probability_pos hLM))
  letI instProbabilityGamma := conditionalGammaLaw_probability delta hLM
  letI instProbabilityRecorded : IsProbabilityMeasure ((conditionalGammaLaw M L delta).map recordStart) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  have hc := map_tv_le_of_ae_eq_off mu {omega | gamma M L delta omega=none}
    (measurable_firstStart M L) ((measurable_of_countable recordStart).comp (measurable_gamma M L delta))
    (Eventually.of_forall fun omega ho => firstStart_eq_recordStart ho)
  have hp : mu.real {omega | gamma M L delta omega=none}=
      (conditionalGammaLaw M L delta).real {none} := by
    rw [conditionalGammaLaw,map_measureReal_apply (measurable_gamma M L delta) (measurableSet_singleton _)]
    rfl
  rw [hp] at hc
  have he : mu.map (recordStart ∘ gamma M L delta)=
      (conditionalGammaLaw M L delta).map recordStart := by
    rw [conditionalGammaLaw,Measure.map_map (measurable_of_countable _) (measurable_gamma M L delta)]
  rw [he] at hc
  change measureTotalVariation ((cond infiniteRademacherMeasure (hitEvent M L)).map (firstStart M L)) _≤_ at hc
  rw [← firstStartLaw_eq hLM] at hc
  have hm := measureTotalVariation_map_le (conditionalGammaLaw M L delta) (targetLaw M L delta)
    (measurable_of_countable recordStart)
  have ht := variation_triangle (firstStartLaw M L : Measure ℕ)
    ((conditionalGammaLaw M L delta).map recordStart) (targetStartLaw M L delta : Measure ℕ)
  have hcem := conditionalGamma_cemetery_le delta hLM
  change _≤actualDistance M L delta at hm
  change _≤_+measureTotalVariation ((conditionalGammaLaw M L delta).map recordStart)
    ((targetLaw M L delta).map recordStart) at ht
  linarith

theorem firstLocation_integral_error_le {M L : ℕ} (delta : ℝ) (hLM : L≤M) (F : ℝ→ᵇℝ) :
    |(∫ x,F x ∂(firstLocationLaw M L : Measure ℝ))-
      (∫ x,F x ∂(physicalLocationMixtureLaw M L delta : Measure ℝ))|≤
        4*‖F‖*actualDistance M L delta := by
  rw [← targetStartLaw_position M L delta]
  change |(∫ x,F x ∂((firstStartLaw M L : Measure ℕ).map (fun x : ℕ => (x : ℝ)/M)))-_|≤_
  rw [integral_map_of_stronglyMeasurable (measurable_of_countable _) F.continuous.measurable.stronglyMeasurable,
    integral_map_of_stronglyMeasurable (measurable_of_countable _) F.continuous.measurable.stronglyMeasurable]
  have h := integral_difference_le_tv (firstStartLaw M L : Measure ℕ) (targetStartLaw M L delta : Measure ℕ)
    measurable_id measurable_id (fun x => F ((x : ℝ)/M)) ‖F‖
    (fun x => by simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm ((x : ℝ)/M))
  rw [← measureTotalVariation_eq_mass] at h
  exact h.trans (by
    calc
      _≤2*‖F‖*(2*actualDistance M L delta) :=
        mul_le_mul_of_nonneg_left (firstStartLaw_tv_le delta hLM) (by positivity)
      _=_ := by ring)

/-- Auxiliary weak transfer: the genuine marked comparison must be proved separately.
All sizes may lie on an arbitrary subsequence and no phase limit is needed here. -/
theorem firstLocationLaw_tendsto_of_actualDistance
    (sizes lengths : ℕ→ℕ) (delta : ℝ) (hcontained : ∀ᶠ n in atTop,lengths n≤sizes n)
    (htv : Tendsto (fun n => actualDistance (sizes n) (lengths n) delta) atTop (𝓝 0))
    (limit : ProbabilityMeasure ℝ)
    (htarget : Tendsto (fun n => physicalLocationMixtureLaw (sizes n) (lengths n) delta) atTop (𝓝 limit)) :
    Tendsto (fun n => firstLocationLaw (sizes n) (lengths n)) atTop (𝓝 limit) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at htarget ⊢
  intro F
  have hb : ∀ᶠ n in atTop,
      |(∫ x,F x ∂(firstLocationLaw (sizes n) (lengths n) : Measure ℝ))-
        (∫ x,F x ∂(physicalLocationMixtureLaw (sizes n) (lengths n) delta : Measure ℝ))|≤
          4*‖F‖*actualDistance (sizes n) (lengths n) delta :=
    hcontained.mono fun n hn => firstLocation_integral_error_le delta hn F
  have hzero := squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) hb
    (show Tendsto (fun n => 4*‖F‖*actualDistance (sizes n) (lengths n) delta) atTop (𝓝 0) by
      simpa only [mul_zero] using htv.const_mul (4*‖F‖))
  have hd : Tendsto (fun n =>
      (∫ x,F x ∂(firstLocationLaw (sizes n) (lengths n) : Measure ℝ))-
        (∫ x,F x ∂(physicalLocationMixtureLaw (sizes n) (lengths n) delta : Measure ℝ))) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using hzero)
  simpa only [sub_add_cancel,zero_add] using hd.add (htarget F)

/-- Finite-phase form of (7.19), conditional only on the separately established marked approximation. -/
theorem firstLocation_phase_limit_of_actualDistance
    (sizes lengths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop)
    (beta delta : ℝ) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hpositive : ∀ᶠ n in atTop,1≤lengths n)
    (htv : Tendsto (fun n => actualDistance (sizes n) (lengths n) delta) atTop (𝓝 0))
    (s : ℝ) (hphase : Tendsto (fun n => CrossoverLocationPhase.crossoverPhase (sizes n) (lengths n))
      atTop (𝓝 s)) :
    Tendsto (fun n => firstLocationLaw (sizes n) (lengths n)) atTop (𝓝 (crossoverLimitLaw s)) := by
  apply firstLocationLaw_tendsto_of_actualDistance sizes lengths delta
    (RarePrefixMass.logarithmic_lengths_eventually_contained sizes lengths hsizes beta hupper) htv
  exact physicalLocationMixtureLaw_tendsto sizes lengths hsizes beta delta hdelta hdeltaOne
    hupper hpositive s hphase

end
end PaperC.V282.CrossoverLocationTransfer
