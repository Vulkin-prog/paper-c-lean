import PaperCV282.CrossoverLocationExtreme

/-! # Source-labelled location targets on the two genuine spatial scales -/
namespace PaperC.V282.CrossoverResolvedLocationTarget

open MeasureTheory ProbabilityTheory Filter Topology CrossoverMarkedModel CrossoverMarkedTarget
open CrossoverBulkOnePoint CrossoverMovingTarget CrossoverLocationGrid CrossoverLocationMixture
open CrossoverLocationProjection CrossoverLocationExtreme CrossoverLocationPhase
open BulkMarkedGeometry CountableWeakTransfer
open scoped NNReal ENNReal BoundedContinuousFunction

noncomputable section
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

/-- False denotes the microscopic source; true denotes the bulk source. -/
def labelledLaw (b : Bool) (p : ProbabilityMeasure ℝ) : ProbabilityMeasure (Bool×ℝ) :=
  imageProbabilityLaw (p : Measure ℝ) (fun x => (b,x)) (measurable_const.prodMk measurable_id)

def resolvedMixture (a b : ℝ≥0) (hab : a+b=1) (p q : ProbabilityMeasure ℝ) : ProbabilityMeasure (Bool×ℝ) :=
  ⟨(a : ℝ≥0∞) • (labelledLaw false p : Measure (Bool×ℝ))+
    (b : ℝ≥0∞) • (labelledLaw true q : Measure (Bool×ℝ)),by
    constructor
    simp only [Measure.add_apply,Measure.smul_apply,smul_eq_mul,measure_univ,mul_one]
    exact_mod_cast hab⟩

theorem integral_resolvedMixture (a b : ℝ≥0) (hab : a+b=1) (p q : ProbabilityMeasure ℝ)
    (F : (Bool×ℝ)→ᵇℝ) :
    (∫ z,F z ∂(resolvedMixture a b hab p q : Measure (Bool×ℝ)))=
      (a : ℝ)*(∫ x,F (false,x) ∂(p : Measure ℝ))+(b : ℝ)*(∫ x,F (true,x) ∂(q : Measure ℝ)) := by
  have hp : Integrable F (a • (labelledLaw false p : Measure (Bool×ℝ))) :=
    ⟨F.continuous.measurable.aestronglyMeasurable,HasFiniteIntegral.of_bounded
      (Eventually.of_forall fun z => F.norm_coe_le_norm z)⟩
  have hq : Integrable F (b • (labelledLaw true q : Measure (Bool×ℝ))) :=
    ⟨F.continuous.measurable.aestronglyMeasurable,HasFiniteIntegral.of_bounded
      (Eventually.of_forall fun z => F.norm_coe_le_norm z)⟩
  rw [show (resolvedMixture a b hab p q : Measure (Bool×ℝ))=
      a • (labelledLaw false p : Measure (Bool×ℝ))+b • (labelledLaw true q : Measure (Bool×ℝ)) from rfl,
    integral_add_measure hp hq,integral_smul_nnreal_measure,integral_smul_nnreal_measure]
  simp only [labelledLaw,integral_imageProbabilityLaw]
  rfl

theorem resolvedMixture_tendsto (a b : ℕ→ℝ≥0) (hab : ∀n,a n+b n=1)
    (a0 b0 : ℝ≥0) (hzero : a0+b0=1) (p q : ℕ→ProbabilityMeasure ℝ) (p0 q0 : ProbabilityMeasure ℝ)
    (ha : Tendsto (fun n => (a n : ℝ)) atTop (𝓝 (a0 : ℝ)))
    (hb : Tendsto (fun n => (b n : ℝ)) atTop (𝓝 (b0 : ℝ)))
    (hp : Tendsto p atTop (𝓝 p0)) (hq : Tendsto q atTop (𝓝 q0)) :
    Tendsto (fun n => resolvedMixture (a n) (b n) (hab n) (p n) (q n)) atTop
      (𝓝 (resolvedMixture a0 b0 hzero p0 q0)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hp hq ⊢
  intro F
  have hp' := hp (F.compContinuous ⟨fun x => (false,x),continuous_const.prodMk continuous_id⟩)
  have hq' := hq (F.compContinuous ⟨fun x => (true,x),continuous_const.prodMk continuous_id⟩)
  simpa only [integral_resolvedMixture,BoundedContinuousFunction.compContinuous_apply,ContinuousMap.coe_mk]
    using (ha.mul hp').add (hb.mul hq')

def microscopicLocationLaw (L : ℕ) : ProbabilityMeasure ℝ := ⟨Measure.dirac (1/(L : ℝ)^2),inferInstance⟩

def resolvedLimitLaw (s : ℝ) : ProbabilityMeasure (Bool×ℝ) :=
  resolvedMixture (phaseBorderWeight s) (phaseBulkWeight s) (phase_weights_sum s) zeroLocationLaw unitIntervalLaw

def resolvedTargetLaw (M L : ℕ) (delta : ℝ) : ProbabilityMeasure (Bool×ℝ) :=
  imageProbabilityLaw (targetLaw M L delta) (twoClockPosition M L) (measurable_of_countable _)

theorem borderLaw_twoClockPosition (M L : ℕ) :
    borderLaw.map (twoClockPosition M L)=(labelledLaw false (microscopicLocationLaw L) : Measure (Bool×ℝ)) := by
  rw [borderLaw,Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  change (geometricMeasure GeometricClusterTarget.halfSuccess).map (fun _ => (false,1/(L : ℝ)^2))=
    (Measure.dirac (1/(L : ℝ)^2)).map (fun x => (false,x))
  simp

theorem bulkLaw_twoClockPosition (M L : ℕ) (delta : ℝ) (hs : (bulkStarts M L delta).Nonempty) :
    (bulkLaw (bulkStarts M L delta) hs).map (twoClockPosition M L)=
      (labelledLaw true (bulkLocationLaw M L delta) : Measure (Bool×ℝ)) := by
  rw [bulkLaw,Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  change (labelMeasure (bulkStarts M L delta) hs).map
    ((fun x : bulkStarts M L delta => (true,(x.val : ℝ)/M)) ∘ Prod.fst)=
      (bulkLocationLaw M L delta : Measure ℝ).map (fun x => (true,x))
  rw [← Measure.map_map (measurable_of_countable _) measurable_fst,labelMeasure,
    Measure.map_fst_prod,measure_univ,one_smul,bulkLocationLaw_eq_uniform_site M L delta hs,
    Measure.map_map (show Measurable (fun x : ℝ => (true,x)) from measurable_const.prodMk measurable_id) (measurable_of_countable _)]
  rfl

theorem resolvedTargetLaw_eq {M L : ℕ} {delta : ℝ} (hs : (bulkStarts M L delta).Nonempty) :
    resolvedTargetLaw M L delta=resolvedMixture (borderWeight (bulkStarts M L delta) L)
      (bulkWeight (bulkStarts M L delta) L) (weights_sum _ L)
      (microscopicLocationLaw L) (bulkLocationLaw M L delta) := by
  apply Subtype.ext
  change (targetLaw M L delta).map (twoClockPosition M L)=_
  rw [targetLaw_eq hs,mixedLaw,Measure.map_add _ _ (measurable_of_countable _),
    Measure.map_smul,Measure.map_smul,borderLaw_twoClockPosition,bulkLaw_twoClockPosition M L delta hs]
  rfl

theorem microscopicLocationLaw_tendsto (lengths : ℕ→ℕ) (hlengths : Tendsto lengths atTop atTop) :
    Tendsto (fun n => microscopicLocationLaw (lengths n)) atTop (𝓝 zeroLocationLaw) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro F
  have hz : Tendsto (fun n => 1/(lengths n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hlengths)
  have hz2 : Tendsto (fun n => 1/(lengths n : ℝ)^2) atTop (𝓝 0) := by
    simpa only [div_pow,one_pow,zero_pow (by decide : 2≠0)] using hz.pow 2
  simpa only [microscopicLocationLaw,zeroLocationLaw,ProbabilityMeasure.coe_mk,integral_dirac,Function.comp_def]
    using F.continuous.continuousAt.tendsto.comp hz2

/-- A true two-source target limit, with both labels preserved. -/
theorem resolvedTargetLaw_tendsto_of_weights
    (sizes lengths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop) (hlengths : Tendsto lengths atTop atTop)
    (beta delta : ℝ) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (a b : ℝ≥0) (hab : a+b=1)
    (ha : Tendsto (fun n => (borderWeight (bulkStarts (sizes n) (lengths n) delta) (lengths n) : ℝ)) atTop (𝓝 (a : ℝ)))
    (hb : Tendsto (fun n => (bulkWeight (bulkStarts (sizes n) (lengths n) delta) (lengths n) : ℝ)) atTop (𝓝 (b : ℝ))) :
    Tendsto (fun n => resolvedTargetLaw (sizes n) (lengths n) delta) atTop
      (𝓝 (resolvedMixture a b hab zeroLocationLaw unitIntervalLaw)) := by
  have ht := resolvedMixture_tendsto _ _ (fun n => weights_sum (bulkStarts (sizes n) (lengths n) delta) (lengths n))
    a b hab _ _ zeroLocationLaw unitIntervalLaw ha hb (microscopicLocationLaw_tendsto lengths hlengths)
    (bulkLocationLaw_tendsto sizes lengths hsizes beta delta hdelta hdeltaOne hupper
      (hlengths.eventually (eventually_ge_atTop 1)))
  apply ht.congr'
  filter_upwards [bulk_nonempty_eventually sizes lengths hsizes beta delta hdelta hdeltaOne hupper
    (hlengths.eventually (eventually_ge_atTop 1))] with n hn
  exact (resolvedTargetLaw_eq hn).symm

end
end PaperC.V282.CrossoverResolvedLocationTarget
