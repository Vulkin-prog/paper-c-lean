import PaperCV282.CrossoverResolvedLocationTarget
import PaperCV282.CrossoverLocationTransfer
import PaperCV282.CrossoverRareScaleExceptions

/-! # The genuine first departure with its source label and its own clock -/
namespace PaperC.V282.CrossoverResolvedLocationSource

open MeasureTheory ProbabilityTheory Filter Topology InfiniteRademacher RarePrefixGeometry
open CrossoverMarkedModel CrossoverMovingTarget CrossoverSparseSource CrossoverLocationTransfer
open CrossoverLocationProjection CrossoverResolvedLocationTarget CrossoverSourceCoupling CrossoverUncapping
open SharpConditioning SharpConditioningDiscrete CrossoverConditioningTools ConditionedCountableLaw
open CountableWeakTransfer CountableExpectationTransfer MicroscopicNonvacancy
open CrossoverRareScale CrossoverRareScaleProbabilities CrossoverRareScaleExceptions
open PrimeEulerPNT ProcessAGGInput LaishramUniformInput PostQuadraticLiterature AllStartSoftPoisson
open scoped NNReal ENNReal BoundedContinuousFunction

noncomputable section
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- This classifies the real first start, including non-border microscopic starts. -/
def resolvedInteger (L x : ℕ) : Bool×ℕ := if x≤2*L^2 then (false,x) else (true,x)

def recordInteger : Record→Bool×ℕ
  | some (Sum.inl _) => (false,1)
  | some (Sum.inr (x,_)) => (true,x)
  | none => (false,0)

def resolvedPosition (M L : ℕ) (z : Bool×ℕ) : Bool×ℝ :=
  (z.1,(z.2 : ℝ)/(if z.1 then (M : ℝ) else (L : ℝ)^2))

/-- The actual source statistic: microscopic x/L², bulk x/M, with the label retained. -/
def resolvedFirstPosition (M L : ℕ) (omega : InfiniteSample) : Bool×ℝ :=
  resolvedPosition M L (resolvedInteger L (firstStart M L omega))

theorem resolvedPosition_recordInteger (M L : ℕ) (r : Record) :
    resolvedPosition M L (recordInteger r)=twoClockPosition M L r := by
  cases r with
  | none => simp [resolvedPosition,recordInteger,twoClockPosition]
  | some r => cases r <;> simp [resolvedPosition,recordInteger,twoClockPosition]

theorem resolvedInteger_first_eq {M L : ℕ} {delta : ℝ} {omega : InfiniteSample}
    (hL : 1≤L) (hh : omega∈hitEvent M L) (hi : omega∉interiorEvent L)
    (hg : gamma M L delta omega≠none) :
    resolvedInteger L (firstStart M L omega)=recordInteger (gamma M L delta omega) := by
  have hx := firstStart_eq_recordStart hg
  cases he : gamma M L delta omega with
  | none => exact (hg he).elim
  | some r =>
    cases r with
    | inl G =>
      have hx1 : firstStart M L omega=1 := by simpa [he,recordStart] using hx
      have hsmall : 1≤2*L^2 := by nlinarith
      simp [hx1,resolvedInteger,recordInteger,hsmall]
    | inr j =>
      have hxj : firstStart M L omega=j.1 := by simpa [he,recordStart] using hx
      have hxne : firstStart M L omega≠1 := by
        intro h
        simp [gamma,recordFromValues,h,borderLabel] at he
      obtain ⟨hx1,_,_,hs⟩ := (mem_containedStarts M L _ omega).mp (firstStart_mem hh)
      have hx2 : 2≤firstStart M L omega := by omega
      have hstart : omega∈InfiniteStartProbabilityTransfer.infiniteStartEvent (firstStart M L omega) L := by
        simpa [siteStartEvent,hxne,hx2] using hs
      have hlarge : ¬firstStart M L omega≤2*L^2 := by
        intro hsmall
        exact hi (Set.mem_iUnion.mpr ⟨_,Set.mem_iUnion.mpr
          ⟨Finset.mem_Icc.mpr ⟨hx2,hsmall⟩,hstart⟩⟩)
      have hjlarge : ¬j.1≤2*L^2 := hxj ▸ hlarge
      simp only [resolvedInteger,hxj,if_neg hjlarge,recordInteger]

def resolvedIntegerLaw (M L : ℕ) : ProbabilityMeasure (Bool×ℕ) :=
  imageProbabilityLaw (firstStartLaw M L : Measure ℕ) (resolvedInteger L) (measurable_of_countable _)

def resolvedSourceLaw (M L : ℕ) : ProbabilityMeasure (Bool×ℝ) :=
  imageProbabilityLaw (resolvedIntegerLaw M L : Measure (Bool×ℕ)) (resolvedPosition M L) (measurable_of_countable _)

def resolvedTargetIntegerLaw (M L : ℕ) (delta : ℝ) : ProbabilityMeasure (Bool×ℕ) :=
  imageProbabilityLaw (targetLaw M L delta) recordInteger (measurable_of_countable _)

theorem resolvedIntegerLaw_eq {M L : ℕ} (hLM : L≤M) :
    (resolvedIntegerLaw M L : Measure (Bool×ℕ))=
      (cond infiniteRademacherMeasure (hitEvent M L)).map (resolvedInteger L ∘ firstStart M L) := by
  change (firstStartLaw M L : Measure ℕ).map (resolvedInteger L)=_
  rw [firstStartLaw_eq hLM,Measure.map_map (measurable_of_countable _) (measurable_firstStart M L)]

theorem resolvedSourceLaw_eq {M L : ℕ} (hLM : L≤M) :
    (resolvedSourceLaw M L : Measure (Bool×ℝ))=
      (cond infiniteRademacherMeasure (hitEvent M L)).map (resolvedFirstPosition M L) := by
  change (resolvedIntegerLaw M L : Measure (Bool×ℕ)).map (resolvedPosition M L)=_
  rw [resolvedIntegerLaw_eq hLM,Measure.map_map (measurable_of_countable _)
    ((measurable_of_countable _).comp (measurable_firstStart M L))]
  rfl

theorem resolvedTargetIntegerLaw_position (M L : ℕ) (delta : ℝ) :
    (resolvedTargetIntegerLaw M L delta : Measure (Bool×ℕ)).map (resolvedPosition M L)=
      (resolvedTargetLaw M L delta : Measure (Bool×ℝ)) := by
  change ((targetLaw M L delta).map recordInteger).map (resolvedPosition M L)=_
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  congr 1
  funext r
  exact resolvedPosition_recordInteger M L r

def conditionalInteriorProbability (M L : ℕ) : ℝ :=
  (cond infiniteRademacherMeasure (hitEvent M L)).real (interiorEvent L)

theorem resolvedIntegerLaw_tv_le {M L : ℕ} (delta : ℝ) (hL : 1≤L) (hLM : L≤M) :
    measureTotalVariation (resolvedIntegerLaw M L : Measure (Bool×ℕ))
      (resolvedTargetIntegerLaw M L delta : Measure (Bool×ℕ))≤
        2*actualDistance M L delta+conditionalInteriorProbability M L := by
  let mu := cond infiniteRademacherMeasure (hitEvent M L)
  letI instProbabilityConditional : IsProbabilityMeasure mu :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ (hit_probability_pos hLM))
  letI instProbabilityGamma := conditionalGammaLaw_probability delta hLM
  letI instProbabilityRecorded : IsProbabilityMeasure ((conditionalGammaLaw M L delta).map recordInteger) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  have hc := map_tv_le_of_ae_eq_off mu ({omega | gamma M L delta omega=none}∪interiorEvent L)
    ((measurable_of_countable (resolvedInteger L)).comp (measurable_firstStart M L))
    ((measurable_of_countable recordInteger).comp (measurable_gamma M L delta)) (by
      filter_upwards [ae_cond_mem (μ := infiniteRademacherMeasure) (measurableSet_hitEvent M L)] with omega hh
      intro ho
      exact resolvedInteger_first_eq hL hh (fun hi => ho (Or.inr hi)) (fun hg => ho (Or.inl hg)))
  have hp : mu.real {omega | gamma M L delta omega=none}=(conditionalGammaLaw M L delta).real {none} := by
    rw [conditionalGammaLaw,map_measureReal_apply (measurable_gamma M L delta) (measurableSet_singleton _)]
    rfl
  have hu : mu.real ({omega | gamma M L delta omega=none}∪interiorEvent L)≤
      actualDistance M L delta+conditionalInteriorProbability M L := by
    calc
      _≤mu.real {omega | gamma M L delta omega=none}+mu.real (interiorEvent L) := measureReal_union_le _ _
      _=(conditionalGammaLaw M L delta).real {none}+conditionalInteriorProbability M L := by rw [hp]; rfl
      _≤_ := add_le_add (conditionalGamma_cemetery_le delta hLM) le_rfl
  have he : mu.map (recordInteger ∘ gamma M L delta)=
      (conditionalGammaLaw M L delta).map recordInteger := by
    rw [conditionalGammaLaw,Measure.map_map (measurable_of_countable _) (measurable_gamma M L delta)]
  rw [he] at hc
  change measureTotalVariation ((cond infiniteRademacherMeasure (hitEvent M L)).map
    (resolvedInteger L ∘ firstStart M L)) _≤_ at hc
  rw [← resolvedIntegerLaw_eq hLM] at hc
  have hm := measureTotalVariation_map_le (conditionalGammaLaw M L delta) (targetLaw M L delta)
    (measurable_of_countable recordInteger)
  have ht := variation_triangle (resolvedIntegerLaw M L : Measure (Bool×ℕ))
    ((conditionalGammaLaw M L delta).map recordInteger) (resolvedTargetIntegerLaw M L delta : Measure (Bool×ℕ))
  change _≤actualDistance M L delta at hm
  change _≤_+measureTotalVariation ((conditionalGammaLaw M L delta).map recordInteger)
    ((targetLaw M L delta).map recordInteger) at ht
  linarith

theorem resolvedSource_integral_error_le {M L : ℕ} (delta : ℝ) (hL : 1≤L) (hLM : L≤M)
    (F : (Bool×ℝ)→ᵇℝ) :
    |(∫ z,F z ∂(resolvedSourceLaw M L : Measure (Bool×ℝ)))-
      (∫ z,F z ∂(resolvedTargetLaw M L delta : Measure (Bool×ℝ)))|≤
        2*‖F‖*(2*actualDistance M L delta+conditionalInteriorProbability M L) := by
  rw [← resolvedTargetIntegerLaw_position M L delta]
  change |(∫ z,F z ∂((resolvedIntegerLaw M L : Measure (Bool×ℕ)).map (resolvedPosition M L)))-_|≤_
  rw [integral_map_of_stronglyMeasurable (measurable_of_countable _) F.continuous.measurable.stronglyMeasurable,
    integral_map_of_stronglyMeasurable (measurable_of_countable _) F.continuous.measurable.stronglyMeasurable]
  have h := integral_difference_le_tv (resolvedIntegerLaw M L : Measure (Bool×ℕ))
    (resolvedTargetIntegerLaw M L delta : Measure (Bool×ℕ)) measurable_id measurable_id
    (fun z => F (resolvedPosition M L z)) ‖F‖
    (fun z => by simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm (resolvedPosition M L z))
  rw [← measureTotalVariation_eq_mass] at h
  exact h.trans (mul_le_mul_of_nonneg_left (resolvedIntegerLaw_tv_le delta hL hLM) (by positivity))

theorem conditionalInteriorProbability_tendsto_zero
    (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (sizes lengths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop) (hlengths : Tendsto lengths atTop atTop)
    (beta delta : ℝ) (hbeta : 0<beta) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hrare : Tendsto (fun n => (fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => conditionalInteriorProbability (sizes n) (lengths n)) atTop (𝓝 0) := by
  have hi := interior_probability_rare_scale_tendsto_zero hLS hShorey hPNT sizes lengths hlengths delta
  have hh := hit_probability_ratio_tendsto_one hAGG hPNT hLS hShorey hNR sizes lengths hsizes hlengths
    beta delta hbeta hdelta hdeltaOne hupper hrare
  have hr := hi.div hh (by norm_num : (1 : ℝ)≠0)
  have hz : Tendsto (fun n => infiniteRademacherMeasure.real (interiorEvent (lengths n))/
      RarePrefixPoisson.hitProbability (sizes n) (lengths n)) atTop (𝓝 0) := by
    apply (show Tendsto _ atTop (𝓝 (0 : ℝ)) from by simpa only [zero_div] using hr).congr
    intro n
    dsimp only [Pi.div_apply]
    have hn := ne_of_gt (rareScale_pos (sizes n) (lengths n) delta)
    field_simp
  have hn0 : ∀ᶠ n in atTop,0≤conditionalInteriorProbability (sizes n) (lengths n) :=
    Eventually.of_forall fun _ => measureReal_nonneg
  apply squeeze_zero' hn0 ?_ hz
  filter_upwards [RarePrefixMass.logarithmic_lengths_eventually_contained sizes lengths hsizes beta hupper] with n hn
  change (cond infiniteRademacherMeasure (hitEvent (sizes n) (lengths n))).real (interiorEvent (lengths n))≤_
  rw [cond_real_apply _ _ (measurableSet_hitEvent _ _)]
  exact div_le_div_of_nonneg_right (measureReal_mono (h₂ := measure_ne_top _ _) Set.inter_subset_right)
    (hit_probability_pos hn).le

/-- Weak transfer on the labelled space, with both actual exceptional probabilities paid. -/
theorem resolvedSourceLaw_tendsto_of_errors
    (sizes lengths : ℕ→ℕ) (delta : ℝ)
    (hcontained : ∀ᶠ n in atTop,lengths n≤sizes n) (hpositive : ∀ᶠ n in atTop,1≤lengths n)
    (htv : Tendsto (fun n => actualDistance (sizes n) (lengths n) delta) atTop (𝓝 0))
    (hi : Tendsto (fun n => conditionalInteriorProbability (sizes n) (lengths n)) atTop (𝓝 0))
    (limit : ProbabilityMeasure (Bool×ℝ))
    (htarget : Tendsto (fun n => resolvedTargetLaw (sizes n) (lengths n) delta) atTop (𝓝 limit)) :
    Tendsto (fun n => resolvedSourceLaw (sizes n) (lengths n)) atTop (𝓝 limit) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at htarget ⊢
  intro F
  have hb : ∀ᶠ n in atTop,
      |(∫ z,F z ∂(resolvedSourceLaw (sizes n) (lengths n) : Measure (Bool×ℝ)))-
        (∫ z,F z ∂(resolvedTargetLaw (sizes n) (lengths n) delta : Measure (Bool×ℝ)))|≤
          2*‖F‖*(2*actualDistance (sizes n) (lengths n) delta+conditionalInteriorProbability (sizes n) (lengths n)) := by
    filter_upwards [hcontained,hpositive] with n hc hp
    exact resolvedSource_integral_error_le delta hp hc F
  have hz := squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) hb
    (show Tendsto (fun n => 2*‖F‖*(2*actualDistance (sizes n) (lengths n) delta+
      conditionalInteriorProbability (sizes n) (lengths n))) atTop (𝓝 0) by
        simpa only [mul_zero,add_zero] using ((htv.const_mul 2).add hi).const_mul (2*‖F‖))
  have hd : Tendsto (fun n =>
      (∫ z,F z ∂(resolvedSourceLaw (sizes n) (lengths n) : Measure (Bool×ℝ)))-
        (∫ z,F z ∂(resolvedTargetLaw (sizes n) (lengths n) delta : Measure (Bool×ℝ)))) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using hz)
  simpa only [sub_add_cancel,zero_add] using hd.add (htarget F)

end
end PaperC.V282.CrossoverResolvedLocationSource
