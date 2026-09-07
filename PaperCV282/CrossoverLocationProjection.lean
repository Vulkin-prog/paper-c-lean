import PaperCV282.CrossoverLocationMixture
import PaperCV282.CrossoverMovingTarget
import PaperCV282.SharpConditioningDiscrete

/-! # Exact macroscopic projection of the moving crossover target -/
namespace PaperC.V282.CrossoverLocationProjection

open MeasureTheory ProbabilityTheory Filter Topology CrossoverMarkedModel CrossoverMarkedTarget
open CrossoverBulkOnePoint CrossoverMovingTarget CrossoverLocationGrid CrossoverLocationMixture
open BulkMarkedGeometry CountableWeakTransfer SharpConditioning SharpConditioningDiscrete
open scoped NNReal ENNReal BoundedContinuousFunction

noncomputable section
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

theorem borderLaw_macroPosition (M : ℕ) : borderLaw.map (macroPosition M)=Measure.dirac 0 := by
  rw [borderLaw,Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  change (geometricMeasure GeometricClusterTarget.halfSuccess).map (fun _ => (0 : ℝ))=_
  simp

theorem bulkLaw_macroPosition (M : ℕ) (sites : Finset ℕ) (hs : sites.Nonempty) :
    (bulkLaw sites hs).map (macroPosition M)=
      (uniformSiteMeasure sites hs).map (fun x => (x.val : ℝ)/M) := by
  rw [bulkLaw,Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  change (labelMeasure sites hs).map ((fun x : sites => (x.val : ℝ)/M) ∘ Prod.fst)=_
  rw [← Measure.map_map (measurable_of_countable _) measurable_fst,labelMeasure,
    Measure.map_fst_prod,measure_univ,one_smul]

/-- The map is the literal mixture of an atom at zero and uniform contained sites. -/
theorem targetLaw_macroPosition (M L : ℕ) (delta : ℝ) :
    (targetLaw M L delta).map (macroPosition M)=(locationMixtureLaw M L delta : Measure ℝ) := by
  by_cases hs : (bulkStarts M L delta).Nonempty
  · rw [targetLaw_eq hs,mixedLaw,Measure.map_add _ _ (measurable_of_countable _),
      Measure.map_smul,Measure.map_smul,borderLaw_macroPosition,bulkLaw_macroPosition]
    change _=(borderWeight _ L : ℝ≥0∞) • Measure.dirac 0+
      (bulkWeight _ L : ℝ≥0∞) • (bulkLocationLaw M L delta : Measure ℝ)
    rw [bulkLocationLaw_eq_uniform_site M L delta hs]
  · have he : bulkStarts M L delta=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    have hb : borderWeight (bulkStarts M L delta) L=1 := by
      simp only [borderWeight,he,CrossoverBulkAtoms.totalRate,Finset.card_empty,Nat.cast_zero,
        zero_div,add_zero,div_self (ne_of_gt (borderRate_pos L))]
    have hc : bulkWeight (bulkStarts M L delta) L=0 := by
      simp [bulkWeight,he,CrossoverBulkAtoms.totalRate]
    rw [targetLaw,dif_neg hs,borderLaw_macroPosition]
    change _=(borderWeight _ L : ℝ≥0∞) • Measure.dirac 0+
      (bulkWeight _ L : ℝ≥0∞) • (bulkLocationLaw M L delta : Measure ℝ)
    simp [hb,hc]

theorem targetLaw_cemetery_zero (M L : ℕ) (delta : ℝ) : (targetLaw M L delta).real {none}=0 := by
  unfold targetLaw
  split_ifs with hs
  · exact mixedLaw_cemetery_zero _ hs _
  · rw [borderLaw,Measure.real,Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
    have he : borderLabel ⁻¹' {none}=∅ := by ext k; simp [borderLabel]
    simp [he]

/-- The cemetery probability is controlled by the genuine source-to-target comparison. -/
theorem conditionalGamma_cemetery_le {M L : ℕ} (delta : ℝ) (hLM : L≤M) :
    (CrossoverSparseSource.conditionalGammaLaw M L delta).real {none}≤actualDistance M L delta := by
  letI instProbabilityGamma := CrossoverSparseSource.conditionalGammaLaw_probability delta hLM
  have h := discrepancy_le (CrossoverSparseSource.conditionalGammaLaw M L delta)
    (targetLaw M L delta) {none} (measurableSet_singleton _)
  simpa only [targetLaw_cemetery_zero,sub_zero,abs_of_nonneg measureReal_nonneg,actualDistance] using h

/-- The original integer position, with the border at one and the cemetery at zero. -/
def recordStart : Record→ℕ
  | some (Sum.inl _) => 1
  | some (Sum.inr (x,_)) => x
  | none => 0

def borderLocationLaw (M : ℕ) : ProbabilityMeasure ℝ := ⟨Measure.dirac (1/(M : ℝ)),inferInstance⟩

def physicalLocationMixtureLaw (M L : ℕ) (delta : ℝ) : ProbabilityMeasure ℝ :=
  mixtureLaw (borderWeight (bulkStarts M L delta) L) (bulkWeight (bulkStarts M L delta) L)
    (weights_sum _ L) (borderLocationLaw M) (bulkLocationLaw M L delta)

theorem borderLaw_recordPosition (M : ℕ) :
    borderLaw.map (fun r => (recordStart r : ℝ)/M)=Measure.dirac (1/(M : ℝ)) := by
  rw [borderLaw,Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  simp only [Function.comp_def,borderLabel,recordStart,Nat.cast_one]
  simp

theorem bulkLaw_recordPosition (M : ℕ) (sites : Finset ℕ) (hs : sites.Nonempty) :
    (bulkLaw sites hs).map (fun r => (recordStart r : ℝ)/M)=
      (uniformSiteMeasure sites hs).map (fun x => (x.val : ℝ)/M) := by
  rw [bulkLaw,Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  change (labelMeasure sites hs).map ((fun x : sites => (x.val : ℝ)/M) ∘ Prod.fst)=_
  rw [← Measure.map_map (measurable_of_countable _) measurable_fst,labelMeasure,
    Measure.map_fst_prod,measure_univ,one_smul]

theorem targetLaw_recordPosition (M L : ℕ) (delta : ℝ) :
    (targetLaw M L delta).map (fun r => (recordStart r : ℝ)/M)=
      (physicalLocationMixtureLaw M L delta : Measure ℝ) := by
  by_cases hs : (bulkStarts M L delta).Nonempty
  · rw [targetLaw_eq hs,mixedLaw,Measure.map_add _ _ (measurable_of_countable _),
      Measure.map_smul,Measure.map_smul,borderLaw_recordPosition,bulkLaw_recordPosition]
    change _=(borderWeight _ L : ℝ≥0∞) • Measure.dirac (1/(M : ℝ))+
      (bulkWeight _ L : ℝ≥0∞) • (bulkLocationLaw M L delta : Measure ℝ)
    rw [bulkLocationLaw_eq_uniform_site M L delta hs]
  · have he : bulkStarts M L delta=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    have hb : borderWeight (bulkStarts M L delta) L=1 := by
      simp only [borderWeight,he,CrossoverBulkAtoms.totalRate,Finset.card_empty,Nat.cast_zero,
        zero_div,add_zero,div_self (ne_of_gt (borderRate_pos L))]
    have hc : bulkWeight (bulkStarts M L delta) L=0 := by
      simp [bulkWeight,he,CrossoverBulkAtoms.totalRate]
    rw [targetLaw,dif_neg hs,borderLaw_recordPosition]
    change _=(borderWeight _ L : ℝ≥0∞) • Measure.dirac (1/(M : ℝ))+
      (bulkWeight _ L : ℝ≥0∞) • (bulkLocationLaw M L delta : Measure ℝ)
    simp [hb,hc]

theorem borderLocationLaw_tendsto (sizes : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop) :
    Tendsto (fun n => borderLocationLaw (sizes n)) atTop (𝓝 zeroLocationLaw) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro F
  have hzero : Tendsto (fun n => 1/(sizes n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hsizes)
  simpa only [borderLocationLaw,zeroLocationLaw,ProbabilityMeasure.coe_mk,integral_dirac,Function.comp_def] using
    F.continuous.continuousAt.tendsto.comp hzero

/-- The actual integer position of the border differs by 1/M, which vanishes in the weak limit. -/
theorem physicalLocationMixtureLaw_tendsto
    (sizes lengths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop)
    (beta delta : ℝ) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hpositive : ∀ᶠ n in atTop,1≤lengths n)
    (s : ℝ) (hphase : Tendsto (fun n => CrossoverLocationPhase.crossoverPhase (sizes n) (lengths n))
      atTop (𝓝 s)) :
    Tendsto (fun n => physicalLocationMixtureLaw (sizes n) (lengths n) delta) atTop
      (𝓝 (crossoverLimitLaw s)) := by
  obtain ⟨ha,hb⟩ := CrossoverLocationPhase.mixture_weights_tendsto sizes lengths hsizes beta delta
    hdelta hdeltaOne hupper hpositive s hphase
  apply mixtureLaw_tendsto _ _ _ _ _ _ _ _ _ _ _ _ (borderLocationLaw_tendsto sizes hsizes)
    (bulkLocationLaw_tendsto sizes lengths hsizes beta delta hdelta hdeltaOne hupper hpositive)
  · change Tendsto _ atTop (𝓝 (1/(1+(2 : ℝ)^(-s))))
    convert ha using 1
    funext n
    simp only [borderWeight,borderRate,CrossoverBulkAtoms.totalRate,BulkPopulation.bulkRate,
      FiniteStartMaskAverages.maskRate,NNReal.coe_div,NNReal.coe_add,NNReal.coe_pow,NNReal.coe_ofNat,
      inv_pow,one_div]
    rfl
  · change Tendsto _ atTop (𝓝 ((2 : ℝ)^(-s)/(1+(2 : ℝ)^(-s))))
    convert hb using 1
    funext n
    simp only [bulkWeight,borderRate,CrossoverBulkAtoms.totalRate,BulkPopulation.bulkRate,
      FiniteStartMaskAverages.maskRate,NNReal.coe_div,NNReal.coe_add,NNReal.coe_pow,NNReal.coe_ofNat,
      inv_pow,one_div]
    rfl

end
end PaperC.V282.CrossoverLocationProjection
