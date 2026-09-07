import PaperCV282.AffineCrossoverLocationTheorem
import PaperCV282.CrossoverSourceSigns

/-! # The actual first sign under affine conditioning

The sign ignores the boundary clock. The zero-cap comparison therefore
proves its moving bias without any future-prime neutrality assumption.
-/
namespace PaperC.V282.AffineCrossoverSign

open MeasureTheory ProbabilityTheory Filter Topology InfiniteRademacher Affine
open AffineCrossoverErrorsAffine AffineCrossoverModel AffineCrossoverCylinder
open AffineCrossoverTheorem AffineCrossoverLocationTheorem AffineCrossoverLocationTransfer
open AffineBorderCylinders RarePrefixGeometry CrossoverMarkedModel CrossoverMarkedTarget
open CrossoverMarkedCandidate CrossoverSourceSigns BulkMarkedGeometry CrossoverBulkAtoms CrossoverRareScaleProbabilities
open HardPoissonRates AllStartSoftPoisson PrimeEulerPNT ProcessAGGInput SaddleParameters SaddleScales
open LaishramUniformInput PostQuadraticLiterature SharpConditioning ConditionedCountableLaw
open scoped NNReal

noncomputable section
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- Probability that the multiplicative sign at the true least departure is +1. -/
def positiveProbability (M L : ℕ) (A : Set InfiniteSample) : ℝ :=
  (cond infiniteRademacherMeasure (A∩hitEvent M L)).real {omega | positiveSource M L omega=true}

theorem capBorder_positiveSign (K : ℕ) (r : Record) : positiveSign (capBorder K r)=positiveSign r := by
  cases r with
  | none => rfl
  | some r => cases r <;> rfl

/-- The target bias involves the actual affine boundary mass and the true bulk population. -/
theorem positive_probability_error_le {M L : ℕ} (delta : ℝ) (alpha : ℝ≥0) {A : Set InfiniteSample}
    (hA : MeasurableSet A) (hpos : 0 < infiniteRademacherMeasure.real (A∩hitEvent M L))
    (hs : (bulkStarts M L delta).Nonempty) :
    |positiveProbability M L A-
      ((alpha : ℝ)+(totalRate (bulkStarts M L delta) L : ℝ)/2)/
        ((alpha : ℝ)+(totalRate (bulkStarts M L delta) L : ℝ))|≤
      2*cappedDistance (conditionedMeasure A) M L 0 delta alpha := by
  letI _instProbabilityConditional : IsProbabilityMeasure (cond infiniteRademacherMeasure (A∩hitEvent M L)) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hpos)
  letI _instProbabilitySourceObserved := Measure.isProbabilityMeasure_map
    (μ := cond infiniteRademacherMeasure (A∩hitEvent M L)) (measurable_positiveSource M L).aemeasurable
  letI _instProbabilityTargetObserved := Measure.isProbabilityMeasure_map
    (μ := AffineCrossoverTarget.targetLaw M L delta alpha) (measurable_of_countable positiveSign).aemeasurable
  have h := statistic_tv_le delta alpha hA hpos ∅ (positiveSource M L) (measurable_positiveSource M L)
    positiveSign (capBorder_positiveSign 0) (fun _ _ _ hn => (positiveSign_eq_source_off_cemetery hn).symm)
  simp only [measureReal_empty,add_zero] at h
  have ht := (discrepancy_le
    ((cond infiniteRademacherMeasure (A∩hitEvent M L)).map (positiveSource M L))
    ((AffineCrossoverTarget.targetLaw M L delta alpha).map positiveSign) {true}
    (measurableSet_singleton true)).trans h
  rw [map_measureReal_apply (measurable_positiveSource M L) (measurableSet_singleton true),
    map_measureReal_apply (measurable_of_countable _) (measurableSet_singleton true)] at ht
  change |positiveProbability M L A-
    (AffineCrossoverTarget.targetLaw M L delta alpha).real {r | positiveSign r=true}|≤_ at ht
  rw [AffineCrossoverTarget.targetLaw_eq alpha hs,AffineCrossoverTarget.mixedLaw_positive] at ht
  exact ht

variable (hAGG : ProcessAGGStatement) (hLS : UniformPrimeDivisorStatement)
    (hShorey : ShoreySquareProductStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (sizes lengths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop) (hlengths : Tendsto lengths atTop atTop)
    (beta delta c : ℝ) (hbeta : 0<beta) (hdelta : 0<delta) (hdeltaOne : delta<1) (hc : 0<c)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hrare : Tendsto (fun n => (fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0))
    (W : ℕ→Type*) [∀ n,AddCommGroup (W n)] [∀ n,Module F₂ (W n)]
    (G : ∀ n,SampleSpace (hardCutoff (sizes n))→ₗ[F₂]W n) (b : ∀ n,W n)
    (hstack : ∀ᶠ n in atTop,∃ hLY : lengths n≤hardCutoff (sizes n),
      Compatible ((G n).prod (borderProjection hLY)) (b n,0))
    (hbudget : ∀ᶠ n in atTop,cylinderInformation (G n)≤saddleCutoff 1 (Real.log (sizes n))-
      c*saddleNu 1 (Real.log (sizes n)))

include hAGG hLS hShorey hPNT hNR hsizes hlengths hbeta hdelta hdeltaOne hc hupper hrare hstack hbudget

/-- The moving positive-sign formula under the actual affine rank budget. -/
theorem theorem_seven_ten_sign :
    let A := fun n => affineCylinder (G n) (b n)
    let alpha := fun n => conditionalBorderRate (A n) (lengths n)
    Tendsto (fun n => positiveProbability (sizes n) (lengths n) (A n)-
      ((alpha n : ℝ)+(totalRate (bulkStarts (sizes n) (lengths n) delta) (lengths n) : ℝ)/2)/
        ((alpha n : ℝ)+(totalRate (bulkStarts (sizes n) (lengths n) delta) (lengths n) : ℝ)))
      atTop (𝓝 0) := by
  dsimp only
  obtain ⟨_,ht,_⟩ := theorem_seven_ten_zero_cap hAGG hLS hShorey hPNT hNR sizes lengths
    hsizes hlengths beta delta c hbeta hdelta hdeltaOne hc hupper hrare W G b hstack hbudget
  obtain ⟨hp,_,_⟩ := location_inputs_under_rank_budget hAGG hLS hShorey hPNT hNR sizes lengths
    hsizes hlengths beta delta c hbeta hdelta hdeltaOne hc hupper hrare W G b hstack hbudget
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (by simpa only [mul_zero] using ht.const_mul 2)
  filter_upwards [hp,bulk_nonempty_eventually sizes lengths hsizes beta delta hdelta hdeltaOne hupper
    (hlengths.eventually (eventually_ge_atTop 1))] with n hpn hn
  simpa only [Real.norm_eq_abs] using positive_probability_error_le delta
    (conditionalBorderRate (affineCylinder (G n) (b n)) (lengths n))
    (measurableSet_affineCylinder (G n) (b n)) hpn hn

end
end PaperC.V282.AffineCrossoverSign
