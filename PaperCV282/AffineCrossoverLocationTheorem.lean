import PaperCV282.AffineCrossoverTheorem
import PaperCV282.AffineCrossoverDeficit
import PaperCV282.AffineCrossoverLocationLimits

/-! # Affine crossover localization from the actual rank budget

The deficit is the exact border row-space deficit, not an independent rate
parameter. Both locations are laws of the original source conditioned by
`affineCylinder ∩ hitEvent`. The resolved location retains its source label
and uses the microscopic or ambient spatial scale accordingly. None of
these three phase conclusions requires future-prime neutrality.
-/
namespace PaperC.V282.AffineCrossoverLocationTheorem

open MeasureTheory ProbabilityTheory Filter Topology InfiniteRademacher Affine
open AffineCrossoverErrorsAffine AffineCrossoverModel AffineCrossoverCylinder
open AffineCrossoverDeficit AffineCrossoverTheorem AffineCrossoverLocationSource
open AffineCrossoverLocationLimits AffineCrossoverPhase AffineBorderCylinders
open RarePrefixGeometry MicroscopicBorderEvents HardPoissonRates AllStartSoftPoisson
open PrimeEulerPNT ProcessAGGInput SaddleParameters SaddleScales
open LaishramUniformInput PostQuadraticLiterature CrossoverLocationMixture CrossoverLocationGrid
open CrossoverResolvedLocationTarget
open scoped NNReal

noncomputable section
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

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

/-- All location-transfer inputs are consequences of the genuine arithmetic budget. -/
theorem location_inputs_under_rank_budget :
    let A := fun n => affineCylinder (G n) (b n)
    let d := fun n => borderDeficitAt (G n) (lengths n)
    (∀ᶠ n in atTop,0 < infiniteRademacherMeasure.real (A n∩hitEvent (sizes n) (lengths n))) ∧
    Tendsto (fun n => cappedDistance (conditionedMeasure (A n)) (sizes n) (lengths n) 0 delta
      (((2 : ℝ≥0)⁻¹)^d n)) atTop (𝓝 0) ∧
    Tendsto (fun n => conditionalInteriorProbability (sizes n) (lengths n) (A n)) atTop (𝓝 0) := by
  dsimp only
  obtain ⟨_,htv,hi⟩ := theorem_seven_ten_zero_cap hAGG hLS hShorey hPNT hNR sizes lengths
    hsizes hlengths beta delta c hbeta hdelta hdeltaOne hc hupper hrare W G b hstack hbudget
  have hLM := RarePrefixMass.logarithmic_lengths_eventually_contained sizes lengths hsizes beta hupper
  refine ⟨?_,?_,hi⟩
  · filter_upwards [hstack,hLM] with n hn hln
    obtain ⟨hLY,hs⟩ := hn
    apply (affine_border_intersection_probability_pos (G n) (b n) hLY hs).trans_le
    apply measureReal_mono (h₂ := measure_ne_top _ _)
    apply Set.inter_subset_inter_right
    rw [hitEvent_eq_union hln]
    exact Set.subset_union_left
  · apply htv.congr'
    filter_upwards [hstack] with n hn
    obtain ⟨hLY,hs⟩ := hn
    rw [conditionalBorderRate_eq_deficit (G n) (b n) hLY hs]

/-- The finite affine phase, with both the ordinary and source-resolved locations. -/
theorem theorem_seven_ten_location
    (s : ℝ) (hphase : Tendsto (fun n => affinePhase (sizes n) (lengths n)
      (borderDeficitAt (G n) (lengths n))) atTop (𝓝 s)) :
    Tendsto (fun n => firstLocationLaw (sizes n) (lengths n) (affineCylinder (G n) (b n)))
      atTop (𝓝 (crossoverLimitLaw s)) ∧
    Tendsto (fun n => resolvedSourceLaw (sizes n) (lengths n) (affineCylinder (G n) (b n)))
      atTop (𝓝 (resolvedLimitLaw s)) := by
  obtain ⟨hp,ht,hi⟩ := location_inputs_under_rank_budget hAGG hLS hShorey hPNT hNR sizes lengths
    hsizes hlengths beta delta c hbeta hdelta hdeltaOne hc hupper hrare W G b hstack hbudget
  exact location_phase_limit_of_errors sizes lengths (fun n => borderDeficitAt (G n) (lengths n))
    (fun n => affineCylinder (G n) (b n)) hsizes hlengths beta delta hdelta hdeltaOne hupper
    (Eventually.of_forall fun n => measurableSet_affineCylinder (G n) (b n)) hp ht hi s hphase

/-- Positive infinite affine phase: all limiting location mass is microscopic. -/
theorem theorem_seven_ten_location_phase_atTop
    (hphase : Tendsto (fun n => affinePhase (sizes n) (lengths n)
      (borderDeficitAt (G n) (lengths n))) atTop atTop) :
    Tendsto (fun n => firstLocationLaw (sizes n) (lengths n) (affineCylinder (G n) (b n)))
      atTop (𝓝 zeroLocationLaw) ∧
    Tendsto (fun n => resolvedSourceLaw (sizes n) (lengths n) (affineCylinder (G n) (b n)))
      atTop (𝓝 (labelledLaw false zeroLocationLaw)) := by
  obtain ⟨hp,ht,hi⟩ := location_inputs_under_rank_budget hAGG hLS hShorey hPNT hNR sizes lengths
    hsizes hlengths beta delta c hbeta hdelta hdeltaOne hc hupper hrare W G b hstack hbudget
  exact location_phase_atTop_of_errors sizes lengths (fun n => borderDeficitAt (G n) (lengths n))
    (fun n => affineCylinder (G n) (b n)) hsizes hlengths beta delta hdelta hdeltaOne hupper
    (Eventually.of_forall fun n => measurableSet_affineCylinder (G n) (b n)) hp ht hi hphase

/-- Negative infinite affine phase: all limiting location mass is in the uniform bulk. -/
theorem theorem_seven_ten_location_phase_atBot
    (hphase : Tendsto (fun n => affinePhase (sizes n) (lengths n)
      (borderDeficitAt (G n) (lengths n))) atTop atBot) :
    Tendsto (fun n => firstLocationLaw (sizes n) (lengths n) (affineCylinder (G n) (b n)))
      atTop (𝓝 unitIntervalLaw) ∧
    Tendsto (fun n => resolvedSourceLaw (sizes n) (lengths n) (affineCylinder (G n) (b n)))
      atTop (𝓝 (labelledLaw true unitIntervalLaw)) := by
  obtain ⟨hp,ht,hi⟩ := location_inputs_under_rank_budget hAGG hLS hShorey hPNT hNR sizes lengths
    hsizes hlengths beta delta c hbeta hdelta hdeltaOne hc hupper hrare W G b hstack hbudget
  exact location_phase_atBot_of_errors sizes lengths (fun n => borderDeficitAt (G n) (lengths n))
    (fun n => affineCylinder (G n) (b n)) hsizes hlengths beta delta hdelta hdeltaOne hupper
    (Eventually.of_forall fun n => measurableSet_affineCylinder (G n) (b n)) hp ht hi hphase

end
end PaperC.V282.AffineCrossoverLocationTheorem
