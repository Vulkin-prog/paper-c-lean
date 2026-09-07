import PaperCV282.AffineCrossoverCensored
import PaperCV282.AffineCrossoverUncappingTheorem
import PaperCV282.AffineCrossoverLocationTheorem

/-! # The right-censored affine crossover under the actual rank budget

Censoring only the bulk excess leaves the limiting complete target unchanged.
The source law is literally conditioned on A intersected with non-vacancy.
-/
namespace PaperC.V282.AffineCrossoverCensoredTheorem

open MeasureTheory ProbabilityTheory Filter Topology InfiniteRademacher Affine
open AffineCrossoverErrorsAffine AffineCrossoverModel AffineCrossoverCylinder
open AffineCrossoverTheorem AffineCrossoverUncappingTheorem AffineCrossoverLocationTheorem
open AffineCrossoverCensored AffineCrossoverFutureCutoff AffineBorderCylinders
open RarePrefixGeometry CrossoverCensored BulkMarkedGeometry CrossoverRareScaleProbabilities
open HardPoissonRates AllStartSoftPoisson PrimeEulerPNT ProcessAGGInput SaddleParameters SaddleScales
open LaishramUniformInput PostQuadraticLiterature SharpConditioning
open scoped NNReal

noncomputable section
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

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

/-- The complete affine marked comparison also holds for the true right-censored source. -/
theorem theorem_seven_ten_censored
    (hneutral : ∀ K,∀ᶠ n in atTop,FutureNeutralAt (G n) (lengths n) K) :
    Tendsto (fun n => AffineCrossoverCensored.censoredDistance (sizes n) (lengths n) delta
      (affineCylinder (G n) (b n)) (conditionalBorderRate (affineCylinder (G n) (b n)) (lengths n)))
      atTop (𝓝 0) := by
  have ht := theorem_seven_ten_complete_clock hAGG hLS hShorey hPNT hNR sizes lengths
    hsizes hlengths beta delta c hbeta hdelta hdeltaOne hc hupper hrare W G b hstack hbudget hneutral
  have hi := inverse_bulk_card_tendsto_zero sizes lengths hsizes beta delta hdelta hdeltaOne hupper
    (hlengths.eventually (eventually_ge_atTop 1))
  obtain ⟨hp,_,_⟩ := location_inputs_under_rank_budget hAGG hLS hShorey hPNT hNR sizes lengths
    hsizes hlengths beta delta c hbeta hdelta hdeltaOne hc hupper hrare W G b hstack hbudget
  apply squeeze_zero' ?_ ?_ (by simpa only [add_zero] using ht.add hi)
  · filter_upwards [hp] with n hpn
    letI _instProbabilitySource := AffineCrossoverLocationTransfer.sourceLaw_probability delta
      (measurableSet_affineCylinder (G n) (b n)) hpn
    letI _instProbabilityCensored := Measure.isProbabilityMeasure_map
      (μ := sourceLaw (conditionedMeasure (affineCylinder (G n) (b n))) (sizes n) (lengths n) delta)
      (measurable_of_countable (censorRecord (sizes n) (lengths n))).aemeasurable
    rw [AffineCrossoverCensored.censoredDistance,censoredSourceLaw_eq _ _ _ (measurableSet_affineCylinder (G n) (b n))]
    exact measureTotalVariation_nonneg _ _
  · filter_upwards [hp,bulk_nonempty_eventually sizes lengths hsizes beta delta hdelta hdeltaOne hupper
      (hlengths.eventually (eventually_ge_atTop 1))] with n hpn hn
    exact AffineCrossoverCensored.censoredDistance_le delta
      (conditionalBorderRate (affineCylinder (G n) (b n)) (lengths n))
      (measurableSet_affineCylinder (G n) (b n)) hpn hn

end
end PaperC.V282.AffineCrossoverCensoredTheorem
