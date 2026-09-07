import PaperCV282.AffineCrossoverTheorem
import PaperCV282.AffineCrossoverDeficit
import PaperCV282.AffineCrossoverUncappingLimit

/-! # The complete affine-conditioned marked law under finite future neutrality

The arithmetic rank budget proves every fixed-cap comparison. The separate
future row-space neutrality assumption proves the exact conditional geometric
clock at each fixed cap. Removing the cap gives the complete marked law;
no uniform condition on infinitely many future primes is imposed.
-/
namespace PaperC.V282.AffineCrossoverUncappingTheorem

open MeasureTheory ProbabilityTheory Filter Topology InfiniteRademacher Affine
open AffineCrossoverErrorsAffine AffineCrossoverModel AffineCrossoverCylinder
open AffineCrossoverDeficit AffineCrossoverTheorem AffineCrossoverUncappingLimit
open AffineCrossoverFutureCutoff AffineBorderCylinders
open RarePrefixGeometry MicroscopicBorderEvents HardPoissonRates AllStartSoftPoisson
open PrimeEulerPNT ProcessAGGInput SaddleParameters SaddleScales
open LaishramUniformInput PostQuadraticLiterature
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

/-- Full marked comparison with the true conditional border probability. -/
theorem theorem_seven_ten_complete_clock
    (hneutral : ∀ K,∀ᶠ n in atTop,FutureNeutralAt (G n) (lengths n) K) :
    let A := fun n => affineCylinder (G n) (b n)
    let alpha := fun n => conditionalBorderRate (A n) (lengths n)
    Tendsto (fun n => actualDistance (conditionedMeasure (A n)) (sizes n) (lengths n) delta (alpha n))
      atTop (𝓝 0) := by
  dsimp only
  have hp : ∀ᶠ n in atTop,IsProbabilityMeasure (conditionedMeasure (affineCylinder (G n) (b n))) := by
    filter_upwards [hstack] with n hn
    obtain ⟨hLY,hs⟩ := hn
    exact conditionedMeasure_probability _ (affineCylinder_probability_pos _ _
      (stacked_compatible_implies_compatible _ _ hLY hs))
  have hb : ∀ᶠ n in atTop,
      0 < (conditionedMeasure (affineCylinder (G n) (b n))).real (borderEvent (lengths n)) := by
    filter_upwards [hstack] with n hn
    obtain ⟨hLY,hs⟩ := hn
    change 0 < (conditionalBorderRate (affineCylinder (G n) (b n)) (lengths n) : ℝ)
    rw [conditionalBorderRate_eq _ _ hLY hs]
    exact_mod_cast AffineCrossoverCylinder.borderRate_pos (G n) hLY
  exact actualDistance_tendsto_of_capped
    (fun n => conditionedMeasure (affineCylinder (G n) (b n))) sizes lengths
    (fun n => conditionalBorderRate (affineCylinder (G n) (b n)) (lengths n)) delta hp
    (RarePrefixMass.logarithmic_lengths_eventually_contained sizes lengths hsizes beta hupper) hb
    (fun K => capped_clock_law_eventually (fun n => hardCutoff (sizes n)) lengths G b hstack hneutral (K+1))
    (fun K => theorem_seven_ten_fixed_cap hAGG hLS hShorey hPNT hNR sizes lengths
      hsizes hlengths beta delta c hbeta hdelta hdeltaOne hc hupper hrare W G b hstack hbudget hneutral K)

/-- The same complete law, with its printed exact rate alpha = 2^(-d). -/
theorem theorem_seven_ten_complete_clock_deficit
    (hneutral : ∀ K,∀ᶠ n in atTop,FutureNeutralAt (G n) (lengths n) K) :
    Tendsto (fun n => actualDistance (conditionedMeasure (affineCylinder (G n) (b n)))
      (sizes n) (lengths n) delta (((2 : ℝ≥0)⁻¹)^borderDeficitAt (G n) (lengths n)))
      atTop (𝓝 0) := by
  have ht := theorem_seven_ten_complete_clock hAGG hLS hShorey hPNT hNR sizes lengths
    hsizes hlengths beta delta c hbeta hdelta hdeltaOne hc hupper hrare W G b hstack hbudget hneutral
  apply ht.congr'
  filter_upwards [hstack] with n hn
  obtain ⟨hLY,hs⟩ := hn
  rw [conditionalBorderRate_eq_deficit (G n) (b n) hLY hs]

end
end PaperC.V282.AffineCrossoverUncappingTheorem
