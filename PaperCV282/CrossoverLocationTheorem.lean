import PaperCV282.CrossoverLocationTransfer
import PaperCV282.CrossoverLocationExtreme
import PaperCV282.CrossoverMarkedConvergence

/-! # The actual conditional first-location limit, equation (7.19)

The marked approximation is established internally by Theorem 7.9, then
contracted to the genuine first contained start. The result includes arbitrary
subsequences and both infinite phase endpoints.
-/
namespace PaperC.V282.CrossoverLocationTheorem

open MeasureTheory Filter Topology AllStartSoftPoisson CrossoverLocationPhase CrossoverLocationMixture
open CrossoverLocationGrid CrossoverLocationProjection CrossoverLocationTransfer CrossoverLocationExtreme
open CrossoverMarkedConvergence RarePrefixMass PrimeEulerPNT ProcessAGGInput
open LaishramUniformInput PostQuadraticLiterature

noncomputable section

/-- Equation (7.19), with the true law of firstStart/M conditional on non-vacancy. -/
theorem equation_seven_nineteen
    (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (sizes lengths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop) (hlengths : Tendsto lengths atTop atTop)
    (beta delta : ℝ) (hbeta : 0<beta) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hrare : Tendsto (fun n => (fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0))
    (s : ℝ) (hphase : Tendsto (fun n => crossoverPhase (sizes n) (lengths n)) atTop (𝓝 s)) :
    Tendsto (fun n => firstLocationLaw (sizes n) (lengths n)) atTop (𝓝 (crossoverLimitLaw s)) := by
  exact firstLocation_phase_limit_of_actualDistance sizes lengths hsizes beta delta hdelta hdeltaOne hupper
    (hlengths.eventually (eventually_ge_atTop 1))
    (theorem_seven_nine hAGG hPNT hLS hShorey hNR sizes lengths hsizes hlengths beta delta hbeta hdelta
      hdeltaOne hupper hrare) s hphase

/-- The positive-infinite phase endpoint: the first contained start is microscopic. -/
theorem equation_seven_nineteen_phase_atTop
    (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (sizes lengths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop) (hlengths : Tendsto lengths atTop atTop)
    (beta delta : ℝ) (hbeta : 0<beta) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hrare : Tendsto (fun n => (fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0))
    (hphase : Tendsto (fun n => crossoverPhase (sizes n) (lengths n)) atTop atTop) :
    Tendsto (fun n => firstLocationLaw (sizes n) (lengths n)) atTop (𝓝 zeroLocationLaw) := by
  apply firstLocationLaw_tendsto_of_actualDistance sizes lengths delta
    (logarithmic_lengths_eventually_contained sizes lengths hsizes beta hupper)
    (theorem_seven_nine hAGG hPNT hLS hShorey hNR sizes lengths hsizes hlengths beta delta hbeta hdelta
      hdeltaOne hupper hrare)
  exact physicalLocationMixtureLaw_tendsto_border sizes lengths hsizes beta delta hdelta hdeltaOne hupper
    (hlengths.eventually (eventually_ge_atTop 1)) hphase

/-- The negative-infinite phase endpoint: the first contained start is asymptotically uniform. -/
theorem equation_seven_nineteen_phase_atBot
    (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (sizes lengths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop) (hlengths : Tendsto lengths atTop atTop)
    (beta delta : ℝ) (hbeta : 0<beta) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hrare : Tendsto (fun n => (fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0))
    (hphase : Tendsto (fun n => crossoverPhase (sizes n) (lengths n)) atTop atBot) :
    Tendsto (fun n => firstLocationLaw (sizes n) (lengths n)) atTop (𝓝 unitIntervalLaw) := by
  apply firstLocationLaw_tendsto_of_actualDistance sizes lengths delta
    (logarithmic_lengths_eventually_contained sizes lengths hsizes beta hupper)
    (theorem_seven_nine hAGG hPNT hLS hShorey hNR sizes lengths hsizes hlengths beta delta hbeta hdelta
      hdeltaOne hupper hrare)
  exact physicalLocationMixtureLaw_tendsto_bulk sizes lengths hsizes beta delta hdelta hdeltaOne hupper
    (hlengths.eventually (eventually_ge_atTop 1)) hphase

end
end PaperC.V282.CrossoverLocationTheorem
