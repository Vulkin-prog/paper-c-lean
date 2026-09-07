import PaperCV282.CrossoverResolvedLocationSource
import PaperCV282.CrossoverMarkedConvergence

/-! # The source-resolved clause of Theorem 7.8, for all three phase limits -/
namespace PaperC.V282.CrossoverResolvedLocationTheorem

open MeasureTheory Filter Topology CrossoverLocationPhase CrossoverLocationMixture CrossoverLocationGrid
open CrossoverLocationExtreme CrossoverResolvedLocationTarget CrossoverResolvedLocationSource
open CrossoverMarkedConvergence CrossoverMarkedTarget BulkMarkedGeometry BulkPopulation CrossoverBulkAtoms
open PrimeEulerPNT ProcessAGGInput LaishramUniformInput PostQuadraticLiterature AllStartSoftPoisson

open scoped NNReal ENNReal

noncomputable section

/-- The source approximation and the vanishing conditioned interior error are both proved here. -/
theorem resolved_limit_of_weights
    (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (sizes lengths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop) (hlengths : Tendsto lengths atTop atTop)
    (beta delta : ℝ) (hbeta : 0<beta) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hrare : Tendsto (fun n => (fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0))
    (a b : ℝ≥0) (hab : a+b=1)
    (ha : Tendsto (fun n => (borderWeight (bulkStarts (sizes n) (lengths n) delta) (lengths n) : ℝ)) atTop (𝓝 (a : ℝ)))
    (hb : Tendsto (fun n => (bulkWeight (bulkStarts (sizes n) (lengths n) delta) (lengths n) : ℝ)) atTop (𝓝 (b : ℝ))) :
    Tendsto (fun n => resolvedSourceLaw (sizes n) (lengths n)) atTop
      (𝓝 (resolvedMixture a b hab zeroLocationLaw unitIntervalLaw)) := by
  apply resolvedSourceLaw_tendsto_of_errors sizes lengths delta
    (RarePrefixMass.logarithmic_lengths_eventually_contained sizes lengths hsizes beta hupper)
    (hlengths.eventually (eventually_ge_atTop 1))
    (theorem_seven_nine hAGG hPNT hLS hShorey hNR sizes lengths hsizes hlengths beta delta hbeta hdelta hdeltaOne hupper hrare)
    (conditionalInteriorProbability_tendsto_zero hAGG hPNT hLS hShorey hNR sizes lengths hsizes hlengths
      beta delta hbeta hdelta hdeltaOne hupper hrare)
  exact resolvedTargetLaw_tendsto_of_weights sizes lengths hsizes hlengths beta delta hdelta hdeltaOne hupper a b hab ha hb

/-- The source label is retained, with true microscopic x/L² and bulk x/M locations. -/
theorem equation_seven_nineteen_resolved
    (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (sizes lengths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop) (hlengths : Tendsto lengths atTop atTop)
    (beta delta : ℝ) (hbeta : 0<beta) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hrare : Tendsto (fun n => (fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0))
    (s : ℝ) (hphase : Tendsto (fun n => crossoverPhase (sizes n) (lengths n)) atTop (𝓝 s)) :
    Tendsto (fun n => resolvedSourceLaw (sizes n) (lengths n)) atTop (𝓝 (resolvedLimitLaw s)) := by
  obtain ⟨ha,hb⟩ := mixture_weights_tendsto sizes lengths hsizes beta delta hdelta hdeltaOne hupper
    (hlengths.eventually (eventually_ge_atTop 1)) s hphase
  apply resolved_limit_of_weights hAGG hPNT hLS hShorey hNR sizes lengths hsizes hlengths beta delta
    hbeta hdelta hdeltaOne hupper hrare (phaseBorderWeight s) (phaseBulkWeight s) (phase_weights_sum s)
  · change Tendsto _ atTop (𝓝 (1/(1+(2 : ℝ)^(-s))))
    convert ha using 1
    funext n
    simp only [borderWeight,borderRate,totalRate,bulkRate,FiniteStartMaskAverages.maskRate,
      NNReal.coe_div,NNReal.coe_add,NNReal.coe_pow,NNReal.coe_ofNat,inv_pow,one_div]
    rfl
  · change Tendsto _ atTop (𝓝 ((2 : ℝ)^(-s)/(1+(2 : ℝ)^(-s))))
    convert hb using 1
    funext n
    simp only [bulkWeight,borderRate,totalRate,bulkRate,FiniteStartMaskAverages.maskRate,
      NNReal.coe_div,NNReal.coe_add,NNReal.coe_pow,NNReal.coe_ofNat,inv_pow,one_div]
    rfl

/-- The degenerate microscopic limit keeps the microscopic source label. -/
theorem equation_seven_nineteen_resolved_phase_atTop
    (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (sizes lengths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop) (hlengths : Tendsto lengths atTop atTop)
    (beta delta : ℝ) (hbeta : 0<beta) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hrare : Tendsto (fun n => (fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0))
    (hphase : Tendsto (fun n => crossoverPhase (sizes n) (lengths n)) atTop atTop) :
    Tendsto (fun n => resolvedSourceLaw (sizes n) (lengths n)) atTop
      (𝓝 (labelledLaw false zeroLocationLaw)) := by
  have ha := borderWeight_tendsto_one_of_phase_atTop sizes lengths hsizes beta delta hdelta hdeltaOne hupper
    (hlengths.eventually (eventually_ge_atTop 1)) hphase
  have hb := bulkWeight_tendsto_of_borderWeight (fun n => bulkStarts (sizes n) (lengths n) delta) lengths 1 ha
  have ht := resolved_limit_of_weights hAGG hPNT hLS hShorey hNR sizes lengths hsizes hlengths beta delta
    hbeta hdelta hdeltaOne hupper hrare 1 0 (by norm_num) ha (by simpa using hb)
  have he : resolvedMixture 1 0 (by norm_num) zeroLocationLaw unitIntervalLaw=labelledLaw false zeroLocationLaw := by
    apply Subtype.ext
    simp [resolvedMixture]
  rwa [he] at ht

/-- The degenerate uniform limit keeps the bulk source label. -/
theorem equation_seven_nineteen_resolved_phase_atBot
    (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (sizes lengths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop) (hlengths : Tendsto lengths atTop atTop)
    (beta delta : ℝ) (hbeta : 0<beta) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hrare : Tendsto (fun n => (fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0))
    (hphase : Tendsto (fun n => crossoverPhase (sizes n) (lengths n)) atTop atBot) :
    Tendsto (fun n => resolvedSourceLaw (sizes n) (lengths n)) atTop
      (𝓝 (labelledLaw true unitIntervalLaw)) := by
  have ha := borderWeight_tendsto_zero_of_phase_atBot sizes lengths hsizes beta delta hdelta hdeltaOne hupper
    (hlengths.eventually (eventually_ge_atTop 1)) hphase
  have hb := bulkWeight_tendsto_of_borderWeight (fun n => bulkStarts (sizes n) (lengths n) delta) lengths 0 ha
  have ht := resolved_limit_of_weights hAGG hPNT hLS hShorey hNR sizes lengths hsizes hlengths beta delta
    hbeta hdelta hdeltaOne hupper hrare 0 1 (by norm_num) ha (by simpa using hb)
  have he : resolvedMixture 0 1 (by norm_num) zeroLocationLaw unitIntervalLaw=labelledLaw true unitIntervalLaw := by
    apply Subtype.ext
    simp [resolvedMixture]
  rwa [he] at ht

end
end PaperC.V282.CrossoverResolvedLocationTheorem
