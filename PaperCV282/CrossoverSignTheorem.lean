import PaperCV282.CrossoverMarkedConvergence
import PaperCV282.CrossoverSignComparison

/-! # Theorem 7.9's sign bias for the actual least contained start -/
namespace PaperC.V282.CrossoverSignTheorem

open Filter Topology MeasureTheory ProbabilityTheory InfiniteRademacher AllStartSoftPoisson
open CrossoverMarkedConvergence CrossoverSignComparison CrossoverSourceSigns CrossoverMovingTarget
open CrossoverMarkedTarget CrossoverBulkAtoms CrossoverRareScaleProbabilities BulkMarkedGeometry
open RarePrefixMass RarePrefixGeometry PrimeEulerPNT ProcessAGGInput LaishramUniformInput PostQuadraticLiterature

noncomputable section

/-- This is the actual probability of f(X*)=+1; zero denotes positive in F₂ coordinates. -/
def positiveProbability (M L : ℕ) : ℝ :=
  (cond infiniteRademacherMeasure (hitEvent M L)).real {omega | positiveSource M L omega=true}

/-- No relative phase limit is needed for the moving sign-bias formula. -/
theorem theorem_seven_nine_sign
    (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop) (hlengths : Tendsto lengths atTop atTop)
    (beta delta : ℝ) (hbeta : 0 < beta) (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hupper : ∀ᶠ n in atTop, (lengths n : ℝ) ≤ beta*Real.log (sizes n))
    (hrare : Tendsto (fun n => (fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => positiveProbability (sizes n) (lengths n)-
      ((borderRate (lengths n) : ℝ)+(totalRate (bulkStarts (sizes n) (lengths n) delta) (lengths n) : ℝ)/2)/
        ((borderRate (lengths n) : ℝ)+(totalRate (bulkStarts (sizes n) (lengths n) delta) (lengths n) : ℝ)))
      atTop (𝓝 0) := by
  have ht := theorem_seven_nine hAGG hPNT hLS hShorey hNR sizes lengths hsizes hlengths
    beta delta hbeta hdelta hdeltaOne hupper hrare
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (by simpa only [mul_zero] using ht.const_mul 2)
  filter_upwards [logarithmic_lengths_eventually_contained sizes lengths hsizes beta hupper,
    bulk_nonempty_eventually sizes lengths hsizes beta delta hdelta hdeltaOne hupper
      (hlengths.eventually (eventually_ge_atTop 1))] with n hc hn
  simpa only [Real.norm_eq_abs,positiveProbability] using positive_source_probability_error_le hc hn

end
end PaperC.V282.CrossoverSignTheorem
