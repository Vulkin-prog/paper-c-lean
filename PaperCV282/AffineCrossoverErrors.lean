import PaperCV282.AffineCrossoverErrorsMiddle
import PaperCV282.AffineCrossoverStable

/-! # Genuine conditional probabilities of the discarded sources

These estimates are valid for every positive measurable information event.
Affine rank identities may enlarge the denominators afterwards.
-/
namespace PaperC.V282.AffineCrossoverErrors

open MeasureTheory ProbabilityTheory Filter Topology InfiniteRademacher
open AffineCrossoverBudget AffineCrossoverErrorsInterior AffineCrossoverErrorsMiddle
open RareConditioningRates SaddleParameters SaddleScales CrossoverMarkedTarget CrossoverRareScale
open MicroscopicNonvacancy MicroscopicBorderEvents RarePrefixEvents AllStartSoftPoisson
open PrimeEulerPNT LaishramUniformInput PostQuadraticLiterature ConditionedCountableLaw

noncomputable section
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- Conditioning a true event loses at most one inverse information probability. -/
theorem conditional_probability_le_information (A E : Set InfiniteSample) (hA : MeasurableSet A)
    (hpos : 0 < infiniteRademacherMeasure.real A) :
    (cond infiniteRademacherMeasure A).real E≤
      Real.exp (eventInformation A)*infiniteRademacherMeasure.real E := by
  rw [SharpConditioning.cond_real_apply _ A hA]
  apply (div_le_div_of_nonneg_right (measureReal_mono Set.inter_subset_right) hpos.le).trans
  rw [div_eq_mul_inv,← exp_eventInformation A hpos]
  exact le_of_eq (mul_comm _ _)

/-- All three weighted errors vanish under the original hard information budget. -/
theorem weighted_errors_under_budget
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeNumberTheoremRemainder) (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (sizes lengths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop) (hlengths : Tendsto lengths atTop atTop)
    (beta delta c : ℝ) (hbeta : 0<beta) (hdelta : 0<delta) (hdeltaOne : delta<1) (hc : 0<c)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hrare : Tendsto (fun n => (fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0))
    (I : ℕ→ℝ) (hbudget : ∀ᶠ n in atTop,I n≤saddleCutoff 1 (Real.log (sizes n))-
      c*saddleNu 1 (Real.log (sizes n))) :
    Tendsto (fun n => Real.exp (I n)*infiniteRademacherMeasure.real (interiorEvent (lengths n))/
      (borderRate (lengths n) : ℝ)) atTop (𝓝 0) ∧
    Tendsto (fun n => Real.exp (I n)*infiniteRademacherMeasure.real (middleEvent (sizes n) (lengths n) delta)/
      rareScale (sizes n) (lengths n) delta) atTop (𝓝 0) ∧
    Tendsto (fun n => Real.exp (I n)*(borderRate (lengths n) : ℝ)) atTop (𝓝 0) := by
  obtain ⟨Mzero,hzero⟩ := information_le_saddle_eventually hc
  have hI : ∀ᶠ n in atTop,I n≤saddleCutoff 1 (Real.log (sizes n)) := by
    filter_upwards [hbudget,hsizes.eventually (eventually_ge_atTop Mzero)] with n hn hM
    exact hzero (sizes n) hM (I n) hn
  have h := weighted_interior_and_border_tendsto_zero hLS hShorey hPNT sizes lengths hsizes
    beta hbeta hupper hrare I hI
  exact ⟨h.1,weighted_middle_rare_scale_tendsto_zero hShorey hPNT hNR sizes lengths hsizes hlengths
    beta delta hbeta hdelta hdeltaOne hupper hrare I hI,h.2⟩

/-- The actual conditional discarded probabilities have the same relative zero limits. -/
theorem conditional_errors_under_budget
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeNumberTheoremRemainder) (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (sizes lengths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop) (hlengths : Tendsto lengths atTop atTop)
    (beta delta c : ℝ) (hbeta : 0<beta) (hdelta : 0<delta) (hdeltaOne : delta<1) (hc : 0<c)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hrare : Tendsto (fun n => (fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0))
    (A : ℕ→Set InfiniteSample) (hA : ∀ᶠ n in atTop,MeasurableSet (A n))
    (hpos : ∀ᶠ n in atTop,0 < infiniteRademacherMeasure.real (A n))
    (hbudget : ∀ᶠ n in atTop,eventInformation (A n)≤saddleCutoff 1 (Real.log (sizes n))-
      c*saddleNu 1 (Real.log (sizes n))) :
    Tendsto (fun n => (cond infiniteRademacherMeasure (A n)).real (interiorEvent (lengths n))/
      (borderRate (lengths n) : ℝ)) atTop (𝓝 0) ∧
    Tendsto (fun n => (cond infiniteRademacherMeasure (A n)).real (middleEvent (sizes n) (lengths n) delta)/
      rareScale (sizes n) (lengths n) delta) atTop (𝓝 0) ∧
    Tendsto (fun n => (cond infiniteRademacherMeasure (A n)).real (borderEvent (lengths n))) atTop (𝓝 0) := by
  obtain ⟨hi,hm,hb⟩ := weighted_errors_under_budget hLS hShorey hPNT hNR sizes lengths hsizes hlengths
    beta delta c hbeta hdelta hdeltaOne hc hupper hrare (fun n => eventInformation (A n)) hbudget
  refine ⟨?_,?_,?_⟩
  · apply squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_ hi
    filter_upwards [hA,hpos] with n hn hp
    exact div_le_div_of_nonneg_right (conditional_probability_le_information _ _ hn hp) (by positivity)
  · apply squeeze_zero' (Eventually.of_forall fun _ => div_nonneg measureReal_nonneg (rareScale_pos _ _ _).le) ?_ hm
    filter_upwards [hA,hpos] with n hn hp
    exact div_le_div_of_nonneg_right (conditional_probability_le_information _ _ hn hp) (rareScale_pos _ _ _).le
  · apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_ hb
    filter_upwards [hA,hpos] with n hn hp
    have h := conditional_probability_le_information (A n) (borderEvent (lengths n)) hn hp
    simpa only [equation_seven_one,borderRate_coe] using h

end
end PaperC.V282.AffineCrossoverErrors
