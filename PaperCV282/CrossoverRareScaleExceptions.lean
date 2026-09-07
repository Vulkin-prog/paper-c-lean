import PaperCV282.CrossoverRareScaleProbabilities

/-! # The actual microscopic interior and mesoscopic exceptions are negligible at the common rare scale -/
namespace PaperC.V282.CrossoverRareScaleExceptions

open Filter Topology MeasureTheory InfiniteRademacher InfiniteStartProbabilityTransfer AllStartSoftPoisson
open BulkPopulation BulkMarkedGeometry CrossoverMarkedTarget CrossoverBulkAtoms CrossoverRareScale
open MicroscopicBoundaryDominance MicroscopicNonvacancy RarePrefixEvents RarePrefixPoisson
open PrimeEulerPNT LaishramUniformInput PostQuadraticLiterature MesoscopicRareLimit

noncomputable section

/-- The complete interior first moment is controlled by the positive border summand alone. -/
theorem interior_mass_rare_scale_tendsto_zero
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeNumberTheoremRemainder)
    (sizes lengths : ℕ → ℕ) (hlengths : Tendsto lengths atTop atTop) (delta : ℝ) :
    Tendsto (fun n=>(∑ x∈Finset.Icc 2 (2*(lengths n)^2),infiniteStartProbability x (lengths n))/
      rareScale (sizes n) (lengths n) delta) atTop (𝓝 0) := by
  have ht := (interior_mass_relative_tendsto_zero hLS hShorey hPNT).comp hlengths
  apply squeeze_zero' (Eventually.of_forall fun _=>by
    exact div_nonneg (Finset.sum_nonneg fun _ _=>by exact ENNReal.toReal_nonneg) (rareScale_pos _ _ _).le)
    (Eventually.of_forall fun n=>?_) (by simpa only [Function.comp_def] using ht)
  apply div_le_div_of_nonneg_left (Finset.sum_nonneg fun _ _=>by exact ENNReal.toReal_nonneg)
    (by positivity : 0<((2 : ℝ)⁻¹)^Nat.primeCounting (lengths n))
  rw [rareScale,borderRate_coe]
  exact le_add_of_nonneg_right (by positivity)

theorem interior_probability_rare_scale_tendsto_zero
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeNumberTheoremRemainder)
    (sizes lengths : ℕ → ℕ) (hlengths : Tendsto lengths atTop atTop) (delta : ℝ) :
    Tendsto (fun n=>infiniteRademacherMeasure.real (interiorEvent (lengths n))/
      rareScale (sizes n) (lengths n) delta) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _=>div_nonneg measureReal_nonneg (rareScale_pos _ _ _).le)
    (Eventually.of_forall fun n=>div_le_div_of_nonneg_right (interior_probability_le_mass (lengths n))
      (rareScale_pos _ _ _).le)
    (interior_mass_rare_scale_tendsto_zero hLS hShorey hPNT sizes lengths hlengths delta)

/-- The mesoscopic term uses its already proved two-scale denominator, then the actual population ratio. -/
theorem middle_probability_rare_scale_tendsto_zero
    (hShorey : ShoreySquareProductStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop) (hlengths : Tendsto lengths atTop atTop)
    (beta delta : ℝ) (hbeta : 0<beta) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hrare : Tendsto (fun n=>(fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n=>infiniteRademacherMeasure.real (middleEvent (sizes n) (lengths n) delta)/
      rareScale (sizes n) (lengths n) delta) atTop (𝓝 0) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hsizes)
  have hu : ∀ᶠ n in atTop,(lengths n+1 : ℕ)≤(beta+1)*Real.log (sizes n) := by
    filter_upwards [hupper,hlog.eventually (eventually_ge_atTop (1 : ℝ))] with n hn hl
    dsimp only [Function.comp_def] at hl
    push_cast
    nlinarith
  have ht := proposition_seven_three_rare_negligibility (beta+1) delta (by linarith) hdelta hdeltaOne
    hShorey hPNT hNR sizes lengths hsizes hlengths hu hrare
  apply relative_zero_of_half_le
    (Eventually.of_forall fun _=>measureReal_nonneg) ?_ ?_ ht
  · filter_upwards [] with n
    have ha : 0<((2 : ℝ)⁻¹)^Nat.primeCounting (lengths n) := by positivity
    positivity
  · have hr := bulkRate_ratio_tendsto_one sizes lengths hsizes beta delta hdelta hdeltaOne hupper
      (hlengths.eventually (eventually_ge_atTop 1))
    filter_upwards [hr.eventually (lt_mem_nhds (by norm_num : (1/2 : ℝ)<1)),
      hsizes.eventually (eventually_ge_atTop 1)] with n hn hs
    have hp : 0<(fullRate (sizes n) (lengths n) : ℝ) := by
      change 0<(sizes n : ℝ)/(2 : ℝ)^lengths n
      positivity
    have hb := (lt_div_iff₀ hp).mp hn
    have ha : 0≤((2 : ℝ)⁻¹)^Nat.primeCounting (lengths n) := by positivity
    rw [rareScale,borderRate_coe,totalRate_bulk_eq]
    change _≤((2 : ℝ)⁻¹)^Nat.primeCounting (lengths n)+(bulkRate (sizes n) (lengths n) delta : ℝ)
    change (1/2)*(fullRate (sizes n) (lengths n) : ℝ)<_ at hb
    change (_+(fullRate (sizes n) (lengths n) : ℝ))/2≤_
    linarith

/-- Both genuine exceptional events, with no limiting border/bulk phase assumption. -/
theorem exceptions_rare_scale_tendsto_zero
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeNumberTheoremRemainder) (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop) (hlengths : Tendsto lengths atTop atTop)
    (beta delta : ℝ) (hbeta : 0<beta) (hdelta : 0<delta) (hdeltaOne : delta<1)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hrare : Tendsto (fun n=>(fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n=>(infiniteRademacherMeasure.real (interiorEvent (lengths n))+
      infiniteRademacherMeasure.real (middleEvent (sizes n) (lengths n) delta))/
        rareScale (sizes n) (lengths n) delta) atTop (𝓝 0) := by
  have hi := interior_probability_rare_scale_tendsto_zero hLS hShorey hPNT sizes lengths hlengths delta
  have hm := middle_probability_rare_scale_tendsto_zero hShorey hPNT hNR sizes lengths hsizes hlengths
    beta delta hbeta hdelta hdeltaOne hupper hrare
  simpa only [add_zero,add_div] using hi.add hm

end
end PaperC.V282.CrossoverRareScaleExceptions
