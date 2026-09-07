import PaperCV282.AffineCrossoverErrorsScales
import PaperCV282.CrossoverRareScaleExceptions

/-! # Actual microscopic interior errors survive hard conditioning

The quantitative prime surplus is used before multiplying by the information
factor. A previously qualitative small-o estimate is never rescaled.
-/
namespace PaperC.V282.AffineCrossoverErrorsInterior

open Filter Topology MeasureTheory InfiniteRademacher InfiniteStartProbabilityTransfer
open MicroscopicInteriorBounds HarmonicIncidenceSurplus LaishramUniformInput PostQuadraticLiterature
open PrimeEulerPNT AffineCrossoverErrorsScales AffineCrossoverBudget SaddleParameters SaddleScales
open MicroscopicNonvacancy CrossoverRareScale
open RarePrefixEvents RarePrefixPoisson CrossoverMarkedTarget AllStartSoftPoisson BulkMarkedConvergence

noncomputable section

/-- The true interior probability has a fixed strict surplus relative to the exact border mass. -/
theorem interior_relative_prime_bound_eventually
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeNumberTheoremRemainder) :
    ∃ Lzero : ℕ, ∀ L≥Lzero,
      infiniteRademacherMeasure.real (interiorEvent L)/(borderRate L : ℝ) ≤
        (2 : ℝ)^(-(1/12 : ℝ)*Nat.primeCounting L) := by
  have hstar : (1/12 : ℝ)<(surplus 11 : ℝ) := by rw [surplus_eleven_eq];norm_num
  obtain ⟨Lzero,hzero⟩ := theorem_seven_one_interior_sum hLS hShorey hPNT (by norm_num : (0 : ℝ)<1/12) hstar
  refine ⟨Lzero,?_⟩
  intro L hL
  have hprob := (interior_probability_le_mass L).trans (hzero L hL)
  apply (div_le_div_of_nonneg_right hprob (show 0≤(borderRate L : ℝ) by positivity)).trans
  rw [borderRate_coe,inv_pow,div_inv_eq_mul,← Real.rpow_natCast,← Real.rpow_add (by norm_num : (0 : ℝ)<2)]
  exact le_of_eq (by congr 1;ring)

/-- A common size threshold precedes the length and the information parameter. -/
theorem weighted_interior_bound_eventually
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax : ℝ) (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ,
      betaMin*Real.log M≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log M →
      ∀ I : ℝ, I≤saddleCutoff 1 (Real.log M) →
      Real.exp I * infiniteRademacherMeasure.real (interiorEvent L)/(borderRate L : ℝ) ≤
        Real.exp (-((1/12 : ℝ)*betaMin*Real.log 2/16)*(Real.log M/Real.log (Real.log M))) := by
  obtain ⟨Li,hi⟩ := interior_relative_prime_bound_eventually hLS hShorey hPNT
  obtain ⟨Mp,hp⟩ := information_weighted_prime_margin_eventually hPNT betaMin betaMax (1/12)
    hbetaMin hbeta (by norm_num)
  obtain ⟨Ma,ha⟩ := CriticalWeightedDefect.admissible_eventually hbetaMin hbeta
  obtain ⟨Mh,hh⟩ := CriticalWeightedDefect.height_tends_to_infinity (c₂ := betaMax) hbetaMin (Li+1)
  refine ⟨max Mp (max Ma Mh),?_⟩
  intro M hM L hlo hhi I hI
  have hL := hh M (by omega) (L+1) (ha M (by omega) (L+1)
    ⟨hbetaMin,hbeta,by simpa using hlo,by simpa using hhi⟩)
  have hb := mul_le_mul_of_nonneg_left (hi L (by omega)) (Real.exp_nonneg I)
  rw [← mul_div_assoc] at hb
  exact hb.trans (hp M (by omega) L hlo hhi I hI)

/-- Multiplying the raw border mass by exp(I) still leaves an explicit deep error. -/
theorem weighted_border_bound_eventually
    (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax : ℝ) (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ,
      betaMin*Real.log M≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log M →
      ∀ I : ℝ, I≤saddleCutoff 1 (Real.log M) →
      Real.exp I * (borderRate L : ℝ) ≤
        Real.exp (-(betaMin*Real.log 2/16)*(Real.log M/Real.log (Real.log M))) := by
  obtain ⟨Mzero,hzero⟩ := information_weighted_prime_margin_eventually hPNT betaMin betaMax 1
    hbetaMin hbeta (by norm_num)
  refine ⟨Mzero,?_⟩
  intro M hM L hlo hhi I hI
  have h := hzero M hM L hlo hhi I hI
  simpa only [one_mul,neg_one_mul,Real.rpow_neg (by norm_num : (0 : ℝ)≤2),Real.rpow_natCast,
    borderRate_coe,inv_pow] using h

/-- The rare-intensity condition supplies the lower band before the weighted estimates are applied. -/
theorem weighted_interior_and_border_tendsto_zero
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hPNT : PrimeNumberTheoremRemainder)
    (sizes lengths : ℕ→ℕ) (hsizes : Tendsto sizes atTop atTop)
    (beta : ℝ) (hbeta : 0<beta)
    (hupper : ∀ᶠ n in atTop,(lengths n : ℝ)≤beta*Real.log (sizes n))
    (hrare : Tendsto (fun n => (fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0))
    (I : ℕ→ℝ) (hI : ∀ᶠ n in atTop,I n≤saddleCutoff 1 (Real.log (sizes n))) :
    Tendsto (fun n => Real.exp (I n)*infiniteRademacherMeasure.real (interiorEvent (lengths n))/
      (borderRate (lengths n) : ℝ)) atTop (𝓝 0) ∧
    Tendsto (fun n => Real.exp (I n)*(borderRate (lengths n) : ℝ)) atTop (𝓝 0) := by
  obtain ⟨Mi,hi⟩ := weighted_interior_bound_eventually hLS hShorey hPNT (1/2) (beta+1)
    (by norm_num) (by linarith)
  obtain ⟨Mb,hb⟩ := weighted_border_bound_eventually hPNT (1/2) (beta+1) (by norm_num) (by linarith)
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hsizes)
  have hband : ∀ᶠ n in atTop,(1/2 : ℝ)*Real.log (sizes n)≤(lengths n+1 : ℝ) ∧
      (lengths n+1 : ℝ)≤(beta+1)*Real.log (sizes n) := by
    filter_upwards [hupper,hrare.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1)),
      hlog.eventually (eventually_ge_atTop (1 : ℝ)),hsizes.eventually (eventually_ge_atTop 1)] with n hu hr hl hn
    exact rare_window_band hn hl hbeta hu hr.le
  constructor
  · apply squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_
      ((prime_margin_error_tendsto_zero (1/2) (1/12) (by norm_num) (by norm_num)).comp hsizes)
    filter_upwards [hband,hI,hsizes.eventually (eventually_ge_atTop Mi)] with n hbn hin hn
    exact hi (sizes n) hn (lengths n) hbn.1 hbn.2 (I n) hin
  · have he := (prime_margin_error_tendsto_zero (1/2) 1 (by norm_num) (by norm_num)).comp hsizes
    simp only [one_mul] at he
    apply squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_ he
    filter_upwards [hband,hI,hsizes.eventually (eventually_ge_atTop Mb)] with n hbn hin hn
    exact hb (sizes n) hn (lengths n) hbn.1 hbn.2 (I n) hin

end
end PaperC.V282.AffineCrossoverErrorsInterior
