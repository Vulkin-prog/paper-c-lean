import PaperCV282.RarePrefixMassBounds
import PaperCV282.MicroscopicBoundaryDominance

/-! # Theorem 7.8: the actual rare prefix non-vacancy probability -/
namespace PaperC.V282.RarePrefixMass

open Filter Topology MeasureTheory InfiniteRademacher InfiniteStartProbabilityTransfer
open RarePrefixGeometry RarePrefixPoisson RarePrefixEvents RarePrefixMassBounds RarePrefixSubsequence
open BulkPopulation AllStartSoftPoisson MicroscopicNonvacancy MicroscopicBoundaryDominance
open PrimeEulerPNT ProcessAGGInput LaishramUniformInput PostQuadraticLiterature MesoscopicRareLimit

noncomputable section
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

/-- The exact border mass tends to zero, independently of any relative phase. -/
theorem border_probability_tendsto_zero (lengths : ℕ → ℕ) (hlengths : Tendsto lengths atTop atTop) :
    Tendsto (fun n => ((2 : ℝ)⁻¹)^Nat.primeCounting (lengths n)) atTop (𝓝 0) :=
  (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
    (by norm_num : (2 : ℝ)⁻¹ < 1)).comp (Nat.tendsto_primeCounting.comp hlengths)

theorem logarithmic_lengths_eventually_contained
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop)
    (beta : ℝ) (hupper : ∀ᶠ n in atTop, (lengths n : ℝ) ≤ beta*Real.log (sizes n)) :
    ∀ᶠ n in atTop, lengths n ≤ sizes n := by
  have ht := logarithmic_lengths_div_size_tendsto_zero sizes lengths hsizes beta hupper
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1)),
    hsizes.eventually (eventually_ge_atTop 1)] with n ht hn
  have hp : (0 : ℝ) < sizes n := by exact_mod_cast (show 0 < sizes n by omega)
  exact_mod_cast ((div_lt_one hp).mp ht).le

/-- The full relative budget vanishes along arbitrary sizes, without assuming convergence of lambda/q. -/
theorem rareErrorBudget_tendsto_zero
    (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop) (hlengths : Tendsto lengths atTop atTop)
    (beta delta : ℝ) (hbeta : 0 < beta) (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hupper : ∀ᶠ n in atTop, (lengths n : ℝ) ≤ beta*Real.log (sizes n))
    (hrare : Tendsto (fun n => (fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => rareErrorBudget (sizes n) (lengths n) delta) atTop (𝓝 0) := by
  have hi := ((interior_mass_relative_tendsto_zero hLS hShorey hPNT).comp hlengths).const_mul 2
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hsizes)
  have hu : ∀ᶠ n in atTop, (lengths n+1 : ℕ) ≤ (beta+1)*Real.log (sizes n) := by
    filter_upwards [hupper, hlog.eventually (eventually_ge_atTop (1 : ℝ))] with n hn hl
    dsimp only [Function.comp_def] at hl
    push_cast
    nlinarith
  have hm := proposition_seven_three_rare_negligibility (beta+1) delta (by linarith) hdelta hdeltaOne
    hShorey hPNT hNR sizes lengths hsizes hlengths hu hrare
  have hj := microscopic_joint_relative_along_subsequence hAGG hPNT sizes lengths hsizes
    beta delta hbeta hdelta hupper hrare
  have ha := border_probability_tendsto_zero lengths hlengths
  have hb := (bulkRate_ratio_tendsto_one sizes lengths hsizes beta delta hdelta hdeltaOne hupper
    (hlengths.eventually (eventually_ge_atTop 1))).sub_const 1 |>.abs
  have ht := (((((hi.add hm).add hj).add hrare).add ha).add hb)
  simp only [mul_zero, add_zero, sub_self, abs_zero] at ht
  convert ht using 1
  funext n
  simp only [rareErrorBudget, middleEvent, AllStartSoftPoisson.fullRate, Function.comp_def,
    mul_div_assoc]
  rfl


/-- Equation (7.18), with the genuine finite-prefix hit event and the genuine q_L.
The formulation includes all subsequences and does not posit a limiting phase. -/
theorem equation_seven_eighteen
    (hAGG : ProcessAGGStatement) (hPNT : PrimeNumberTheoremRemainder)
    (hLS : UniformPrimeDivisorStatement) (hShorey : ShoreySquareProductStatement)
    (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (sizes lengths : ℕ → ℕ) (hsizes : Tendsto sizes atTop atTop) (hlengths : Tendsto lengths atTop atTop)
    (beta delta : ℝ) (hbeta : 0 < beta) (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hupper : ∀ᶠ n in atTop, (lengths n : ℝ) ≤ beta*Real.log (sizes n))
    (hrare : Tendsto (fun n => (fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => hitProbability (sizes n) (lengths n) /
      (microscopicProbability (lengths n)+(fullRate (sizes n) (lengths n) : ℝ))) atTop (𝓝 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (rareErrorBudget_tendsto_zero hAGG hPNT hLS hShorey hNR sizes lengths hsizes hlengths
      beta delta hbeta hdelta hdeltaOne hupper hrare)
  filter_upwards [hsizes.eventually (eventually_ge_atTop 2),
    hlengths.eventually (eventually_ge_atTop 1),
    logarithmic_lengths_eventually_contained sizes lengths hsizes beta hupper] with n hn hl hc
  simpa only [Real.norm_eq_abs] using hit_relative_error_le hn hl hc hdelta

end
end PaperC.V282.RarePrefixMass
