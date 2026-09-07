import PaperCV282.RareConditioningRates
import PaperCV282.AggregateCutoffRemainder

/-! # Relative scalar error under a hard information margin

The intensity cancels from the actual hard scalar comparison. The information
budget alone absorbs conditioning in the polynomial error; no upper or lower
intensity regime is imposed beyond the positivity supplied by the dyadic block.
-/
namespace PaperC.V282.HardRelativeMargin

open MeasureTheory Set Filter Topology
open InfiniteRademacher InfiniteCylinderTransfer
open ScalarSteinInput PrimeEulerPNT AllStartSoftPoisson
open ArratiaGoldsteinGordonInput SectionThirteenFiniteBound RestrictedPoissonTransfer
open RareConditioningRates HardPoissonRates SaddleParameters SaddleScales
open SaddleRateConvergence AggregateInformationBudget

noncomputable section

/-- An explicit relative error, independent of the length and the conditioning event. -/
def hardRelativeMargin (N : ℕ) (c : ℝ) : ℝ :=
  20 * (Real.exp (-(c / 2) * saddleNu 1 (Real.log N)) + (N : ℝ) ^ (-(1 / 6 : ℝ)))

theorem hardRelativeMargin_tendsto_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => hardRelativeMargin N c) atTop (𝓝 0) := by
  have he := margin_exponential_nat_tendsto_zero 1 c 0 (by norm_num) (by linarith)
  have hp := polynomial_error_nat_tendsto_zero (1 / 6) (by norm_num)
  have h := (he.add hp).const_mul 20
  simpa only [hardRelativeMargin, sub_zero, show -(1 / 3 : ℝ) + 1 / 6 = -(1 / 6 : ℝ) by ring,
    add_zero, mul_zero] using h

/-- The threshold precedes the length and every positive event in the true hard prime field. -/
theorem hard_relative_margin_eventually
    (hStein : ScalarSteinFactorsStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax c : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hc : 0 < c) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ C : Set InfiniteSample,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff N)) inferInstance] C →
      0 < infiniteRademacherMeasure.real C →
      eventInformation C ≤ saddleCutoff 1 (Real.log N) - c * saddleNu 1 (Real.log N) →
      natTotalVariation (restrictedCountLaw N L C) (poissonMass (fullRate N L)) /
        (fullRate N L : ℝ) ≤ hardRelativeMargin N c := by
  obtain ⟨Nr, hr⟩ := hard_event_rate_min_eventually hStein hPNT
    betaMin betaMax (1 / 12) (c / 2) hbetaMin hbeta (by norm_num) (by linarith)
  obtain ⟨Np, hp⟩ := eventually_atTop.1
    (exp_saddle_le_power_eventually 1 (1 / 12) (by norm_num))
  have hnu := (tendsto_saddleNu_atTop (a := 1) (by norm_num)).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨Nn, hn⟩ := eventually_atTop.1 (hnu.eventually (eventually_ge_atTop (0 : ℝ)))
  refine ⟨max Nr (max Np (max Nn 2)), ?_⟩
  intro N hN L hlo hhi C hC hpos hbudget
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hrate : 0 < (fullRate N L : ℝ) := by rw [fullRate_coe]; positivity
  have hnu0 : 0 ≤ saddleNu 1 (Real.log N) := hn N (by omega)
  have hIV : eventInformation C ≤ saddleCutoff 1 (Real.log N) :=
    hbudget.trans (sub_le_self _ (mul_nonneg hc.le hnu0))
  have hexp : Real.exp (eventInformation C) *
      Real.exp (-saddleCutoff 1 (Real.log N) + (c / 2) * saddleNu 1 (Real.log N)) ≤
      Real.exp (-(c / 2) * saddleNu 1 (Real.log N)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hpoly : Real.exp (eventInformation C) * (N : ℝ) ^ (-(1 / 3 : ℝ) + 1 / 12) ≤
      (N : ℝ) ^ (-(1 / 6 : ℝ)) := by
    have hsmall : Real.exp (eventInformation C) ≤ (N : ℝ) ^ (1 / 12 : ℝ) := by
      exact (Real.exp_le_exp.mpr hIV).trans (by simpa only [one_mul] using hp N (by omega))
    calc
      _ ≤ (N : ℝ) ^ (1 / 12 : ℝ) * (N : ℝ) ^ (-(1 / 3 : ℝ) + 1 / 12) :=
        mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hNpos.le _)
      _ = _ := by rw [← Real.rpow_add hNpos]; congr 1; ring
  have hraw := (hr N (by omega) L hlo hhi C hC hpos).trans
    (mul_le_mul_of_nonneg_left (min_le_right (1 : ℝ) _) (by norm_num : (0 : ℝ) ≤ 20))
  apply (div_le_iff₀ hrate).mpr
  unfold hardRelativeMargin
  have hs := mul_le_mul_of_nonneg_left (add_le_add hexp hpoly)
    (show 0 ≤ 20 * (fullRate N L : ℝ) by positivity)
  unfold hardRate at hraw
  nlinarith

/-- Actual relative total variation vanishes along every eventually admissible choice. -/
theorem hard_relative_distance_tendsto_zero
    (hStein : ScalarSteinFactorsStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax c : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hc : 0 < c)
    (sizes lengths : ℕ → ℕ) (events : ℕ → Set InfiniteSample)
    (hsizes : Tendsto sizes atTop atTop)
    (hadmissible : ∀ᶠ k in atTop,
      betaMin * Real.log (sizes k) ≤ (lengths k + 1 : ℝ) ∧
      (lengths k + 1 : ℝ) ≤ betaMax * Real.log (sizes k) ∧
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff (sizes k))) inferInstance]
        (events k) ∧
      0 < infiniteRademacherMeasure.real (events k) ∧
      eventInformation (events k) ≤ saddleCutoff 1 (Real.log (sizes k)) -
        c * saddleNu 1 (Real.log (sizes k))) :
    Tendsto (fun k => natTotalVariation (restrictedCountLaw (sizes k) (lengths k) (events k))
      (poissonMass (fullRate (sizes k) (lengths k))) / (fullRate (sizes k) (lengths k) : ℝ))
      atTop (𝓝 0) := by
  obtain ⟨Nzero, hzero⟩ := hard_relative_margin_eventually
    hStein hPNT betaMin betaMax c hbetaMin hbeta hc
  apply squeeze_zero' _ _ ((hardRelativeMargin_tendsto_zero hc).comp hsizes)
  · exact Eventually.of_forall fun k => div_nonneg
      (FiniteFieldTotalVariation.massTotalVariation_nonneg _ _) (NNReal.coe_nonneg _)
  · filter_upwards [hsizes.eventually (eventually_ge_atTop Nzero), hadmissible] with k hk ha
    exact hzero (sizes k) hk (lengths k) ha.1 ha.2.1 (events k) ha.2.2.1 ha.2.2.2.1 ha.2.2.2.2

end
end PaperC.V282.HardRelativeMargin
