import PaperCV282.RestrictedPoissonTransfer
import PaperCV282.HardPoissonRates
import PaperCV282.SoftRateAssembly
import PaperCV282.SaddleRateConvergence

/-!
# Actual small-prime event restrictions and their information cost

The event probability is the real source probability, not an abstract
budget denominator. The source conditional count law keeps the same F_Y
as the corresponding hard or soft estimate. A fixed positive information
margin gives convergence; no general path-conditioning theorem is claimed.
-/

namespace PaperC.V282.RareConditioningRates

open MeasureTheory Set Filter Topology
open InfiniteRademacher InfiniteCylinderTransfer InfiniteConditionalWords
open PrimeFieldEventConditioning RestrictedPoissonTransfer
open ArratiaGoldsteinGordonInput SectionThirteenFiniteBound
open ScalarSteinInput PrimeEulerPNT AllStartSoftPoisson DyadicPoissonDistance
open SaddleParameters SaddleScales SaddleRateConvergence
open HardPoissonRates SoftRateAssembly

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

local instance instIsProbabilityMeasureInfiniteRademacher :
    IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- Information cost of a source event; used as conditioning only at positive probability. -/
def eventInformation (E : Set InfiniteSample) : ℝ :=
  -Real.log (infiniteRademacherMeasure.real E)

/-- Positive source event probabilities belong to the probability interval. -/
theorem event_probability_mem_Ioc (E : Set InfiniteSample)
    (hpos : 0 < infiniteRademacherMeasure.real E) :
    infiniteRademacherMeasure.real E ∈ Set.Ioc (0 : ℝ) 1 :=
  ⟨hpos, measureReal_le_one⟩

theorem eventInformation_nonneg (E : Set InfiniteSample)
    (hpos : 0 < infiniteRademacherMeasure.real E) : 0 ≤ eventInformation E := by
  unfold eventInformation
  exact neg_nonneg.mpr (Real.log_nonpos hpos.le (event_probability_mem_Ioc E hpos).2)

/-- The inverse-probability factor is exactly exp(I). -/
theorem exp_eventInformation (E : Set InfiniteSample)
    (hpos : 0 < infiniteRademacherMeasure.real E) :
    Real.exp (eventInformation E) = (infiniteRademacherMeasure.real E)⁻¹ := by
  rw [eventInformation, Real.exp_neg, Real.exp_log hpos]

/-- The restriction bound uses the actual sigma-algebra identified by the rate theorem. -/
theorem event_tv_le_conditional_of_sigma {N L Y : ℕ}
    (hsigma : smallPrimeSigmaAlgebra (dyadicCutoff N L) Y =
      MeasurableSpace.comap (restrictToFinite Y) inferInstance)
    (E : Set InfiniteSample)
    (hE : MeasurableSet[MeasurableSpace.comap (restrictToFinite Y) inferInstance] E)
    (hpos : 0 < infiniteRademacherMeasure.real E) :
    natTotalVariation (restrictedCountLaw N L E) (poissonMass (fullRate N L)) ≤
      conditionalDistance N L Y / infiniteRademacherMeasure.real E := by
  rw [← hsigma] at hE
  obtain ⟨S,rfl⟩ := measurableSet_eq_primeFieldEvent hE
  exact selected_event_tv_le_conditionalDistance N L Y S
    ((real_primeFieldEvent_pos_iff _ _ S).mp hpos)

/-- The hard rate divided by the exact probability of an event in its own F_Y. -/
theorem hard_event_rate_eventually
    (hStein : ScalarSteinFactorsStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax epsilon eta : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ E : Set InfiniteSample,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff N)) inferInstance] E →
      0 < infiniteRademacherMeasure.real E →
      natTotalVariation (restrictedCountLaw N L E) (poissonMass (fullRate N L)) ≤
        (20 * min 1 (hardRate N L epsilon eta)) / infiniteRademacherMeasure.real E := by
  obtain ⟨Nzero,hzero⟩ := theorem_four_three_hard hStein hPNT betaMin betaMax epsilon eta
    hbetaMin hbeta hepsilon heta
  refine ⟨Nzero, ?_⟩
  intro N hN L hlo hhi E hE hpos
  obtain ⟨hsigma,hbound,_⟩ := hzero N hN L hlo hhi
  exact (event_tv_le_conditional_of_sigma hsigma E hE hpos).trans
    (div_le_div_of_nonneg_right hbound hpos.le)

/-- The soft rate divided by the exact probability at the same soft conditioning field. -/
theorem soft_event_rate_eventually
    (hStein : ScalarSteinFactorsStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax epsilon eta : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ E : Set InfiniteSample,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (softCutoff N)) inferInstance] E →
      0 < infiniteRademacherMeasure.real E →
      natTotalVariation (restrictedCountLaw N L E) (poissonMass (fullRate N L)) ≤
        (6 * min 1 (softRate N L epsilon eta)) / infiniteRademacherMeasure.real E := by
  obtain ⟨Nzero,hzero⟩ := theorem_four_three_soft hStein hPNT betaMin betaMax epsilon eta
    hbetaMin hbeta hepsilon heta
  refine ⟨Nzero, ?_⟩
  intro N hN L hlo hhi E hE hpos
  obtain ⟨hsigma,hbound,_⟩ := hzero N hN L hlo hhi
  exact (event_tv_le_conditional_of_sigma hsigma E hE hpos).trans
    (div_le_div_of_nonneg_right hbound hpos.le)

/-- Expanding the soft restricted rate gives the exact coefficient 2I in the information budget. -/
theorem soft_rate_div_probability_le_information (N L : ℕ) (epsilon eta : ℝ)
    (E : Set InfiniteSample) (hpos : 0 < infiniteRademacherMeasure.real E) :
    (6 * min 1 (softRate N L epsilon eta)) / infiniteRademacherMeasure.real E ≤
      6 * (Real.exp (-(saddleCutoff 2 (Real.log N) -
          (2 * eventInformation E + max 0 (Real.log (fullRate N L : ℝ)))) / 2 +
          eta * saddleNu 2 (Real.log N)) +
        Real.exp (eventInformation E) * (N : ℝ) ^ (-(1 / (3 : ℝ)) + epsilon)) := by
  apply (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (min_le_right 1 (softRate N L epsilon eta)) (by norm_num)) hpos.le).trans_eq
  rw [div_eq_mul_inv, ← exp_eventInformation E hpos, softRate]
  have hexp : Real.exp (-(saddleCutoff 2 (Real.log N) - max 0 (Real.log (fullRate N L : ℝ))) / 2 +
      eta * saddleNu 2 (Real.log N)) * Real.exp (eventInformation E) =
      Real.exp (-(saddleCutoff 2 (Real.log N) -
        (2 * eventInformation E + max 0 (Real.log (fullRate N L : ℝ)))) / 2 +
        eta * saddleNu 2 (Real.log N)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [mul_assoc, add_mul, hexp]
  ring

/-- The exact source-event soft ledger, uniform before both the length and event are chosen. -/
theorem soft_event_information_bound_eventually
    (hStein : ScalarSteinFactorsStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax epsilon eta : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ E : Set InfiniteSample,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (softCutoff N)) inferInstance] E →
      0 < infiniteRademacherMeasure.real E →
      natTotalVariation (restrictedCountLaw N L E) (poissonMass (fullRate N L)) ≤
        6 * (Real.exp (-(saddleCutoff 2 (Real.log N) -
          (2 * eventInformation E + max 0 (Real.log (fullRate N L : ℝ)))) / 2 +
          eta * saddleNu 2 (Real.log N)) +
          Real.exp (eventInformation E) * (N : ℝ) ^ (-(1 / (3 : ℝ)) + epsilon)) := by
  obtain ⟨Nzero,hzero⟩ := soft_event_rate_eventually hStein hPNT betaMin betaMax epsilon eta
    hbetaMin hbeta hepsilon heta
  exact ⟨Nzero, fun N hN L hlo hhi E hE hpos =>
    (hzero N hN L hlo hhi E hE hpos).trans
      (soft_rate_div_probability_le_information N L epsilon eta E hpos)⟩

/-- The information margin keeps the inverse event probability subpolynomial. -/
theorem information_polynomial_error_le {N : ℕ} {I w ell nu c : ℝ}
    (hN : 1 ≤ N) (_hI : 0 ≤ I) (hell : 0 ≤ ell) (hc : 0 ≤ c) (hnu : 0 ≤ nu)
    (hw : w ≤ (1 / (12 : ℝ)) * Real.log N)
    (hmargin : 2 * I + ell ≤ w - c * nu) :
    Real.exp I * (N : ℝ) ^ (-(1 / (3 : ℝ)) + 1 / 12) ≤ (N : ℝ) ^ (-(1 / (6 : ℝ))) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hIupper : I ≤ (1 / (12 : ℝ)) * Real.log N := by
    nlinarith [mul_nonneg hc hnu]
  have hExp : Real.exp I ≤ (N : ℝ) ^ (1 / (12 : ℝ)) := by
    calc
      _ ≤ Real.exp ((1 / (12 : ℝ)) * Real.log N) := Real.exp_le_exp.mpr hIupper
      _ = _ := by
        rw [Real.rpow_def_of_pos hn]
        congr 1
        ring
  calc
    _ ≤ (N : ℝ) ^ (1 / (12 : ℝ)) * (N : ℝ) ^ (-(1 / (3 : ℝ)) + 1 / 12) := by
      exact mul_le_mul_of_nonneg_right hExp (Real.rpow_nonneg hn.le _)
    _ = _ := by
      rw [← Real.rpow_add hn]
      norm_num

/-- A uniform explicit vanishing envelope for positive events satisfying the soft margin. -/
theorem soft_event_margin_bound_eventually
    (hStein : ScalarSteinFactorsStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax c : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hc : 0 < c) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ E : Set InfiniteSample,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (softCutoff N)) inferInstance] E →
      0 < infiniteRademacherMeasure.real E →
      2 * eventInformation E + max 0 (Real.log (fullRate N L : ℝ)) ≤
        saddleCutoff 2 (Real.log N) - c * saddleNu 2 (Real.log N) →
      natTotalVariation (restrictedCountLaw N L E) (poissonMass (fullRate N L)) ≤
        6 * (Real.exp (-(c / 2 - c / 4) * saddleNu 2 (Real.log N)) +
          (N : ℝ) ^ (-(1 / (6 : ℝ)))) := by
  obtain ⟨Nrate,hrate⟩ := soft_event_information_bound_eventually hStein hPNT
    betaMin betaMax (1 / 12) (c / 4) hbetaMin hbeta (by norm_num) (by positivity)
  obtain ⟨Nw,hw⟩ := softCutoff_exponent_le_log_eventually (1 / 12) (by norm_num)
  have hnuLimit := (tendsto_saddleNu_atTop (by norm_num : (0 : ℝ) < 2)).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨Nnu,hnu⟩ := eventually_atTop.1 (hnuLimit.eventually (eventually_ge_atTop 0))
  refine ⟨max Nrate (max Nw (max Nnu 1)), ?_⟩
  intro N hN L hlo hhi E hE hpos hmargin
  have hbound := hrate N (by omega) L hlo hhi E hE hpos
  have hpower := information_polynomial_error_le (by omega : 1 ≤ N)
    (eventInformation_nonneg E hpos) (le_max_left 0 _) hc.le
    (hnu N (by omega)) (hw N (by omega)) hmargin
  have hmain : Real.exp (-(saddleCutoff 2 (Real.log N) -
      (2 * eventInformation E + max 0 (Real.log (fullRate N L : ℝ)))) / 2 +
      (c / 4) * saddleNu 2 (Real.log N)) ≤
      Real.exp (-(c / 2 - c / 4) * saddleNu 2 (Real.log N)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact hbound.trans (mul_le_mul_of_nonneg_left (add_le_add hmain hpower) (by norm_num))

/-- Actual conditional Poisson convergence for moving positive events in the same soft F_Y.
The margin is strict by a fixed c*nu; the exact boundary is not included. -/
theorem soft_event_convergence_of_information_margin
    (hStein : ScalarSteinFactorsStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax c : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hc : 0 < c)
    (L : ℕ → ℕ) (E : ℕ → Set InfiniteSample)
    (hband : ∀ᶠ N : ℕ in atTop,
      betaMin * Real.log N ≤ (L N + 1 : ℝ) ∧ (L N + 1 : ℝ) ≤ betaMax * Real.log N)
    (hE : ∀ᶠ N : ℕ in atTop,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (softCutoff N)) inferInstance] (E N))
    (hpos : ∀ᶠ N : ℕ in atTop, 0 < infiniteRademacherMeasure.real (E N))
    (hmargin : ∀ᶠ N : ℕ in atTop,
      2 * eventInformation (E N) + max 0 (Real.log (fullRate N (L N) : ℝ)) ≤
        saddleCutoff 2 (Real.log N) - c * saddleNu 2 (Real.log N)) :
    Tendsto (fun N => natTotalVariation (restrictedCountLaw N (L N) (E N))
      (poissonMass (fullRate N (L N)))) atTop (𝓝 0) := by
  obtain ⟨Nzero,hzero⟩ := soft_event_margin_bound_eventually hStein hPNT
    betaMin betaMax c hbetaMin hbeta hc
  apply squeeze_zero' (Eventually.of_forall fun N => natTotalVariation_nonneg _ _)
  · filter_upwards [eventually_ge_atTop Nzero,hband,hE,hpos,hmargin]
      with N hN hbandN hEN hposN hmarginN
    exact hzero N hN (L N) hbandN.1 hbandN.2 (E N) hEN hposN hmarginN
  · have hmain := margin_exponential_nat_tendsto_zero 2 c (c / 4)
      (by norm_num) (by linarith)
    have hpower := polynomial_error_nat_tendsto_zero (1 / 6) (by norm_num)
    have hlim := (hmain.add hpower).const_mul 6
    norm_num at hlim ⊢
    exact hlim

/-- Positive restrictions in the represented full F_Y remain probability laws. -/
theorem restrictedCountLaw_tv_le_one {N L Y : ℕ}
    (hsigma : smallPrimeSigmaAlgebra (dyadicCutoff N L) Y =
      MeasurableSpace.comap (restrictToFinite Y) inferInstance)
    (E : Set InfiniteSample)
    (hE : MeasurableSet[MeasurableSpace.comap (restrictToFinite Y) inferInstance] E)
    (hpos : 0 < infiniteRademacherMeasure.real E) :
    natTotalVariation (restrictedCountLaw N L E) (poissonMass (fullRate N L)) ≤ 1 := by
  have hmass : HasSum (restrictedCountLaw N L E) 1 := by
    rw [← hsigma] at hE
    obtain ⟨S,rfl⟩ := measurableSet_eq_primeFieldEvent hE
    exact hasSum_restrictedCountLaw_selected N L Y S
      ((real_primeFieldEvent_pos_iff _ _ S).mp hpos)
  apply FiniteFieldTotalVariation.massTotalVariation_le_one hmass
    (hasSum_poissonMass _) _ (poissonMass_nonneg _)
  intro k
  exact div_nonneg (measureReal_nonneg) hpos.le

/-- The hard estimate is truncated after its exact inverse-probability penalty. -/
theorem hard_event_rate_min_eventually
    (hStein : ScalarSteinFactorsStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax epsilon eta : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ E : Set InfiniteSample,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff N)) inferInstance] E →
      0 < infiniteRademacherMeasure.real E →
      natTotalVariation (restrictedCountLaw N L E) (poissonMass (fullRate N L)) ≤
        20 * min 1 (Real.exp (eventInformation E) * hardRate N L epsilon eta) := by
  obtain ⟨Nzero,hzero⟩ := theorem_four_three_hard hStein hPNT betaMin betaMax epsilon eta
    hbetaMin hbeta hepsilon heta
  refine ⟨Nzero, ?_⟩
  intro N hN L hlo hhi E hE hpos
  obtain ⟨hsigma,hbound,_⟩ := hzero N hN L hlo hhi
  apply le_mul_min_one_of_le (by norm_num : (1 : ℝ) ≤ 20)
    (restrictedCountLaw_tv_le_one hsigma E hE hpos)
  have hraw := (event_tv_le_conditional_of_sigma hsigma E hE hpos).trans
    (div_le_div_of_nonneg_right hbound hpos.le)
  apply hraw.trans
  calc
    _ ≤ (20 * hardRate N L epsilon eta) / infiniteRademacherMeasure.real E := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (min_le_right 1 _) (by norm_num)) hpos.le
    _ = _ := by rw [div_eq_mul_inv, ← exp_eventInformation E hpos]; ring

/-- The soft information ledger is truncated after conditioning on the actual event. -/
theorem soft_event_information_min_eventually
    (hStein : ScalarSteinFactorsStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax epsilon eta : ℝ) (hbetaMin : 0 < betaMin)
    (hbeta : betaMin < betaMax) (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    ∃ Nzero : ℕ, ∀ N ≥ Nzero, ∀ L : ℕ,
      betaMin * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ betaMax * Real.log N →
      ∀ E : Set InfiniteSample,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (softCutoff N)) inferInstance] E →
      0 < infiniteRademacherMeasure.real E →
      natTotalVariation (restrictedCountLaw N L E) (poissonMass (fullRate N L)) ≤
        6 * min 1 (Real.exp (-(saddleCutoff 2 (Real.log N) -
          (2 * eventInformation E + max 0 (Real.log (fullRate N L : ℝ)))) / 2 +
          eta * saddleNu 2 (Real.log N)) +
          Real.exp (eventInformation E) * (N : ℝ) ^ (-(1 / (3 : ℝ)) + epsilon)) := by
  obtain ⟨Nzero,hzero⟩ := theorem_four_three_soft hStein hPNT betaMin betaMax epsilon eta
    hbetaMin hbeta hepsilon heta
  refine ⟨Nzero, ?_⟩
  intro N hN L hlo hhi E hE hpos
  obtain ⟨hsigma,hbound,_⟩ := hzero N hN L hlo hhi
  apply le_mul_min_one_of_le (by norm_num : (1 : ℝ) ≤ 6)
    (restrictedCountLaw_tv_le_one hsigma E hE hpos)
  exact ((event_tv_le_conditional_of_sigma hsigma E hE hpos).trans
    (div_le_div_of_nonneg_right hbound hpos.le)).trans
    (soft_rate_div_probability_le_information N L epsilon eta E hpos)

end
end PaperC.V282.RareConditioningRates
