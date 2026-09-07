import PaperCV282.PoissonQuantitativeTailBudget
import PaperCV282.HardLocalClosureRates

/-! # True conditional moderate tails under the hard information margin -/
namespace PaperC.V282.PoissonQuantitativeTailRates

open MeasureTheory ProbabilityTheory Filter Topology Real Set
open InfiniteRademacher InfiniteCylinderTransfer InfiniteConditionalWords
open InfiniteStartProbabilityTransfer InfiniteMaskedScalarTransfer
open RestrictedPoissonTransfer RareConditioningRates HardPoissonRates
open AllStartSoftPoisson ScalarSteinInput PrimeEulerPNT SaddleParameters SaddleScales
open ArratiaGoldsteinGordonInput SectionThirteenFiniteBound
open PoissonQuantitativeTailBudget PoissonQuantitativeMills PoissonQuantitativeModerate
open PoissonQuantitativeModerateLimit SmallIntensityConditioning
open SharpConditioning PoissonRareProbabilities PoissonGaussianSource InfiniteMassCoupling ConditionedCountableLaw

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- Uniform before the count length, the positive environment event, and the tail threshold. -/
theorem hard_tail_normalized_tv_eventually
    (hStein : ScalarSteinFactorsStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax c : ℝ) (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax) (hc : 0<c) :
    ∃ Nzero : ℕ, ∀ N≥Nzero, ∀ L : ℕ,
      betaMin*log N≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*log N →
      ∀ C : Set InfiniteSample,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff N)) inferInstance] C →
      0 < infiniteRademacherMeasure.real C → ∀ t : ℝ, 0≤t →
      hardTailCost (eventInformation C) (fullRate N L) t ≤
        saddleCutoff 1 (log N)-c*saddleNu 1 (log N) →
      natTotalVariation (restrictedCountLaw N L C) (poissonMass (fullRate N L)) /
        normalTail t ≤ hardTailRemainder N c := by
  obtain ⟨Nr,hr⟩ := hard_event_rate_eventually hStein hPNT
    betaMin betaMax (1/12) (c/2) hbetaMin hbeta (by norm_num) (by linarith)
  obtain ⟨Np,hp⟩ := eventually_atTop.1 (hard_polynomial_div_tail_eventually c hc.le)
  refine ⟨max Nr (max Np 2),?_⟩
  intro N hN L hlo hhi C hC hpos t ht hb
  have hrate : 0<(fullRate N L : ℝ) := by
    rw [fullRate_coe]
    have hnpos : 0<N := by omega
    positivity
  have htail := normalTail_pos t ht
  have hlead := hard_leading_div_tail_le (eta := c/2) hrate ht hb
  have hpoly := hp N (by omega) (eventInformation C) (fullRate N L) t hrate ht hb
  have hraw := hr N (by omega) L hlo hhi C hC hpos
  have hmin : (20 : ℝ)*min 1 (hardRate N L (1/12) (c/2))≤20*hardRate N L (1/12) (c/2) :=
    mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
  have hraw' := hraw.trans (div_le_div_of_nonneg_right hmin hpos.le)
  have hraw'' := div_le_div_of_nonneg_right hraw' htail.le
  simp only [div_eq_mul_inv] at hraw''
  rw [← exp_eventInformation C hpos] at hraw''
  unfold hardTailRemainder
  have heq : c-c/2=c/2 := by ring
  rw [heq] at hlead
  apply hraw''.trans
  unfold hardRate
  convert (mul_le_mul_of_nonneg_left (add_le_add hlead hpoly) (by norm_num : (0 : ℝ)≤20)) using 1
  ring_nf

/-- An actual conditional event, compared at the positive normal-tail scale. -/
theorem source_tail_relative_error_le {N L : ℕ} (C : Set InfiniteSample)
    (hC : MeasurableSet C) (hpos : 0 < infiniteRademacherMeasure.real C)
    (t : ℝ) (ht : 0≤t) (hr : (4096 : ℝ)≤fullRate N L) (hcubic : t^3/sqrt (fullRate N L)≤1) :
    |(conditionalStartMeasure N L C).real
        (Ici ⌈(fullRate N L : ℝ)+sqrt (fullRate N L)*t⌉₊)/normalTail t-1|≤
      natTotalVariation (restrictedCountLaw N L C) (poissonMass (fullRate N L))/normalTail t+
        moderateConstant*((1+t^3)/sqrt (fullRate N L)) := by
  letI instProbabilityConditionalSource : IsProbabilityMeasure (cond infiniteRademacherMeasure C) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hpos)
  letI instProbabilityConditionalCount : IsProbabilityMeasure (conditionalStartMeasure N L C) :=
    Measure.isProbabilityMeasure_map (measurable_source_startCount N L).aemeasurable
  have h := relative_event_error_le (conditionalStartMeasure N L C)
    (poissonMeasure (fullRate N L)) (Ici ⌈(fullRate N L : ℝ)+sqrt (fullRate N L)*t⌉₊)
    (normalTail_pos t ht) (poisson_moderate_relative_error (fullRate N L) hr t ht hcubic)
  rwa [conditionalStartMeasure_tv_eq N L C hC hpos] at h

/-- D.1: the true conditional tail is asymptotic to the Gaussian tail under its printed hard budget. -/
theorem hard_conditional_tail_normal_ratio_tendsto_one
    (hStein : ScalarSteinFactorsStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax c : ℝ) (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax) (hc : 0<c)
    (sizes lengths : ℕ→ℕ) (t : ℕ→ℝ) (C : ℕ→Set InfiniteSample)
    (hsizes : Tendsto sizes atTop atTop)
    (hrate : Tendsto (fun k => (fullRate (sizes k) (lengths k) : ℝ)) atTop atTop)
    (ht : Tendsto (fun k => t k/(fullRate (sizes k) (lengths k) : ℝ)^(1/6 : ℝ)) atTop (𝓝 0))
    (hadmissible : ∀ᶠ k in atTop,
      betaMin*log (sizes k)≤(lengths k+1 : ℝ) ∧
      (lengths k+1 : ℝ)≤betaMax*log (sizes k) ∧
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff (sizes k))) inferInstance] (C k) ∧
      0 < infiniteRademacherMeasure.real (C k) ∧ 0≤t k ∧
      hardTailCost (eventInformation (C k)) (fullRate (sizes k) (lengths k)) (t k) ≤
        saddleCutoff 1 (log (sizes k))-c*saddleNu 1 (log (sizes k))) :
    Tendsto (fun k => (cond infiniteRademacherMeasure (C k)).real
      {omega | ⌈(fullRate (sizes k) (lengths k) : ℝ)+sqrt (fullRate (sizes k) (lengths k))*t k⌉₊≤
        infiniteDyadicStartCount (sizes k) (lengths k) omega}/normalTail (t k)) atTop (𝓝 1) := by
  obtain ⟨Nzero,hzero⟩ := hard_tail_normalized_tv_eventually
    hStein hPNT betaMin betaMax c hbetaMin hbeta hc
  have he := (hardTailRemainder_tendsto_zero hc).comp hsizes
  have hm := (moderate_error_scale_tendsto_zero
    (fun k => (fullRate (sizes k) (lengths k) : ℝ)) t hrate ht).const_mul moderateConstant
  have hh := he.add hm
  simp only [mul_zero,add_zero] at hh
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) _ hh
  filter_upwards [hsizes.eventually (eventually_ge_atTop Nzero),hadmissible,
    moderate_domain_eventually (fun k => (fullRate (sizes k) (lengths k) : ℝ)) t hrate ht]
    with k hk ha hd
  have hCm : MeasurableSet (C k) := by
    have hm := ha.2.2.1
    rw [← smallPrimeSigmaAlgebra_eq_primeCylinder (M := hardCutoff (sizes k)) le_rfl] at hm
    exact smallPrimeSigmaAlgebra_le _ _ (C k) hm
  have hb := source_tail_relative_error_le (N := sizes k) (L := lengths k) (C k) hCm
    ha.2.2.2.1 (t k) ha.2.2.2.2.1 hd.1 hd.2
  rw [conditionalStartMeasure_event] at hb
  exact hb.trans (add_le_add (hzero (sizes k) hk (lengths k) ha.1 ha.2.1 (C k)
    ha.2.2.1 ha.2.2.2.1 (t k) ha.2.2.2.2.1 ha.2.2.2.2.2) (le_refl _))

/-- The same true conditional tail is relatively asymptotic to the actual Poisson tail. -/
theorem hard_conditional_tail_poisson_ratio_tendsto_one
    (hStein : ScalarSteinFactorsStatement) (hPNT : PrimeNumberTheoremRemainder)
    (betaMin betaMax c : ℝ) (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax) (hc : 0<c)
    (sizes lengths : ℕ→ℕ) (t : ℕ→ℝ) (C : ℕ→Set InfiniteSample)
    (hsizes : Tendsto sizes atTop atTop)
    (hrate : Tendsto (fun k => (fullRate (sizes k) (lengths k) : ℝ)) atTop atTop)
    (ht : Tendsto (fun k => t k/(fullRate (sizes k) (lengths k) : ℝ)^(1/6 : ℝ)) atTop (𝓝 0))
    (hadmissible : ∀ᶠ k in atTop,
      betaMin*log (sizes k)≤(lengths k+1 : ℝ) ∧
      (lengths k+1 : ℝ)≤betaMax*log (sizes k) ∧
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff (sizes k))) inferInstance] (C k) ∧
      0 < infiniteRademacherMeasure.real (C k) ∧ 0≤t k ∧
      hardTailCost (eventInformation (C k)) (fullRate (sizes k) (lengths k)) (t k) ≤
        saddleCutoff 1 (log (sizes k))-c*saddleNu 1 (log (sizes k))) :
    Tendsto (fun k => (cond infiniteRademacherMeasure (C k)).real
      {omega | ⌈(fullRate (sizes k) (lengths k) : ℝ)+sqrt (fullRate (sizes k) (lengths k))*t k⌉₊≤
        infiniteDyadicStartCount (sizes k) (lengths k) omega}/
      (poissonMeasure (fullRate (sizes k) (lengths k))).real
        (Ici ⌈(fullRate (sizes k) (lengths k) : ℝ)+sqrt (fullRate (sizes k) (lengths k))*t k⌉₊))
      atTop (𝓝 1) := by
  have hs := hard_conditional_tail_normal_ratio_tendsto_one hStein hPNT betaMin betaMax c
    hbetaMin hbeta hc sizes lengths t C hsizes hrate ht hadmissible
  have hn := poisson_moderate_ratio_tendsto_one (fun k => fullRate (sizes k) (lengths k)) t hrate ht
    (hadmissible.mono fun _ h => h.2.2.2.2.1)
  have hh := hs.div hn (by norm_num : (1 : ℝ)≠0)
  simp only [div_self (by norm_num : (1 : ℝ)≠0)] at hh
  apply hh.congr'
  filter_upwards [hadmissible] with k hk
  exact div_div_div_cancel_right₀ (normalTail_pos (t k) hk.2.2.2.2.1).ne' _ _

end
end PaperC.V282.PoissonQuantitativeTailRates
