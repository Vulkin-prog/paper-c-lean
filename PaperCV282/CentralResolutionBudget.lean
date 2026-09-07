import PaperCV282.ResolvedInformationTheorem
import PaperCV282.AggregateInformationBudget
import PaperCV282.PoissonCentralAsymptotics

/-! # The central three-halves budget retains a fixed positive margin

The logarithmic Stein factor and the bounded Taylor errors fit into any
strictly smaller positive margin. The source-law specialization below uses
proved central asymptotics, with no local limit assumed as an input.
-/
namespace PaperC.V282.CentralResolutionBudget

open MeasureTheory ProbabilityTheory Filter Topology Real
open PoissonResolutionBudget PoissonStirlingBounds ResolvedInformationTheorem
open AggregateInformationBudget SaddleParameters SaddleScales AllStartSoftPoisson
open CriticalRunWindow SaddleCutoffAdmissibility PoissonCentralAsymptotics
open InfiniteRademacher InfiniteCylinderTransfer RareConditioningRates HardPoissonRates
open ConditionedCountableLaw
open DirectionalSteinInput PrimeEulerPNT SharpConditioning PoissonResolvedComparison PoissonResolvedTarget

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- The extra logarithmic Stein cost is negligible on the saddle-nu scale. -/
theorem stein_log_cost_le_margin_eventually {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ rate : ℝ, 1 ≤ rate →
      log rate ≤ saddleCutoff 1 (log N) →
      log (1 + max 0 (log (2 * rate))) ≤ eta * saddleNu 1 (log N) := by
  have htwo : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hp := linear_saddle_le_exp_nu_eventually (2 + log 2) eta (by positivity) heta
  have hlog : Tendsto (fun N : ℕ => log N) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hp, hlog.eventually (eventually_ge_atTop (saddleThreshold 1))] with N hp hs
  intro rate hr hb
  have hV := (saddleCutoff_pos (a := 1) (by norm_num) hs).le
  have hrpos : 0 < rate := by linarith
  have hlogr := log_nonneg hr
  have hlogtwo : 0 ≤ log (2 * rate) := log_nonneg (by linarith)
  rw [max_eq_right hlogtwo]
  have hfac : 1 + log (2 * rate) ≤ exp (eta * saddleNu 1 (log N)) := by
    refine le_trans ?_ hp
    rw [log_mul (by norm_num) hrpos.ne']
    nlinarith [mul_nonneg hV htwo.le]
  have hfacpos : 0 < 1 + log (2 * rate) := by linarith
  simpa only [log_exp] using log_le_log hfacpos hfac

/-- A bounded central Taylor error costs only a smaller fixed information margin. -/
theorem central_cost_budget_eventually (c c' : ℝ) (hc' : 0 < c') (hcc : c' < c) :
    ∀ᶠ N : ℕ in atTop, ∀ I rate t : ℝ, ∀ n : ℕ,
      0 ≤ I → 1 ≤ rate →
      I + (3/2 : ℝ) * log rate + t^2/2 ≤
        saddleCutoff 1 (log N) - c * saddleNu 1 (log N) →
      |log (n : ℝ) - log rate| ≤ 1 →
      |rate * poissonEntropy (n / rate) - t^2/2| ≤ 1 →
      resolvedInformationCost I rate n ≤
        saddleCutoff 1 (log N) - c' * saddleNu 1 (log N) := by
  have hnu := (tendsto_saddleNu_atTop (a := 1) (by norm_num)).comp
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hmargin := hnu.const_mul_atTop (by linarith : 0 < (c-c')/2)
  filter_upwards [stein_log_cost_le_margin_eventually (eta := (c-c')/2) (by linarith),
    hmargin.eventually (eventually_ge_atTop (3/2 : ℝ)),
    hnu.eventually (eventually_ge_atTop (0 : ℝ))] with N hstein hm hn
  intro I rate t n hI hr hb heLog heEntropy
  dsimp only [Function.comp_def] at hm hn
  have hrlog : 0 ≤ log rate := log_nonneg hr
  have hlogle : log rate ≤ saddleCutoff 1 (log N) := by
    nlinarith [sq_nonneg t, mul_nonneg (show 0 ≤ c by linarith) hn]
  have hs := hstein rate hr hlogle
  have hel := (abs_le.mp heLog).2
  have hee := (abs_le.mp heEntropy).2
  unfold resolvedInformationCost poissonLocalCost
  rw [max_eq_right hrlog]
  linarith

/-- The central information envelope itself places the true length in a common band. -/
theorem central_common_band_eventually :
    ∀ᶠ N : ℕ in atTop, ∀ L : ℕ, 1 ≤ (fullRate N L : ℝ) →
      log (fullRate N L : ℝ) ≤ saddleCutoff 1 (log N) →
      lowerConstant * log N ≤ (L+1 : ℝ) ∧ (L+1 : ℝ) ≤ upperConstant * log N := by
  have hlog : Tendsto (fun N : ℕ => log N) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio := ((tendsto_saddleCutoff_div_height (a := 1) (by norm_num)).comp hlog).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
  filter_upwards [hratio, hlog.eventually (eventually_ge_atTop (max 1 (log 2))),
    eventually_ge_atTop (2 : ℕ)] with N hv hs hN
  intro L hr hb
  have hnpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogN : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogtwo : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hvle : saddleCutoff 1 (log N) ≤ log N / 2 := by
    have hh := (div_lt_iff₀ hlogN).mp hv
    linarith
  have hid : log (fullRate N L : ℝ) = log N - (L : ℝ)*log 2 := by
    rw [fullRate_coe, log_div hnpos.ne' (by positivity), log_pow]
  have hrlog : 0 ≤ log (fullRate N L : ℝ) := log_nonneg hr
  rw [hid] at hrlog hb
  have hlogtwoN : log (2 : ℝ) ≤ log N := (le_max_right _ _).trans hs
  constructor
  · unfold lowerConstant
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < 2*log (2 : ℝ))]
    nlinarith
  · unfold upperConstant
    rw [div_mul_eq_mul_div, le_div_iff₀ hlogtwo]
    nlinarith

/-- The printed central regime controls the actual entire future after resolution.
The common band and positivity of the resolved event are conclusions. -/
theorem central_resolved_future (hStein : DirectionalSteinFactorsStatement)
    (hPNT : PrimeNumberTheoremRemainder) (c c' : ℝ) (hc' : 0 < c') (hcc : c' < c)
    (sizes lengths counts : ℕ → ℕ) (C : ℕ → Set InfiniteSample) (t : ℕ → ℝ) (K : ℝ)
    (hsizes : Tendsto sizes atTop atTop)
    (hrate : Tendsto (fun k => (fullRate (sizes k) (lengths k) : ℝ)) atTop atTop)
    (ht : Tendsto (fun k => t k/(fullRate (sizes k) (lengths k) : ℝ)^(1/6 : ℝ)) atTop (𝓝 0))
    (hround : ∀ᶠ k in atTop, |(counts k : ℝ)-((fullRate (sizes k) (lengths k) : ℝ)+
      t k*sqrt (fullRate (sizes k) (lengths k) : ℝ))| ≤ K)
    (hC : ∀ᶠ k in atTop,
      MeasurableSet[MeasurableSpace.comap (restrictToFinite (hardCutoff (sizes k))) inferInstance] (C k))
    (hpos : ∀ᶠ k in atTop, 0 < infiniteRademacherMeasure.real (C k))
    (hbudget : ∀ᶠ k in atTop,
      eventInformation (C k) + (3/2 : ℝ)*log (fullRate (sizes k) (lengths k) : ℝ)+(t k)^2/2 ≤
        saddleCutoff 1 (log (sizes k))-c*saddleNu 1 (log (sizes k))) :
    (∀ᶠ k in atTop, 0 < infiniteRademacherMeasure.real
      (C k ∩ {omega | InfiniteStartProbabilityTransfer.infiniteDyadicStartCount
        (sizes k) (lengths k) omega = counts k}) ∧
      measureTotalVariation (resolvedFutureLaw (sizes k) (lengths k) (counts k) (C k))
        (thinningPathMeasure (counts k)) ≤ resolvedBudgetRemainder (sizes k) c') ∧
    Tendsto (fun k => measureTotalVariation
      (resolvedFutureLaw (sizes k) (lengths k) (counts k) (C k))
      (thinningPathMeasure (counts k))) atTop (𝓝 0) := by
  obtain ⟨hlogerr,hentropyerr⟩ := bounded_rounding_central_errors
    (fun k => (fullRate (sizes k) (lengths k) : ℝ)) counts t K hrate ht hround
  have hlogs := hlogerr.abs.eventually (gt_mem_nhds (by norm_num : |(0 : ℝ)| < 1))
  have hentropies := hentropyerr.abs.eventually (gt_mem_nhds (by norm_num : |(0 : ℝ)| < 1))
  obtain ⟨Nzero,hzero⟩ := resolved_future_under_information_budget hStein hPNT
    lowerConstant upperConstant c' lowerConstant_pos lowerConstant_lt_upperConstant hc'
  have hnu := ((tendsto_saddleNu_atTop (a := 1) (by norm_num)).comp
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).comp hsizes
  have hfinal : ∀ᶠ k in atTop, 0 < infiniteRademacherMeasure.real
      (C k ∩ {omega | InfiniteStartProbabilityTransfer.infiniteDyadicStartCount
        (sizes k) (lengths k) omega = counts k}) ∧
      measureTotalVariation (resolvedFutureLaw (sizes k) (lengths k) (counts k) (C k))
        (thinningPathMeasure (counts k)) ≤ resolvedBudgetRemainder (sizes k) c' := by
    filter_upwards [hsizes.eventually (central_cost_budget_eventually c c' hc' hcc),
      hsizes.eventually central_common_band_eventually, hsizes.eventually (eventually_ge_atTop Nzero),
      hrate.eventually (eventually_ge_atTop (1 : ℝ)),
      (tendsto_log_atTop.comp hrate).eventually (eventually_ge_atTop (2 : ℝ)),
      hnu.eventually (eventually_ge_atTop (0 : ℝ)), hC,hpos,hbudget,hlogs,hentropies]
      with k hcost hband hN hr hlr hnu0 hmeas hpositive hb hel hee
    dsimp only [Function.comp_def] at hlr
    have hI := eventInformation_nonneg (C k) hpositive
    have hn : 0 < counts k := by
      by_contra hn
      have hz : counts k = 0 := by omega
      simp only [hz,Nat.cast_zero,log_zero,zero_sub,abs_neg] at hel
      have hh := le_abs_self (log (fullRate (sizes k) (lengths k) : ℝ))
      linarith
    have hbfull := hcost (eventInformation (C k)) (fullRate (sizes k) (lengths k)) (t k)
      (counts k) hI hr hb hel.le hee.le
    have hlogle : log (fullRate (sizes k) (lengths k) : ℝ) ≤ saddleCutoff 1 (log (sizes k)) := by
      have hrl := log_nonneg hr
      dsimp only [Function.comp_def] at hnu0
      nlinarith [sq_nonneg (t k), mul_nonneg (show 0 ≤ c by linarith) hnu0]
    obtain ⟨hlo,hhi⟩ := hband (lengths k) hr hlogle
    exact hzero (sizes k) hN (lengths k) hlo hhi (C k) hmeas hpositive (counts k) hn hbfull
  refine ⟨hfinal, ?_⟩
  have hlim := (resolvedBudgetRemainder_tendsto_zero hc').comp hsizes
  have hnonneg : ∀ᶠ k in atTop, 0 ≤ measureTotalVariation
      (resolvedFutureLaw (sizes k) (lengths k) (counts k) (C k))
      (thinningPathMeasure (counts k)) := by
    filter_upwards [hfinal] with k hk
    letI instProbabilityResolvedConditional : IsProbabilityMeasure
        (cond infiniteRademacherMeasure
          (C k ∩ {omega | InfiniteStartProbabilityTransfer.infiniteDyadicStartCount
            (sizes k) (lengths k) omega = counts k})) :=
      cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hk.1)
    letI instProbabilityResolvedFuture : IsProbabilityMeasure
        (resolvedFutureLaw (sizes k) (lengths k) (counts k) (C k)) :=
      Measure.isProbabilityMeasure_map (measurable_actualFuturePath (sizes k) (lengths k)).aemeasurable
    exact measureTotalVariation_nonneg _ _
  apply squeeze_zero' hnonneg (hfinal.mono fun _ h => h.2)
  simpa only [Function.comp_def] using hlim

end
end PaperC.V282.CentralResolutionBudget
