import PaperCV282.MacroAggregateHard
import PaperCV282.MacroTransportStatistics
import PaperCV282.MacroTransportHardComparison
import PaperCV282.MacroTransportInformation

/-! # Restoring microscopic starts in the true aggregate comparison -/
namespace PaperC.V282.MacroAggregateRestoration

open MeasureTheory ProbabilityTheory Filter Topology InfiniteRademacher InfiniteCylinderTransfer
open MacroAggregateModel MacroAggregateTruncation MacroAggregateHard MacroTransportModel
open MacroTransportRestriction MacroTransportStatistics MacroTransportHardComparison MacroTransportInformation
open BulkMarkedTypes BulkMarkedSource BulkMarkedTarget BulkMarkedGeometry InfiniteMassCoupling
open ConditionedCountableLaw FiniteFieldTotalVariation FiniteStartMaskAverages InfiniteStartProbabilityTransfer
open AggregateInformationBudget AggregateCutoffRemainder RareConditioningRates GrowingMarkedTruncation
open SaddleParameters SaddleScales HardPoissonRates AllStartSoftPoisson PrimeEulerPNT DirectionalSteinInput
open LaishramUniformInput PostQuadraticLiterature MesoscopicPrefixMass InfiniteConditionalWords
open scoped BigOperators NNReal

noncomputable section

local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- The observable forgets positions only, retaining every exact excess and sign. -/
def containedAggregateDistance (M L : ℕ) (A : Set InfiniteSample) : ℝ :=
  conditionalSignedAggregateDistance (containedStarts M L) L A

theorem aggregate_embed_sites {s t : Finset ℕ} (h : s⊆t) (c : SpatialMarkedConfig s) :
    aggregateSigned t (embedSites h c)=aggregateSigned s c := by
  unfold aggregateSigned embedSites
  rw [Finsupp.embDomain_eq_mapDomain,← Finsupp.mapDomain_comp]
  rfl

/-- Restoring sites after aggregation preserves its directional middle cost. -/
theorem conditional_aggregate_restoration_le {s t : Finset ℕ} (h : s⊆t) (L : ℕ)
    (A : Set InfiniteSample) (hA : MeasurableSet A) (hpos : 0 < infiniteRademacherMeasure.real A) :
    conditionalSignedAggregateDistance t L A≤
      (∑ x∈t\s,infiniteStartProbability x L)/infiniteRademacherMeasure.real A+
        conditionalSignedAggregateDistance s L A+(maskRate L (t\s) : ℝ) := by
  letI instProbabilityConditional : IsProbabilityMeasure (cond infiniteRademacherMeasure A) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hpos)
  have hh := conditional_statistic_restoration_le h L (aggregateSigned s) (aggregateSigned t)
    (aggregate_embed_sites h) A hA hpos
  rw [two_map_distance_eq_mass _ _ ((measurable_of_countable (aggregateSigned t)).comp (measurable_spatialMarkedSource t L)) (measurable_of_countable _),
    two_map_distance_eq_mass _ _ ((measurable_of_countable (aggregateSigned s)).comp (measurable_spatialMarkedSource s L)) (measurable_of_countable _)] at hh
  exact hh

/-- The removed true starts, and their target mass, obey the single-intensity information budget. -/
theorem restoration_under_budget_eventually
    (hPNT : PrimeNumberTheoremRemainder) (hLS : UniformPrimeDivisorStatement)
    (hShorey : ShoreySquareProductStatement) (hNR : PellInput.NicolasRobinDivisorLogBoundStatement)
    (betaMin betaMax c epsilon : ℝ) (hbetaMin : 0<betaMin) (hbeta : betaMin<betaMax)
    (hc : 0≤c) (hepsilon : 0<epsilon) :
    ∃ Mzero : ℕ, ∀ M≥Mzero, ∀ L : ℕ,
      betaMin*Real.log M≤(L+1 : ℝ) → (L+1 : ℝ)≤betaMax*Real.log M →
      ∀ A : Set InfiniteSample, 0 < infiniteRademacherMeasure.real A → 1≤(fullRate M L : ℝ) →
      aggregateLogCost (eventInformation A) (fullRate M L)≤
        saddleCutoff 1 (Real.log M)-c*saddleNu 1 (Real.log M) →
      (∑ x∈containedStarts M L\bulkStarts M L (1/2),infiniteStartProbability x L)/infiniteRademacherMeasure.real A+
        (maskRate L (containedStarts M L\bulkStarts M L (1/2)) : ℝ)≤
      (M : ℝ)^(-(1/3 : ℝ)+epsilon)+
        2*Real.exp (-(betaMin*Real.log 2/16)*(Real.log M/Real.log (Real.log M))) := by
  obtain ⟨Np,hp⟩ := equation_seven_seven betaMin betaMax hbetaMin hbeta hLS hShorey hPNT hNR
  obtain ⟨Nd,hd⟩ := information_weighted_deep_eventually 1 1 (betaMin*Real.log 2/8)
    (by norm_num) (by positivity)
  obtain ⟨Ns,hs⟩ := eventually_atTop.1 (constant_exp_saddle_le_power_eventually 2 1 (1/6+epsilon) (by norm_num) (by positivity))
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hnu := (tendsto_saddleNu_atTop (a := 1) (by norm_num)).comp hlog
  obtain ⟨Nnu,hnu⟩ := eventually_atTop.1 (hnu.eventually (eventually_ge_atTop (0 : ℝ)))
  refine ⟨max Np (max Nd (max Ns (max Nnu 2))),?_⟩
  intro M hM L hlo hhi A hpos hrate hbudget
  have hnu0 : 0≤saddleNu 1 (Real.log M) := hnu M (by omega)
  obtain ⟨hI,_,hw⟩ := aggregate_parameters_le (eventInformation_nonneg A hpos) hrate hc hnu0 hbudget
  have hpre := hp M (by omega) L (by simpa using hlo) (by simpa using hhi) (1/2) (by norm_num) (by norm_num)
  have hsum : (∑ x∈containedStarts M L\bulkStarts M L (1/2),infiniteStartProbability x L)≤
      (M : ℝ)^(1/2 : ℝ)/(2 : ℝ)^L+
        2*Real.exp (-(betaMin*Real.log 2/8)*(Real.log M/Real.log (Real.log M))) :=
    (Finset.sum_le_sum_of_subset_of_nonneg (removed_contained_subset_prefix M L (1/2))
      (fun x _ _ => ENNReal.toReal_nonneg)).trans hpre
  have htar := removed_contained_rate_le M L (1/2)
  have hdeep := hd M (by omega) (eventInformation A) (by simpa using hI)
  have hexp : 1≤Real.exp (eventInformation A) := Real.one_le_exp_iff.mpr (eventInformation_nonneg A hpos)
  have hsmall : 2*Real.exp (eventInformation A)*((M : ℝ)^(1/2 : ℝ)/(2 : ℝ)^L)≤
      (M : ℝ)^(-(1/3 : ℝ)+epsilon) := by
    have heq : (M : ℝ)^(1/2 : ℝ)/(2 : ℝ)^L=
        (fullRate M L : ℝ)*(M : ℝ)^(-(1/2 : ℝ)) := by
      rw [prefix_bulk_term_eq M L (1/2) (by omega)]
      congr 2
      ring
    rw [heq]
    have hh := mul_le_mul_of_nonneg_right hw (by positivity : 0≤2*(M : ℝ)^(-(1/2 : ℝ)))
    have hpw := mul_le_mul_of_nonneg_right (hs M (by omega)) (by positivity : 0≤(M : ℝ)^(-(1/2 : ℝ)))
    simp only [one_mul] at hpw
    have he : (M : ℝ)^(1/6+epsilon)*(M : ℝ)^(-(1/2 : ℝ))=(M : ℝ)^(-(1/3 : ℝ)+epsilon) := by
      rw [← Real.rpow_add (by exact_mod_cast (show 0<M by omega))]
      congr 1
      ring
    rw [he] at hpw
    nlinarith only [hh,hpw]
  have hsum' := mul_le_mul_of_nonneg_left hsum (Real.exp_nonneg (eventInformation A))
  have htar' : (maskRate L (containedStarts M L\bulkStarts M L (1/2)) : ℝ)≤
      Real.exp (eventInformation A)*((M : ℝ)^(1/2 : ℝ)/(2 : ℝ)^L) :=
    htar.trans (le_mul_of_one_le_left (by positivity) hexp)
  have hdexp : Real.exp (-((betaMin*Real.log 2/8)/2)*(Real.log M/Real.log (Real.log M)))=
      Real.exp (-(betaMin*Real.log 2/16)*(Real.log M/Real.log (Real.log M))) := by congr 1;ring
  rw [hdexp] at hdeep
  rw [div_eq_mul_inv,← exp_eventInformation A hpos]
  nlinarith only [hsum',htar',hsmall,hdeep]

end
end PaperC.V282.MacroAggregateRestoration
