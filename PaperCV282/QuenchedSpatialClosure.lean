import PaperCV282.MeanSpatialBudget
import PaperCV282.QuenchedAggregateTheorem

/-! # The labelled quenched conclusion in its own information domain -/
namespace PaperC.V282.QuenchedSpatialClosure

open MeasureTheory Filter Topology InfiniteRademacher InfiniteCylinderTransfer
open FinitePrimeEnvironment MeanSpatialBudget QuenchedBorelCantelli GeometricSaddleSummability
open GeometricScaleInstances SpatialMarkedSource SpatialMarkedFieldComparison
open SignedAggregateHardBudget GrowingLevelParameters AllStartSoftPoisson SaddleParameters SaddleScales
open ProcessAGGInput PrimeEulerPNT HardPoissonRates LabelledInformationBudget

noncomputable section

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

def spatialEnvironmentDistance (N L : ℕ) : InfiniteSample → ℝ :=
  environmentDistance (hardCutoff N) (hardCutoff N) (spatialMarkedSource N L) (spatialTargetLaw N L)

/-- The full labelled configuration is close in almost every prime environment. -/
theorem corollary_six_four_labelled (hAGG : ProcessAGGStatement)
    (hPNT : PrimeNumberTheoremRemainder) (sizes depths : ℕ → ℕ)
    (hg : GeometricLowerGrowth sizes)
    (hdepths : Tendsto (fun k => (depths k : ℝ)/Real.log (sizes k)) atTop (𝓝 0))
    (c beta : ℝ) (hbeta : 0<beta) (hcb : beta<c)
    (hbudget : ∀ᶠ k in atTop, labelledLogCost 0 (fullRate (sizes k) (movingLength (sizes k) (depths k)))≤
      saddleCutoff 1 (Real.log (sizes k))-c*saddleNu 1 (Real.log (sizes k))) :
    ∀ᵐ omega ∂infiniteRademacherMeasure, ∀ᶠ k in atTop,
      spatialEnvironmentDistance (sizes k) (movingLength (sizes k) (depths k)) omega ≤
        Real.exp (-beta*saddleNu 1 (Real.log (sizes k))) := by
  have hsizes := sizes_tendsto_atTop hg
  have hlog2 : 0<Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let lo := 1/(2*Real.log 2)
  let hi := 2/Real.log 2
  have hlo : 0<lo := by dsimp [lo];positivity
  have hlomid : lo<1/Real.log 2 := by dsimp [lo];apply (div_lt_div_iff₀ (by positivity) hlog2).mpr;nlinarith
  have hhimid : 1/Real.log 2<hi := by dsimp [hi];exact div_lt_div_of_pos_right (by norm_num) hlog2
  have hband := moving_sequence_domain_eventually sizes depths hsizes hdepths lo hi hlomid hhimid
  obtain ⟨Nzero,hzero⟩ := integral_spatial_hard_rate hAGG hPNT lo hi c ((c+beta)/2)
    hlo (hlomid.trans hhimid) (by linarith) (by linarith)
  have hmean : ∀ᶠ k in atTop,
      (∫ omega, spatialEnvironmentDistance (sizes k) (movingLength (sizes k) (depths k)) omega
        ∂infiniteRademacherMeasure) ≤
      67*Real.exp (-((c+beta)/2)*saddleNu 1 (Real.log (sizes k)))+(sizes k : ℝ)^(-(1/6 : ℝ)) := by
    filter_upwards [hband,hbudget,hsizes.eventually (eventually_ge_atTop Nzero)] with k hb hbu hn
    have hh := hzero (sizes k) hn (movingLength (sizes k) (depths k)) hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2 hbu
    exact hh.trans (le_add_of_nonneg_right (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  exact ae_eventually_saddle_bound infiniteRademacherMeasure
    (fun k => spatialEnvironmentDistance (sizes k) (movingLength (sizes k) (depths k)))
    (fun _ => integrable_environmentDistance _ _ _ _) (fun _ => environmentDistance_nonneg _ _ _ _)
    sizes hg 1 ((c+beta)/2) beta (1/6) 67 (by norm_num) (by linarith) (by norm_num) hmean


end
end PaperC.V282.QuenchedSpatialClosure
