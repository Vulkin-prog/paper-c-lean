import PaperCV282.QuenchedSpatialClosure
import PaperCV282.QuenchedBudgetDomain

/-! # The labelled budget supplies the moving-depth domain automatically -/
namespace PaperC.V282.QuenchedSpatialDomain

open MeasureTheory Filter Topology InfiniteRademacher GrowingLevelParameters
open QuenchedSpatialClosure QuenchedBudgetDomain LabelledInformationBudget
open GeometricSaddleSummability GeometricScaleInstances AllStartSoftPoisson
open SaddleParameters SaddleScales ProcessAGGInput PrimeEulerPNT

noncomputable section

/-- Removing the extra log(1+lambda) cost leaves the established one-intensity domain. -/
theorem log_rate_le_labelled_cost (N L : ℕ) :
    Real.log (fullRate N L)≤labelledLogCost 0 (fullRate N L) := by
  have hn : 0≤Real.log (1+(fullRate N L : ℝ)) :=
    Real.log_nonneg (by have hh := (fullRate N L).coe_nonneg;linarith)
  unfold labelledLogCost
  linarith

/-- Literal labelled Corollary6.4: no independently supplied depth-growth hypothesis. -/
theorem corollary_six_four_labelled (hAGG : ProcessAGGStatement)
    (hPNT : PrimeNumberTheoremRemainder) (sizes depths : ℕ → ℕ)
    (hg : GeometricLowerGrowth sizes) (c beta : ℝ) (hbeta : 0<beta) (hcb : beta<c)
    (hbudget : ∀ᶠ k in atTop,
      labelledLogCost 0 (fullRate (sizes k) (movingLength (sizes k) (depths k)))≤
        saddleCutoff 1 (Real.log (sizes k))-c*saddleNu 1 (Real.log (sizes k))) :
    ∀ᵐ omega ∂infiniteRademacherMeasure, ∀ᶠ k in atTop,
      spatialEnvironmentDistance (sizes k) (movingLength (sizes k) (depths k)) omega ≤
        Real.exp (-beta*saddleNu 1 (Real.log (sizes k))) := by
  have hlog : ∀ᶠ k in atTop,
      Real.log (fullRate (sizes k) (movingLength (sizes k) (depths k)))≤
        saddleCutoff 1 (Real.log (sizes k))-c*saddleNu 1 (Real.log (sizes k)) := by
    filter_upwards [hbudget] with k hk
    exact (log_rate_le_labelled_cost _ _).trans hk
  have hd := depth_div_log_tendsto_zero_of_saddle_budget sizes depths
    (sizes_tendsto_atTop hg) 1 c (by norm_num) (by linarith) hlog
  exact QuenchedSpatialClosure.corollary_six_four_labelled hAGG hPNT sizes depths hg hd
    c beta hbeta hcb hbudget

end
end PaperC.V282.QuenchedSpatialDomain
