import PaperCV282.SpatialPointEmbedding

/-! # Weak convergence to the diffuse, countably marked Poisson law

The limiting law is an actual Poisson number of independent marks with
uniform positions on [1,2], geometric excesses and uniform signs. Arbitrary
subsequences of positive spatial scales are permitted; positivity is only
eventual, as implied by their divergence to infinity.
-/
namespace PaperC.V282.SpatialPointConvergence

open MeasureTheory ProbabilityTheory Filter PointMeasureSpace SpatialDiffuseMarks
open SpatialPointEmbedding PoissonPointProcess UniformSpatialGrid AllStartSoftPoisson
open scoped NNReal Topology

noncomputable section

def diffusePoissonLaw (rate : ℝ≥0) : ProbabilityMeasure (PointMeasure (ℝ × (ℕ × F₂))) :=
  poissonPointLaw rate spatialMarkMeasure continuousMark measurable_continuousMark

theorem gridPhysicalMark_tendsto (sizes : ℕ → ℕ) (hpos : ∀ n, 0 < sizes n)
    (hsizes : Tendsto sizes atTop atTop) (x : unitInterval × (ℕ × F₂)) :
    Tendsto (fun n => gridPhysicalMark (sizes n) (hpos n) x) atTop (𝓝 (continuousMark x)) := by
  exact (physical_grid_position_tendsto sizes hpos hsizes x.1).prodMk_nhds tendsto_const_nhds

/-- The true complete spatial product target, embedded as a finite measure,
converges weakly to the diffuse marked Poisson law along any admissible
subsequence of sizes. No finite mark truncation remains in the statement. -/
theorem spatialPointTargetLaw_tendsto (sizes lengths : ℕ → ℕ) (rate : ℝ≥0)
    (hsizes : Tendsto sizes atTop atTop)
    (hrate : Tendsto (fun n => (fullRate (sizes n) (lengths n) : ℝ)) atTop (𝓝 (rate : ℝ))) :
    Tendsto (fun n => spatialPointTargetLaw (sizes n) (lengths n)) atTop
      (𝓝 (diffusePoissonLaw rate)) := by
  let positiveSizes : ℕ → ℕ := fun n => max 1 (sizes n)
  have hpos : ∀ n, 0 < positiveSizes n := fun n => lt_of_lt_of_le (by omega) (le_max_left _ _)
  have hlim : Tendsto positiveSizes atTop atTop :=
    tendsto_atTop_mono (fun n => le_max_right 1 (sizes n)) hsizes
  have h := poissonPointLaw_tendsto spatialMarkMeasure
    (fun n => fullRate (sizes n) (lengths n)) rate hrate
    (fun n => gridPhysicalMark (positiveSizes n) (hpos n)) continuousMark
    (fun n => measurable_gridPhysicalMark _ _) measurable_continuousMark
    (gridPhysicalMark_tendsto positiveSizes hpos hlim)
  apply h.congr'
  filter_upwards [hsizes.eventually_ge_atTop 1] with n hn
  have hnpos : 0 < sizes n := by omega
  have heq : positiveSizes n = sizes n := max_eq_right hn
  have hemb : gridPhysicalMark (positiveSizes n) (hpos n) = gridPhysicalMark (sizes n) hnpos := by
    funext x
    simp only [gridPhysicalMark, spatialPosition, gridMark, gridSite, heq]
  apply Eq.trans _ (spatialPointTargetLaw_eq_poissonPointLaw (sizes n) (lengths n) hnpos).symm
  apply Subtype.ext
  change (GeneralPoissonMarking.markSampleMeasure _ _).map (mappedPointMeasure _) =
    (GeneralPoissonMarking.markSampleMeasure _ _).map (mappedPointMeasure _)
  rw [hemb]

end
end PaperC.V282.SpatialPointConvergence
