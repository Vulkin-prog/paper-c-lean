import PaperCV282.SpatialMarkedTargetAggregation
import PaperCV282.CompoundPoissonTransform

/-! # The complete spatial target contracts to the genuine compound cluster law -/
namespace PaperC.V282.SpatialMarkedTargetCompound

open MeasureTheory ProbabilityTheory SpatialMarkedTypes SpatialMarkedTarget SpatialMarkedTargetTail
open SpatialMarkedTargetAggregation GeometricMarkedConfiguration GeometricClusterTarget
open CompoundPoissonTransform AllStartSoftPoisson
open scoped BigOperators NNReal ENNReal

noncomputable section

theorem spatial_weight_complex_transform (N L : ℕ) (z : ℂ) (hz : ‖z‖≤1) :
    (∫ config, z ^ totalSpatialWeight N config ∂spatialTargetMeasure N L) =
      Complex.exp ((fullRate N L : ℂ)*((∫ h : ℕ, z^h ∂geometricClusterMeasure)-1)) := by
  rw [spatialTargetMeasure,integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable]
  simp_rw [totalSpatialWeight_flattenRows,← Finset.prod_pow_eq_pow_sum]
  have hd := (independent_spatial_rows N L).comp
    (fun _ => fun row : ℕ →₀ ℕ => z ^ configurationWeight row) (fun _ => measurable_of_countable _)
  have hp := hd.integral_fun_prod_eq_prod_integral
    (fun i => ((measurable_of_countable (fun row : ℕ →₀ ℕ => z ^ configurationWeight row)).comp
      (measurable_pi_apply i)).aestronglyMeasurable)
  simp only [Function.comp_apply] at hp
  rw [hp]
  have hrow (i : Fin N × F₂) :
      (∫ rows, z ^ configurationWeight (rows i) ∂spatialRowsMeasure N L) =
        Complex.exp ((signedSiteRate L : ℂ)*((∫ h : ℕ, z^h ∂geometricClusterMeasure)-1)) :=
    (((hasLaw_configurationWeight (signedSiteRate L)).fun_comp (hasLaw_spatial_row N L i)).integral_comp
      (measurable_of_countable (fun n : ℕ => z^n)).aestronglyMeasurable).trans
        (compound_complex_transform (signedSiteRate L) geometricClusterMeasure hz)
  simp_rw [hrow]
  rw [← Complex.exp_sum,← Finset.sum_mul]
  have hr : (∑ _ : Fin N × F₂, (signedSiteRate L : ℂ))=(fullRate N L : ℂ) := by
    exact_mod_cast sum_signedSiteRate N L
  rw [hr]

/-- The unbounded geometric weight is an actual compound-Poisson law, with all labels retained first. -/
theorem hasLaw_totalSpatialWeight (N L : ℕ) :
    HasLaw (totalSpatialWeight N) (geometricCompoundMeasure (fullRate N L)) (spatialTargetMeasure N L) := by
  refine ⟨(measurable_of_countable _).aemeasurable,?_⟩
  letI : IsProbabilityMeasure ((spatialTargetMeasure N L).map (totalSpatialWeight N)) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  apply natural_law_eq_of_unit_transforms
  intro z hz
  rw [integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable (fun n : ℕ => z^n)).aestronglyMeasurable,
    spatial_weight_complex_transform N L z hz.le]
  exact (compound_complex_transform (fullRate N L) geometricClusterMeasure hz.le).symm

end
end PaperC.V282.SpatialMarkedTargetCompound
