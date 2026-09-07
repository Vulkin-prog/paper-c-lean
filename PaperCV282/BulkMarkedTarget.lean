import PaperCV282.BulkMarkedTypes
import PaperCV282.GeometricMarkedConfiguration
import PaperCV282.SpatialMarkedTarget

/-!
# The actual spatial, excess and sign resolved Poisson configuration

Each spatial site and sign receives its own independent geometric Poisson
configuration. The resulting configuration has finite support, even though
all excess marks are retained. The construction also applies to an empty grid.
-/
namespace PaperC.V282.BulkMarkedTarget

open MeasureTheory ProbabilityTheory BulkMarkedTypes GeometricMarkedConfiguration
open GeometricClusterTruncation ExactMarkedModel
open SpatialMarkedTarget
open scoped BigOperators NNReal ENNReal

noncomputable section

def spatialRowsMeasure (sites : Finset ℕ) (L : ℕ) : Measure (({x : ℕ // x ∈ sites} × F₂) → (ℕ →₀ ℕ)) :=
  Measure.pi (fun _ : {x : ℕ // x ∈ sites} × F₂ => configurationMeasure (signedSiteRate L))

instance instProbabilitySpatialRows (sites : Finset ℕ) (L : ℕ) : IsProbabilityMeasure (spatialRowsMeasure sites L) := by
  unfold spatialRowsMeasure
  infer_instance

def flattenRows (sites : Finset ℕ) (rows : ({x : ℕ // x ∈ sites} × F₂) → (ℕ →₀ ℕ)) : SpatialMarkedConfig sites := by
  classical
  exact Finsupp.onFinset
    (Finset.univ.biUnion (fun i : {x : ℕ // x ∈ sites} × F₂ =>
      (rows i).support.image (fun e => (i.1, (e, i.2)))))
    (fun j => rows (j.1, j.2.2) j.2.1) (by
      intro j hj
      exact Finset.mem_biUnion.mpr ⟨(j.1,j.2.2),Finset.mem_univ _,
        Finset.mem_image.mpr ⟨j.2.1,Finsupp.mem_support_iff.mpr hj,rfl⟩⟩)

theorem flattenRows_apply (sites : Finset ℕ) (rows : ({x : ℕ // x ∈ sites} × F₂) → (ℕ →₀ ℕ))
    (j : SpatialMarkedIndex sites) : flattenRows sites rows j = rows (j.1,j.2.2) j.2.1 := rfl

def spatialTargetMeasure (sites : Finset ℕ) (L : ℕ) : Measure (SpatialMarkedConfig sites) :=
  (spatialRowsMeasure sites L).map (flattenRows sites)

instance instProbabilitySpatialTarget (sites : Finset ℕ) (L : ℕ) : IsProbabilityMeasure (spatialTargetMeasure sites L) := by
  unfold spatialTargetMeasure
  exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

theorem hasLaw_flattenRows (sites : Finset ℕ) (L : ℕ) :
    HasLaw (flattenRows sites) (spatialTargetMeasure sites L) (spatialRowsMeasure sites L) :=
  ⟨(measurable_of_countable _).aemeasurable,rfl⟩

theorem hasLaw_spatial_row (sites : Finset ℕ) (L : ℕ) (i : {x : ℕ // x ∈ sites} × F₂) :
    HasLaw (fun rows => rows i) (configurationMeasure (signedSiteRate L)) (spatialRowsMeasure sites L) :=
  (measurePreserving_eval (fun _ : {x : ℕ // x ∈ sites} × F₂ => configurationMeasure (signedSiteRate L)) i).hasLaw

theorem independent_spatial_rows (sites : Finset ℕ) (L : ℕ) :
    iIndepFun (fun i (rows : ({x : ℕ // x ∈ sites} × F₂) → (ℕ →₀ ℕ)) => rows i) (spatialRowsMeasure sites L) :=
  iIndepFun_pi (fun _ => measurable_id.aemeasurable)

end
end PaperC.V282.BulkMarkedTarget
