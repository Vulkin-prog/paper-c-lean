import PaperCV282.SpatialMarkedTypes
import PaperCV282.GeometricMarkedConfiguration
import PaperCV282.ExactMarkedFieldTransfer

/-!
# The actual spatial, excess and sign resolved Poisson configuration

Each spatial site and sign receives its own independent geometric Poisson
configuration. The resulting configuration has finite support, even though
all excess marks are retained. The construction also applies to an empty grid.
-/
namespace PaperC.V282.SpatialMarkedTarget

open MeasureTheory ProbabilityTheory SpatialMarkedTypes GeometricMarkedConfiguration
open GeometricClusterTruncation ExactMarkedModel
open scoped BigOperators NNReal ENNReal

noncomputable section

def signedSiteRate (L : ℕ) : ℝ≥0 := 1 / 2 ^ (L + 1)

def spatialRowsMeasure (N L : ℕ) : Measure ((Fin N × F₂) → (ℕ →₀ ℕ)) :=
  Measure.pi (fun _ : Fin N × F₂ => configurationMeasure (signedSiteRate L))

instance instProbabilitySpatialRows (N L : ℕ) : IsProbabilityMeasure (spatialRowsMeasure N L) := by
  unfold spatialRowsMeasure
  infer_instance

def flattenRows (N : ℕ) (rows : (Fin N × F₂) → (ℕ →₀ ℕ)) : SpatialMarkedConfig N := by
  classical
  exact Finsupp.onFinset
    (Finset.univ.biUnion (fun i : Fin N × F₂ =>
      (rows i).support.image (fun e => (i.1, (e, i.2)))))
    (fun j => rows (j.1, j.2.2) j.2.1) (by
      intro j hj
      exact Finset.mem_biUnion.mpr ⟨(j.1,j.2.2),Finset.mem_univ _,
        Finset.mem_image.mpr ⟨j.2.1,Finsupp.mem_support_iff.mpr hj,rfl⟩⟩)

theorem flattenRows_apply (N : ℕ) (rows : (Fin N × F₂) → (ℕ →₀ ℕ))
    (j : SpatialMarkedIndex N) : flattenRows N rows j = rows (j.1,j.2.2) j.2.1 := rfl

def spatialTargetMeasure (N L : ℕ) : Measure (SpatialMarkedConfig N) :=
  (spatialRowsMeasure N L).map (flattenRows N)

instance instProbabilitySpatialTarget (N L : ℕ) : IsProbabilityMeasure (spatialTargetMeasure N L) := by
  unfold spatialTargetMeasure
  exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

theorem hasLaw_flattenRows (N L : ℕ) :
    HasLaw (flattenRows N) (spatialTargetMeasure N L) (spatialRowsMeasure N L) :=
  ⟨(measurable_of_countable _).aemeasurable,rfl⟩

theorem hasLaw_spatial_row (N L : ℕ) (i : Fin N × F₂) :
    HasLaw (fun rows => rows i) (configurationMeasure (signedSiteRate L)) (spatialRowsMeasure N L) :=
  (measurePreserving_eval (fun _ : Fin N × F₂ => configurationMeasure (signedSiteRate L)) i).hasLaw

theorem independent_spatial_rows (N L : ℕ) :
    iIndepFun (fun i (rows : (Fin N × F₂) → (ℕ →₀ ℕ)) => rows i) (spatialRowsMeasure N L) :=
  iIndepFun_pi (fun _ => measurable_id.aemeasurable)

theorem signedSiteRate_coordinate_eq (L E : ℕ) (e : Fin (E+1)) :
    geometricCoordinateRates (signedSiteRate L) E e = signedMarkRate L e.val := by
  apply NNReal.coe_injective
  change (1 : ℝ) / 2 ^ (L+1) / 2 ^ (e.val+1) = 1 / 2 ^ (L+e.val+2)
  rw [show L+e.val+2=(L+1)+(e.val+1) by omega,pow_add]
  field_simp
  simp only [pow_add,pow_succ,mul_assoc]

end
end PaperC.V282.SpatialMarkedTarget
