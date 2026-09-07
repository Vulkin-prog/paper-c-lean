import PaperCV282.BulkMarkedTarget

/-! # Every finite spatial target projection has the exact signed product law -/
namespace PaperC.V282.BulkMarkedTargetProjection

open MeasureTheory ProbabilityTheory BulkMarkedTypes BulkMarkedTarget BulkSupportGraph
open SpatialMarkedTarget (signedSiteRate signedSiteRate_coordinate_eq)
open GeometricMarkedConfiguration GeometricClusterTruncation ExactMarkedModel
open BulkMarkedTransfer PoissonFieldMeasure ConditionalStartProbability
open scoped BigOperators NNReal ENNReal

noncomputable section

def reindexFiniteRows (sites : Finset ℕ) (E : ℕ) (k : ({x : ℕ // x ∈ sites} × F₂) → Fin (E+1) → ℕ)
    (i : LabelledIndex sites (Fin (E+1) × F₂)) : ℕ := k (i.1,i.2.2) i.2.1

theorem hasLaw_rowProjections (sites : Finset ℕ) (L E : ℕ) :
    HasLaw (fun rows : ({x : ℕ // x ∈ sites} × F₂) → (ℕ →₀ ℕ) => fun i => fun e : Fin (E+1) => rows i e.val)
      (Measure.pi (fun _ : {x : ℕ // x ∈ sites} × F₂ => fieldMeasure (geometricCoordinateRates (signedSiteRate L) E)))
      (spatialRowsMeasure sites L) := by
  refine ⟨(measurable_of_countable _).aemeasurable,?_⟩
  rw [spatialRowsMeasure,Measure.pi_map_pi
    (f := fun _ : {x : ℕ // x ∈ sites} × F₂ => fun config : ℕ →₀ ℕ => fun e : Fin (E+1) => config e.val)
    (fun _ => (measurable_of_countable _).aemeasurable)]
  congr 1
  funext i
  exact (hasLaw_finite_configuration (signedSiteRate L) E).map_eq

theorem hasLaw_reindexFiniteRows (sites : Finset ℕ) (L E : ℕ) :
    HasLaw (reindexFiniteRows sites E) (fieldMeasure (allSignedRates sites L E (sites)))
      (Measure.pi (fun _ : {x : ℕ // x ∈ sites} × F₂ => fieldMeasure (geometricCoordinateRates (signedSiteRate L) E))) := by
  classical
  refine ⟨(measurable_of_countable _).aemeasurable,?_⟩
  apply Measure.ext_of_singleton
  intro k
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have hpre : reindexFiniteRows sites E ⁻¹' {k} =
      {fun i : {x : ℕ // x ∈ sites} × F₂ => fun e : Fin (E+1) => k (i.1,(e,i.2))} := by
    ext v
    simp only [Set.mem_preimage,Set.mem_singleton_iff]
    constructor
    · intro h
      funext i e
      have hh := congrFun h (i.1,(e,i.2))
      simpa only [reindexFiniteRows] using hh
    · intro h
      subst v
      funext i
      simp only [reindexFiniteRows]
  rw [hpre]
  have hrate (i : LabelledIndex sites (Fin (E+1) × F₂)) :
      allSignedRates sites L E (sites) i = signedMarkRate L i.2.1.val := if_pos i.1.property
  simp only [fieldMeasure,Measure.pi_singleton,Fintype.prod_prod_type]
  simp_rw [signedSiteRate_coordinate_eq,hrate]
  calc
    _ = ∏ x : sites, ∏ e : Fin (E+1), ∏ s : F₂,
        poissonMeasure (signedMarkRate L e.val) {k (x,(e,s))} := by
      apply Finset.prod_congr rfl
      intro x hx
      exact Finset.prod_comm
    _ = _ := rfl

/-- This is the full joint law on the old finite signed carrier, including all spatial labels. -/
theorem hasLaw_projectConfiguration (sites : Finset ℕ) (L E : ℕ) :
    HasLaw (projectConfiguration sites E) (fieldMeasure (allSignedRates sites L E (sites)))
      (spatialTargetMeasure sites L) := by
  have h := (hasLaw_reindexFiniteRows sites L E).fun_comp (hasLaw_rowProjections sites L E)
  refine ⟨(measurable_of_countable _).aemeasurable,?_⟩
  rw [spatialTargetMeasure,Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  exact h.map_eq

theorem spatial_project_mass_eq (sites : Finset ℕ) (L E : ℕ) (k : LabelledIndex sites (Fin (E+1) × F₂) → ℕ) :
    (spatialTargetMeasure sites L).real {config | projectConfiguration sites E config = k} =
      FiniteFieldPoissonCoupling.poissonFieldMass (allSignedRates sites L E (sites)) k := by
  exact ((hasLaw_projectConfiguration sites L E).measureReal_eq (measurableSet_singleton k)).trans
    (fieldMeasure_real_singleton _ k)

end
end PaperC.V282.BulkMarkedTargetProjection
