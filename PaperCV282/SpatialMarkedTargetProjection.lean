import PaperCV282.SpatialMarkedTarget

/-! # Every finite spatial target projection has the exact signed product law -/
namespace PaperC.V282.SpatialMarkedTargetProjection

open MeasureTheory ProbabilityTheory SpatialMarkedTypes SpatialMarkedTarget
open GeometricMarkedConfiguration GeometricClusterTruncation ExactMarkedModel
open ExactMarkedFieldTransfer PoissonFieldMeasure ConditionalStartProbability
open scoped BigOperators NNReal ENNReal

noncomputable section

def reindexFiniteRows (N E : ℕ) (k : (Fin N × F₂) → Fin (E+1) → ℕ)
    (i : SignedMarkIndex N E) : ℕ := k ((dyadicSiteEquiv N).symm i.1,i.2.2) i.2.1

theorem hasLaw_rowProjections (N L E : ℕ) :
    HasLaw (fun rows : (Fin N × F₂) → (ℕ →₀ ℕ) => fun i => fun e : Fin (E+1) => rows i e.val)
      (Measure.pi (fun _ : Fin N × F₂ => fieldMeasure (geometricCoordinateRates (signedSiteRate L) E)))
      (spatialRowsMeasure N L) := by
  refine ⟨(measurable_of_countable _).aemeasurable,?_⟩
  rw [spatialRowsMeasure,Measure.pi_map_pi
    (f := fun _ : Fin N × F₂ => fun config : ℕ →₀ ℕ => fun e : Fin (E+1) => config e.val)
    (fun _ => (measurable_of_countable _).aemeasurable)]
  congr 1
  funext i
  exact (hasLaw_finite_configuration (signedSiteRate L) E).map_eq

theorem hasLaw_reindexFiniteRows (N L E : ℕ) :
    HasLaw (reindexFiniteRows N E) (fieldMeasure (allSignedRates N L E (dyadicBlock N)))
      (Measure.pi (fun _ : Fin N × F₂ => fieldMeasure (geometricCoordinateRates (signedSiteRate L) E))) := by
  classical
  refine ⟨(measurable_of_countable _).aemeasurable,?_⟩
  apply Measure.ext_of_singleton
  intro k
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have hpre : reindexFiniteRows N E ⁻¹' {k} =
      {fun i : Fin N × F₂ => fun e : Fin (E+1) => k (dyadicSiteEquiv N i.1,(e,i.2))} := by
    ext v
    simp only [Set.mem_preimage,Set.mem_singleton_iff]
    constructor
    · intro h
      funext i e
      have hh := congrFun h (dyadicSiteEquiv N i.1,(e,i.2))
      simpa only [reindexFiniteRows,Equiv.symm_apply_apply] using hh
    · intro h
      subst v
      funext i
      simp only [reindexFiniteRows,Equiv.apply_symm_apply]
  rw [hpre]
  have hrate (i : SignedMarkIndex N E) :
      allSignedRates N L E (dyadicBlock N) i = signedMarkRate L i.2.1.val := if_pos i.1.property
  simp only [fieldMeasure,Measure.pi_singleton,Fintype.prod_prod_type]
  simp_rw [signedSiteRate_coordinate_eq,hrate]
  calc
    _ = ∏ x : Fin N, ∏ e : Fin (E+1), ∏ s : F₂,
        poissonMeasure (signedMarkRate L e.val) {k (dyadicSiteEquiv N x,(e,s))} := by
      apply Finset.prod_congr rfl
      intro x hx
      exact Finset.prod_comm
    _ = _ := (dyadicSiteEquiv N).prod_comp
      (fun x => ∏ e : Fin (E+1), ∏ s : F₂, poissonMeasure (signedMarkRate L e.val) {k (x,(e,s))})

/-- This is the full joint law on the old finite signed carrier, including all spatial labels. -/
theorem hasLaw_projectConfiguration (N L E : ℕ) :
    HasLaw (projectConfiguration N E) (fieldMeasure (allSignedRates N L E (dyadicBlock N)))
      (spatialTargetMeasure N L) := by
  have h := (hasLaw_reindexFiniteRows N L E).fun_comp (hasLaw_rowProjections N L E)
  refine ⟨(measurable_of_countable _).aemeasurable,?_⟩
  rw [spatialTargetMeasure,Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  exact h.map_eq

theorem spatial_project_mass_eq (N L E : ℕ) (k : SignedMarkIndex N E → ℕ) :
    (spatialTargetMeasure N L).real {config | projectConfiguration N E config = k} =
      FiniteFieldPoissonCoupling.poissonFieldMass (allSignedRates N L E (dyadicBlock N)) k := by
  exact ((hasLaw_projectConfiguration N L E).measureReal_eq (measurableSet_singleton k)).trans
    (fieldMeasure_real_singleton _ k)

end
end PaperC.V282.SpatialMarkedTargetProjection
