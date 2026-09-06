import PaperCV282.SpatialMarkedTypes
import PaperCV282.PoissonFieldMeasure

/-! # Complete spatial configuration laws are determined by their finite mark projections -/
namespace PaperC.V282.SpatialMarkedLawExt

open MeasureTheory ProbabilityTheory SpatialMarkedTypes ExactMarkedModel

noncomputable section

theorem project_eq_iff {N E : ℕ} (config target : SpatialMarkedConfig N) :
    projectConfiguration N E config=projectConfiguration N E target ↔
      ∀ j : SpatialMarkedIndex N, j.2.1≤E → config j=target j := by
  constructor
  · intro h j hj
    obtain ⟨i,rfl⟩ := (finiteMarkedEmbedding_range N E j).mpr hj
    exact congrFun h i
  · intro h
    funext i
    exact h (finiteMarkedEmbedding N E i) (Nat.le_of_lt_succ i.2.1.isLt)

theorem configuration_eq_iff_all_projections {N : ℕ} (config target : SpatialMarkedConfig N) :
    config=target ↔ ∀ E : ℕ, projectConfiguration N E config=projectConfiguration N E target := by
  constructor
  · rintro rfl E
    rfl
  · intro h
    ext j
    exact (project_eq_iff config target).mp (h j.2.1) j le_rfl

def projectionFiber (N E : ℕ) (target : SpatialMarkedConfig N) : Set (SpatialMarkedConfig N) :=
  {config | projectConfiguration N E config=projectConfiguration N E target}

theorem projectionFiber_antitone (N : ℕ) (target : SpatialMarkedConfig N) :
    Antitone (fun E => projectionFiber N E target) := by
  intro E F hEF config hconfig
  apply (project_eq_iff config target).mpr
  intro j hj
  exact (project_eq_iff config target).mp hconfig j (hj.trans hEF)

theorem singleton_eq_iInter_projectionFiber (N : ℕ) (target : SpatialMarkedConfig N) :
    {target}=⋂ E : ℕ, projectionFiber N E target := by
  ext config
  simp only [Set.mem_singleton_iff,Set.mem_iInter,projectionFiber,Set.mem_setOf_eq]
  exact configuration_eq_iff_all_projections config target

/-- Finite measures are identified by all exact finite mark-projection laws. -/
theorem spatialMarkedMeasure_ext {N : ℕ} (mu nu : Measure (SpatialMarkedConfig N))
    [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (h : ∀ E : ℕ, mu.map (projectConfiguration N E)=nu.map (projectConfiguration N E)) :
    mu=nu := by
  apply Measure.ext_of_singleton
  intro target
  rw [singleton_eq_iInter_projectionFiber]
  rw [(projectionFiber_antitone N target).measure_iInter
      (fun E => (Set.to_countable (projectionFiber N E target)).measurableSet.nullMeasurableSet)
      ⟨0,measure_ne_top _ _⟩,
    (projectionFiber_antitone N target).measure_iInter
      (fun E => (Set.to_countable (projectionFiber N E target)).measurableSet.nullMeasurableSet)
      ⟨0,measure_ne_top _ _⟩]
  congr 1
  funext E
  have he := congrArg (fun m : Measure (SignedMarkIndex N E → ℕ) =>
    m {projectConfiguration N E target}) (h E)
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
    Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)] at he
  have hset : projectConfiguration N E ⁻¹' {projectConfiguration N E target}=
      projectionFiber N E target := by
    ext config
    simp [projectionFiber]
  rw [hset] at he
  exact he

/-- A measurable configuration with all the target projection laws has the entire target law. -/
theorem hasLaw_of_all_projections {Omega : Type*} [MeasurableSpace Omega] {N : ℕ}
    (mu : Measure Omega) (nu : Measure (SpatialMarkedConfig N))
    [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (X : Omega → SpatialMarkedConfig N) (hX : Measurable X)
    (h : ∀ E : ℕ, HasLaw (fun omega => projectConfiguration N E (X omega))
      (nu.map (projectConfiguration N E)) mu) : HasLaw X nu mu := by
  refine ⟨hX.aemeasurable,?_⟩
  apply spatialMarkedMeasure_ext
  intro E
  rw [Measure.map_map (measurable_of_countable _) hX]
  exact (h E).map_eq

/-- Matching joint laws for each finite projection suffice, without a separate tail hypothesis. -/
theorem hasLaw_of_matching_projection_laws {Omega : Type*} [MeasurableSpace Omega] {N : ℕ}
    (mu : Measure Omega) (nu : Measure (SpatialMarkedConfig N))
    [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (X : Omega → SpatialMarkedConfig N) (hX : Measurable X)
    (laws : ∀ E : ℕ, Measure (SignedMarkIndex N E → ℕ))
    (hsource : ∀ E, HasLaw (fun omega => projectConfiguration N E (X omega)) (laws E) mu)
    (htarget : ∀ E, HasLaw (projectConfiguration N E) (laws E) nu) : HasLaw X nu mu := by
  apply hasLaw_of_all_projections mu nu X hX
  intro E
  rw [(htarget E).map_eq]
  exact hsource E

end
end PaperC.V282.SpatialMarkedLawExt
