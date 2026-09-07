import PaperCV282.AggregateCoordinateIdentities
import PaperCV282.SignedAggregateTruncation
import PaperCV282.GeometricMarkedConfiguration
import PaperCV282.ExactMarkedSignProjection

/-! # Identifying the complete unsigned aggregate target with the genuine geometric Poisson configuration -/
namespace PaperC.V282.UnsignedAggregateTarget

open MeasureTheory ProbabilityTheory AggregateCoordinateIdentities SignedAggregateTruncation
open SignedAggregateConfiguration SignedDirectionalFactors ExactMarkedModel ExactMarkedSignProjection
open PoissonFieldAggregation PoissonFieldMeasure GeometricMarkedConfiguration GeometricClusterTruncation
open SpatialMarkedTypes SpatialMarkedTarget MovingMarkedSource AllStartSoftPoisson
open scoped BigOperators NNReal

noncomputable section

theorem sum_signedAggregateRates_eq_geometric (rate : ℝ≥0) (E : ℕ) (e : Fin (E+1)) :
    (∑ s : F₂, signedAggregateRates rate E (e,s))=geometricCoordinateRates rate E e := by
  apply NNReal.coe_injective
  simp only [NNReal.coe_sum,signedAggregateRates,NNReal.coe_mul,← Finset.mul_sum]
  rw [sum_signedMarkRate]
  simp [exactMarkRate_coe,geometricCoordinateRates,div_eq_mul_inv]

theorem hasLaw_forgetFiniteSigns (rate : ℝ≥0) (E : ℕ) :
    HasLaw (forgetFiniteSigns E) (fieldMeasure (geometricCoordinateRates rate E))
      (fieldMeasure (signedAggregateRates rate E)) := by
  have hr := hasLaw_reindexedPoisson (signedAggregateRates rate E) (Equiv.prodComm (Fin (E+1)) F₂)
  have hc := hasLaw_column_sums (fun i : F₂ × Fin (E+1) => signedAggregateRates rate E (i.2,i.1))
    (fun _ => Finset.univ)
  have h := hc.fun_comp hr
  have he : (fun e : Fin (E+1) => ∑ s : F₂, signedAggregateRates rate E (e,s))=
      geometricCoordinateRates rate E := funext (sum_signedAggregateRates_eq_geometric rate E)
  rw [he] at h
  exact h

theorem hasLaw_unsigned_projection (N L E : ℕ) :
    HasLaw (unsignedProjection E ∘ aggregateExcess N)
      (fieldMeasure (geometricCoordinateRates (fullRate N L) E)) (spatialTargetMeasure N L) := by
  have h := (hasLaw_forgetFiniteSigns (fullRate N L) E).fun_comp (hasLaw_project_signedAggregate N L E)
  have he : unsignedProjection E ∘ aggregateExcess N=
      fun config => forgetFiniteSigns E (finiteSignedAggregate N E
        (SpatialMarkedTypes.projectConfiguration N E config)) := funext (unsignedProjection_aggregate N E)
  rw [he]
  exact h

/-- Equality of every finite projection identifies the whole countable configuration law. -/
theorem configurationMeasure_ext (mu nu : Measure (ℕ →₀ ℕ))
    [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (h : ∀ E : ℕ, mu.map (unsignedProjection E)=nu.map (unsignedProjection E)) : mu=nu := by
  apply Measure.ext_of_singleton
  intro target
  let fiber : ℕ → Set (ℕ →₀ ℕ) := fun E => {config | ∀ e≤E, config e=target e}
  have hanti : Antitone fiber := by
    intro E F hEF config hc e he
    exact hc e (he.trans hEF)
  have hinter : {target}=⋂ E : ℕ, fiber E := by
    ext config
    simp only [Set.mem_singleton_iff,Set.mem_iInter,fiber,Set.mem_setOf_eq]
    constructor
    · rintro rfl E e he;rfl
    · intro he
      ext e
      exact he e e le_rfl
  rw [hinter,hanti.measure_iInter (fun E => (Set.to_countable (fiber E)).measurableSet.nullMeasurableSet)
      ⟨0,measure_ne_top _ _⟩,
    hanti.measure_iInter (fun E => (Set.to_countable (fiber E)).measurableSet.nullMeasurableSet)
      ⟨0,measure_ne_top _ _⟩]
  congr 1
  funext E
  have he := congrArg (fun m : Measure (Fin (E+1) → ℕ) => m {unsignedProjection E target}) (h E)
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
    Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)] at he
  have hset : unsignedProjection E ⁻¹' {unsignedProjection E target}=fiber E := by
    ext config
    simp only [Set.mem_preimage,Set.mem_singleton_iff,fiber,Set.mem_setOf_eq]
    constructor
    · intro he e heE
      exact congrFun he ⟨e,by omega⟩
    · intro he
      funext e
      exact he e.val (Nat.le_of_lt_succ e.isLt)
  rw [hset] at he
  exact he

/-- The full target, with every excess retained, is the Poisson configuration at the full rate. -/
theorem hasLaw_aggregateExcess (N L : ℕ) :
    HasLaw (aggregateExcess N) (configurationMeasure (fullRate N L)) (spatialTargetMeasure N L) := by
  refine ⟨(measurable_of_countable _).aemeasurable,?_⟩
  apply configurationMeasure_ext
  intro E
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    (hasLaw_unsigned_projection N L E).map_eq]
  exact (hasLaw_finite_configuration (fullRate N L) E).map_eq.symm

end
end PaperC.V282.UnsignedAggregateTarget
