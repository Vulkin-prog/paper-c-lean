import PaperCV282.GeneralPoissonMarking
import PaperCV282.SpatialMarkedLawExt
import PaperCV282.SpatialMarkedTargetProjection

/-! # A global Poisson sample with iid spatial marks has the full spatial target law -/
namespace PaperC.V282.SpatialMarkedPoissonIdentification

open MeasureTheory ProbabilityTheory SpatialMarkedTypes ExactMarkedModel
open ExactMarkedFieldTransfer SpatialMarkedTarget SpatialMarkedTargetProjection
open GeneralPoissonMarking PoissonFieldMeasure ConditionalStartProbability
open scoped BigOperators NNReal ENNReal

noncomputable section

instance instMeasurableFiniteCategory (N E : ℕ) :
    MeasurableSpace (Option (SignedMarkIndex N E)) := ⊤

instance instMeasurableSingletonFiniteCategory (N E : ℕ) :
    MeasurableSingletonClass (Option (SignedMarkIndex N E)) := by infer_instance

def finiteCategory (N E : ℕ) (j : SpatialMarkedIndex N) : Option (SignedMarkIndex N E) :=
  if h : j.2.1≤E then some (dyadicSiteEquiv N j.1,(⟨j.2.1,by omega⟩,j.2.2)) else none

theorem finiteCategory_eq_some_iff (N E : ℕ) (j : SpatialMarkedIndex N)
    (i : SignedMarkIndex N E) :
    finiteCategory N E j=some i ↔ j=finiteMarkedEmbedding N E i := by
  classical
  by_cases hj : j.2.1≤E
  · rw [finiteCategory,dif_pos hj,Option.some.injEq]
    constructor
    · rintro rfl
      simp [finiteMarkedEmbedding]
    · intro h
      subst j
      apply Prod.ext
      · exact (dyadicSiteEquiv N).apply_symm_apply i.1
      · exact Prod.ext (Fin.ext rfl) rfl
  · rw [finiteCategory,dif_neg hj]
    constructor
    · simp
    · intro h
      subst j
      exact (hj (Nat.le_of_lt_succ i.2.1.isLt)).elim

/-- The complete spatial configuration of a finite Poisson sample, before truncation. -/
def sampledConfiguration {X : Type*} (N : ℕ) (mark : X → SpatialMarkedIndex N)
    (sample : ℕ × (ℕ → X)) : SpatialMarkedConfig N :=
  ∑ i ∈ Finset.range sample.1, Finsupp.single (mark (sample.2 i)) 1

theorem measurable_sampledConfiguration {X : Type*} [MeasurableSpace X] (N : ℕ)
    (mark : X → SpatialMarkedIndex N) (hm : Measurable mark) :
    Measurable (sampledConfiguration N mark) := by
  classical
  apply measurable_from_prod_countable_right
  intro n
  have heq : (fun marks : ℕ → X => sampledConfiguration N mark (n,marks)) =
      (fun v : Fin n → SpatialMarkedIndex N => ∑ i : Fin n, Finsupp.single (v i) (1 : ℕ)) ∘
        (fun marks : ℕ → X => fun i : Fin n => mark (marks i.val)) := by
    funext marks
    exact (Fin.sum_univ_eq_sum_range (fun i => Finsupp.single (mark (marks i)) (1 : ℕ)) n).symm
  rw [heq]
  exact (measurable_of_countable _).comp
    (measurable_pi_lambda _ (fun i => hm.comp (measurable_pi_apply i.val)))

theorem project_sampledConfiguration {X : Type*} (N E : ℕ)
    (mark : X → SpatialMarkedIndex N) (sample : ℕ × (ℕ → X)) :
    projectConfiguration N E (sampledConfiguration N mark sample)=
      categoryCounts (finiteCategory N E ∘ mark) sample := by
  classical
  funext i
  simp only [projectConfiguration,sampledConfiguration,Finsupp.finsetSum_apply,
    categoryCounts,Function.comp_apply]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finsupp.single_apply,finiteCategory_eq_some_iff]

theorem hasLaw_project_sampledConfiguration {X : Type*} [MeasurableSpace X]
    (N E : ℕ) (rate : ℝ≥0) (mu : Measure X) [IsProbabilityMeasure mu]
    (mark : X → SpatialMarkedIndex N) (hm : Measurable mark) :
    HasLaw (fun sample => projectConfiguration N E (sampledConfiguration N mark sample))
      (fieldMeasure (categoryRates rate mu (finiteCategory N E ∘ mark)))
      (markSampleMeasure rate mu) := by
  simpa only [project_sampledConfiguration] using hasLaw_categoryCounts rate mu
    (finiteCategory N E ∘ mark) ((measurable_of_countable _).comp hm)

/-- Elementary atom rates determine the complete target, with no joint-law premise. -/
theorem hasLaw_sampledConfiguration_of_atom_rates {X : Type*} [MeasurableSpace X]
    (N L : ℕ) (rate : ℝ≥0) (mu : Measure X) [IsProbabilityMeasure mu]
    (mark : X → SpatialMarkedIndex N) (hm : Measurable mark)
    (hrates : ∀ j : SpatialMarkedIndex N,
      rate * (mu {x | mark x=j}).toNNReal=signedMarkRate L j.2.1) :
    HasLaw (sampledConfiguration N mark) (spatialTargetMeasure N L) (markSampleMeasure rate mu) := by
  apply SpatialMarkedLawExt.hasLaw_of_matching_projection_laws
    (markSampleMeasure rate mu) (spatialTargetMeasure N L) (sampledConfiguration N mark)
    (measurable_sampledConfiguration N mark hm)
    (fun E => fieldMeasure (allSignedRates N L E (dyadicBlock N)))
  · intro E
    have hr : categoryRates rate mu (finiteCategory N E ∘ mark)=
        allSignedRates N L E (dyadicBlock N) := by
      funext i
      rw [allSignedRates,if_pos i.1.property]
      have hset : {x | (finiteCategory N E ∘ mark) x=some i}=
          {x | mark x=finiteMarkedEmbedding N E i} := by
        ext x
        exact finiteCategory_eq_some_iff N E (mark x) i
      rw [categoryRates,hset]
      exact hrates (finiteMarkedEmbedding N E i)
    rw [← hr]
    exact hasLaw_project_sampledConfiguration N E rate mu mark hm
  · exact hasLaw_projectConfiguration N L

end
end PaperC.V282.SpatialMarkedPoissonIdentification
