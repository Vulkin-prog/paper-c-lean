import PaperCV282.GeneralPoissonMarking
import PaperCPrel8.BulkCloudLawExt
import PaperCV282.BulkMarkedTargetProjection
import PaperCV282.CrossoverBulkOnePoint

/-! # A global Poisson sample with iid spatial marks has the full spatial target law -/
namespace PaperC.Prel8.BulkCloudIdentification

open MeasureTheory ProbabilityTheory V282.BulkMarkedTypes V282.ExactMarkedModel
open V282.BulkMarkedTransfer V282.BulkMarkedTarget V282.BulkMarkedTargetProjection
open V282.GeneralPoissonMarking V282.PoissonFieldMeasure ConditionalStartProbability
open V282.BulkSupportGraph V282.CrossoverBulkOnePoint V282.FiniteStartMaskAverages
open scoped BigOperators NNReal ENNReal

noncomputable section

instance instMeasurableFiniteCategory (N : Finset ℕ) (E : ℕ) :
    MeasurableSpace (Option (LabelledIndex N (Fin (E+1) × F₂))) := ⊤

instance instMeasurableSingletonFiniteCategory (N : Finset ℕ) (E : ℕ) :
    MeasurableSingletonClass (Option (LabelledIndex N (Fin (E+1) × F₂))) := by infer_instance

def finiteCategory (N : Finset ℕ) (E : ℕ) (j : SpatialMarkedIndex N) : Option (LabelledIndex N (Fin (E+1) × F₂)) :=
  if h : j.2.1≤E then some (j.1,(⟨j.2.1,by omega⟩,j.2.2)) else none

theorem finiteCategory_eq_some_iff (N : Finset ℕ) (E : ℕ) (j : SpatialMarkedIndex N)
    (i : LabelledIndex N (Fin (E+1) × F₂)) :
    finiteCategory N E j=some i ↔ j=finiteMarkedEmbedding N E i := by
  classical
  by_cases hj : j.2.1≤E
  · rw [finiteCategory,dite_eq_left hj,Option.some.injEq]
    constructor
    · rintro rfl
      rfl
    · intro h
      subst j
      exact Prod.ext rfl (Prod.ext (Fin.ext rfl) rfl)
  · rw [finiteCategory,dite_eq_right hj]
    constructor
    · simp
    · intro h
      subst j
      exact (hj (Nat.le_of_lt_succ i.2.1.isLt)).elim

/-- The complete spatial configuration of a finite Poisson sample, before truncation. -/
def sampledConfiguration {X : Type*} (N : Finset ℕ) (mark : X → SpatialMarkedIndex N)
    (sample : ℕ × (ℕ → X)) : SpatialMarkedConfig N :=
  ∑ i ∈ Finset.range sample.1, Finsupp.single (mark (sample.2 i)) 1

theorem measurable_sampledConfiguration {X : Type*} [MeasurableSpace X] (N : Finset ℕ)
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
    (Measurable.of_eval (fun i => hm.comp (measurable_pi_apply i.val)))

theorem project_sampledConfiguration {X : Type*} (N : Finset ℕ) (E : ℕ)
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
    (N : Finset ℕ) (E : ℕ) (rate : ℝ≥0) (mu : Measure X) [IsProbabilityMeasure mu]
    (mark : X → SpatialMarkedIndex N) (hm : Measurable mark) :
    HasLaw (fun sample => projectConfiguration N E (sampledConfiguration N mark sample))
      (fieldMeasure (categoryRates rate mu (finiteCategory N E ∘ mark)))
      (markSampleMeasure rate mu) := by
  simpa only [project_sampledConfiguration] using hasLaw_categoryCounts rate mu
    (finiteCategory N E ∘ mark) ((measurable_of_countable _).comp hm)

/-- Elementary atom rates determine the complete target, with no joint-law premise. -/
theorem hasLaw_sampledConfiguration_of_atom_rates {X : Type*} [MeasurableSpace X]
    (N : Finset ℕ) (L : ℕ) (rate : ℝ≥0) (mu : Measure X) [IsProbabilityMeasure mu]
    (mark : X → SpatialMarkedIndex N) (hm : Measurable mark)
    (hrates : ∀ j : SpatialMarkedIndex N,
      rate * (mu {x | mark x=j}).toNNReal=signedMarkRate L j.2.1) :
    HasLaw (sampledConfiguration N mark) (spatialTargetMeasure N L) (markSampleMeasure rate mu) := by
  apply BulkCloudLawExt.hasLaw_of_matching_projection_laws
    (markSampleMeasure rate mu) (spatialTargetMeasure N L) (sampledConfiguration N mark)
    (measurable_sampledConfiguration N mark hm)
    (fun E => fieldMeasure (allSignedRates N L E N))
  · intro E
    have hr : categoryRates rate mu (finiteCategory N E ∘ mark)=
        allSignedRates N L E N := by
      funext i
      rw [allSignedRates,ite_eq_left i.1.property]
      have hset : {x | (finiteCategory N E ∘ mark) x=some i}=
          {x | mark x=finiteMarkedEmbedding N E i} := by
        ext x
        exact finiteCategory_eq_some_iff N E (mark x) i
      rw [categoryRates,hset]
      exact hrates (finiteMarkedEmbedding N E i)
    rw [← hr]
    exact hasLaw_project_sampledConfiguration N E rate mu mark hm
  · exact hasLaw_projectConfiguration N L

/-- The literal independent uniform position, geometric excess and fair sign
have exactly the rates of the full target on any nonempty finite site set. -/
theorem label_atom_rates (sites : Finset ℕ) (hs : sites.Nonempty) (L : ℕ)
    (j : SpatialMarkedIndex sites) :
    maskRate L sites * ((labelMeasure sites hs) {j}).toNNReal = signedMarkRate L j.2.1 := by
  apply NNReal.coe_injective
  rw [NNReal.coe_mul]
  change (maskRate L sites : ℝ) * (labelMeasure sites hs).real {j} = _
  rw [labelMeasure_real_singleton]
  change ((sites.card : ℝ)/2^L)*((1/(sites.card : ℝ))*(1/(2 : ℝ)^(j.2.1+1))*(1/2)) =
    1/(2 : ℝ)^(L+j.2.1+2)
  have hc : (sites.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hs).ne'
  rw [show L+j.2.1+2=L+(j.2.1+1)+1 by omega,pow_add,pow_succ]
  field_simp
  ring

/-- The Poisson sample, with all signs and unbounded excesses, is the actual
complete target. No joint-law or finite-projection premise remains. -/
theorem hasLaw_label_configuration (sites : Finset ℕ) (hs : sites.Nonempty) (L : ℕ) :
    HasLaw (sampledConfiguration sites id) (spatialTargetMeasure sites L)
      (markSampleMeasure (maskRate L sites) (labelMeasure sites hs)) := by
  apply hasLaw_sampledConfiguration_of_atom_rates sites L _ _ id measurable_id
  intro j
  simpa using label_atom_rates sites hs L j

end
end PaperC.Prel8.BulkCloudIdentification
