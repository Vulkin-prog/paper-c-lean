import PaperCV282.SpatialMarkedTargetTail
import PaperCV282.PoissonFieldMeasure

/-! # Exact aggregation of the complete spatial Poisson configuration -/
namespace PaperC.V282.SpatialMarkedTargetAggregation

open MeasureTheory ProbabilityTheory SpatialMarkedTypes SpatialMarkedTarget SpatialMarkedTargetTail
open GeometricMarkedConfiguration GeometricConfigurationCounts AllStartSoftPoisson PoissonFieldMeasure
open scoped BigOperators NNReal ENNReal

noncomputable section

def spatialRowEmbedding (N : ℕ) (i : Fin N × F₂) : ℕ ↪ SpatialMarkedIndex N where
  toFun e := (i.1,(e,i.2))
  inj' := by
    intro e f h
    exact congrArg (fun j : SpatialMarkedIndex N => j.2.1) h

theorem flattenRows_eq_sum (N : ℕ) (rows : (Fin N × F₂) → (ℕ →₀ ℕ)) :
    flattenRows N rows = ∑ i : Fin N × F₂, (rows i).embDomain (spatialRowEmbedding N i) := by
  classical
  ext j
  rw [flattenRows_apply,Finsupp.finsetSum_apply]
  symm
  rw [Finset.sum_eq_single (j.1,j.2.2)]
  · exact Finsupp.embDomain_apply_self _ _ _
  · intro i hi hne
    apply Finsupp.embDomain_notin_range
    rintro ⟨e,he⟩
    apply hne
    exact Prod.ext (congrArg (fun k : SpatialMarkedIndex N => k.1) he)
      (congrArg (fun k : SpatialMarkedIndex N => k.2.2) he)
  · intro hn
    exact (hn (Finset.mem_univ _)).elim

theorem sum_flattenRows {A : Type*} [AddCommMonoid A] (N : ℕ)
    (rows : (Fin N × F₂) → (ℕ →₀ ℕ)) (f : SpatialMarkedIndex N → ℕ → A)
    (hfzero : ∀ j, f j 0=0) (hfadd : ∀ j n m, f j (n+m)=f j n+f j m) :
    (flattenRows N rows).sum f = ∑ i : Fin N × F₂, (rows i).sum (fun e n => f (i.1,e,i.2) n) := by
  rw [flattenRows_eq_sum,← Finsupp.sum_finsetSum_index hfzero hfadd]
  apply Finset.sum_congr rfl
  intro i hi
  exact Finsupp.sum_embDomain

def totalSpatialCount (N : ℕ) (config : SpatialMarkedConfig N) : ℕ := config.sum (fun _ n => n)

def totalSpatialWeight (N : ℕ) (config : SpatialMarkedConfig N) : ℕ :=
  config.sum (fun j n => (j.2.1+1)*n)

theorem totalSpatialCount_flattenRows (N : ℕ) (rows : (Fin N × F₂) → (ℕ →₀ ℕ)) :
    totalSpatialCount N (flattenRows N rows) = ∑ i, configurationSize (rows i) :=
  sum_flattenRows N rows _ (fun _ => rfl) (fun _ _ _ => rfl)

theorem totalSpatialWeight_flattenRows (N : ℕ) (rows : (Fin N × F₂) → (ℕ →₀ ℕ)) :
    totalSpatialWeight N (flattenRows N rows) = ∑ i, configurationWeight (rows i) :=
  sum_flattenRows N rows _ (fun _ => Nat.mul_zero _) (fun _ _ _ => Nat.mul_add _ _ _)

theorem hasLaw_rowCounts (N L : ℕ) :
    HasLaw (fun rows : (Fin N × F₂) → (ℕ →₀ ℕ) => fun i => configurationSize (rows i))
      (fieldMeasure (fun _ : Fin N × F₂ => signedSiteRate L)) (spatialRowsMeasure N L) := by
  refine ⟨(measurable_of_countable _).aemeasurable,?_⟩
  rw [spatialRowsMeasure,Measure.pi_map_pi
    (f := fun _ : Fin N × F₂ => configurationSize)
    (fun _ => (measurable_of_countable _).aemeasurable)]
  unfold fieldMeasure
  congr 1
  funext i
  exact (hasLaw_configurationSize (signedSiteRate L)).map_eq

/-- Counting every spatial point, without any mark cutoff, has exactly the moving Poisson law. -/
theorem hasLaw_totalSpatialCount (N L : ℕ) :
    HasLaw (totalSpatialCount N) (poissonMeasure (fullRate N L)) (spatialTargetMeasure N L) := by
  have hr : (∑ _ : Fin N × F₂, signedSiteRate L)=fullRate N L := by
    apply NNReal.coe_injective
    simpa only [NNReal.coe_sum] using sum_signedSiteRate N L
  have h := (hasLaw_coordinate_sum (fun _ : Fin N × F₂ => signedSiteRate L) Finset.univ).fun_comp
    (hasLaw_rowCounts N L)
  simp only [hr] at h
  refine ⟨(measurable_of_countable _).aemeasurable,?_⟩
  rw [spatialTargetMeasure,Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  have heq : totalSpatialCount N ∘ flattenRows N =
      fun rows : (Fin N × F₂) → (ℕ →₀ ℕ) => ∑ i, configurationSize (rows i) :=
    funext (totalSpatialCount_flattenRows N)
  rw [heq]
  exact h.map_eq

end
end PaperC.V282.SpatialMarkedTargetAggregation
