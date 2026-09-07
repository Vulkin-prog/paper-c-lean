import PaperCV282.AffineCrossoverModel

/-! # Actual source geometry under absolutely continuous conditioning -/
namespace PaperC.V282.AffineCrossoverSourceCoupling

open MeasureTheory ProbabilityTheory Set Filter InfiniteRademacher SharpConditioning ConditionedCountableLaw
open CrossoverSourceGeometry CrossoverMarkedModel CrossoverMarkedCandidate CrossoverBulkAtoms
open CrossoverPrimeClockStable BulkMarkedTypes BulkMarkedSource BulkMarkedGeometry
open RarePrefixGeometry RarePrefixEvents MicroscopicNonvacancy CrossoverSourceCoupling

noncomputable section

/-- Conditioning is on any actual measurable source event with at most one bulk point.
In particular the root's sparse event satisfies this geometric condition. -/
theorem conditional_capGamma_candidate_le (mu : Measure InfiniteSample) [IsProbabilityMeasure mu]
    (habs : mu ≪ infiniteRademacherMeasure) {M L K : ℕ} {delta : ℝ}
    (hM : 2≤M) (hL : 1≤L) (hLM : L≤M) (hdelta : 0<delta)
    (E : Set InfiniteSample) (hE : MeasurableSet E) (hEpos : 0 < mu.real E)
    (hsmall : ∀ omega∈E, totalSize (bulkStarts M L delta) (spatialMarkedSource _ L omega)≤1) :
    measureTotalVariation
      ((cond mu E).map (fun omega => capBorder K (gamma M L delta omega)))
      ((cond mu E).map (candidateSource M L K delta)) ≤
      (mu.real (interiorEvent L)+
        mu.real (middleEvent M L delta))/mu.real E := by
  letI instProbabilityConditional : IsProbabilityMeasure (cond mu E) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hEpos)
  have hcabs : cond mu E ≪ infiniteRademacherMeasure := cond_absolutelyContinuous.trans habs
  have hc := hcabs.ae_le (ae_capGamma_eq_candidate (K := K) hM hL hLM hdelta)
  have hcouple : ∀ᵐ omega ∂cond mu E,
      omega∉interiorEvent L ∪ middleEvent M L delta →
      capBorder K (gamma M L delta omega)=candidateSource M L K delta omega := by
    filter_upwards [hc,ae_cond_mem hE] with omega ho he
    intro hn
    exact ho (fun h => hn (Or.inl h)) (fun h => hn (Or.inr h)) (hsmall omega he)
  apply (map_tv_le_of_ae_eq_off _ _ (measurable_capGamma M L K delta)
    (measurable_candidateSource M L K delta) hcouple).trans
  rw [cond_real_apply _ E hE]
  apply div_le_div_of_nonneg_right _ hEpos.le
  exact (measureReal_mono inter_subset_right).trans (measureReal_union_le _ _)

end
end PaperC.V282.AffineCrossoverSourceCoupling
