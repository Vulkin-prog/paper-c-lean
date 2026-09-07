import PaperCV282.D4ClosurePointMeasure
import PaperCV282.PoissonResolvedTarget

/-! # The independent Poisson rows and uniform positions of the two-sided target -/
namespace PaperC.V282.D4ClosurePointLaws

open MeasureTheory ProbabilityTheory
open D4ClosurePointMeasure D4ClosureIntegerLevels D4ClosureHalfLines
open UniformSpatialGrid GeneralPoissonMarking PoissonResolvedTarget
open scoped BigOperators NNReal ENNReal

noncomputable section

theorem hasLaw_spatialLevelSample (theta : ℝ) (r : ℤ) :
    HasLaw (fun sample : IntegerSpatialSample => sample r)
      (markSampleMeasure (integerLevelRate theta r) unitIntervalUniformMeasure)
      (integerSpatialSampleMeasure theta) :=
  (measurePreserving_eval_infinitePi
    (fun r => markSampleMeasure (integerLevelRate theta r) unitIntervalUniformMeasure) r).hasLaw

theorem independent_spatialLevelSamples (theta : ℝ) :
    iIndepFun (fun r (sample : IntegerSpatialSample) => sample r)
      (integerSpatialSampleMeasure theta) :=
  iIndepFun_infinitePi (fun _ => measurable_id)

theorem hasLaw_integerSpatialCounts (theta : ℝ) :
    HasLaw (fun sample : IntegerSpatialSample => fun r => (sample r).1)
      (integerCountMeasure theta) (integerSpatialSampleMeasure theta) := by
  refine ⟨(measurable_pi_lambda _ (fun r => measurable_fst.comp
    (measurable_pi_apply r))).aemeasurable, ?_⟩
  rw [integerSpatialSampleMeasure, Measure.infinitePi_map_pi _ (fun _ => measurable_fst)]
  simp only [markSampleMeasure, Measure.map_fst_prod, measure_univ, one_smul]
  rfl

/-- Upper exact-level populations are simultaneously finite almost surely,
also in the spatially marked construction. -/
theorem ae_spatial_upper_tails_finite (theta : ℝ) :
    ∀ᵐ sample ∂integerSpatialSampleMeasure theta,
      ∀ m : ℤ, (Function.support (fun e : ℕ => (sample (m+e)).1)).Finite := by
  have h := ae_all_upper_tails_finite theta
  have hlaw := hasLaw_integerSpatialCounts theta
  rw [← hlaw.map_eq] at h
  exact (ae_map_iff hlaw.aemeasurable
    (show MeasurableSet {counts : ℤ → ℕ | ∀ m : ℤ,
        (Function.support (halfLineCounts m counts)).Finite} from by
      have hset : {counts : ℤ → ℕ | ∀ m : ℤ,
          (Function.support (halfLineCounts m counts)).Finite} =
          ⋂ m : ℤ, (halfLineCounts m) ⁻¹' Set.range (fun c : ℕ →₀ ℕ => (c : ℕ → ℕ)) := by
        ext counts
        simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_range]
        apply forall_congr'
        intro m
        constructor
        · intro hc
          exact ⟨Finsupp.ofSupportFinite _ hc, rfl⟩
        · rintro ⟨c, hc⟩
          rw [← hc]
          exact c.hasFiniteSupport
      rw [hset]
      exact MeasurableSet.iInter fun m => (measurable_halfLineCounts m)
        measurableEmbedding_configuration.measurableSet_range)).1 h

/-- Resolving an exact-level count fixes n and leaves its uniform positions iid. -/
theorem conditional_level_positions (theta : ℝ) (r : ℤ) (n : ℕ)
    (hn : (poissonMeasure (integerLevelRate theta r)) {n} ≠ 0) :
    (cond (integerSpatialSampleMeasure theta) {sample | (sample r).1 = n}).map
      (fun sample : IntegerSpatialSample => sample r) =
      (Measure.dirac n).prod (markSequenceMeasure unitIntervalUniformMeasure) := by
  change (cond (integerSpatialSampleMeasure theta)
    ((fun sample : IntegerSpatialSample => sample r) ⁻¹' (Prod.fst ⁻¹' {n}))).map
      (fun sample : IntegerSpatialSample => sample r) = _
  rw [SharpConditioningDiscrete.map_cond_eq _ (measurable_pi_apply r) _
    (measurable_fst (measurableSet_singleton n)), (hasLaw_spatialLevelSample theta r).map_eq,
    markSampleMeasure, cond_prod_first_eq _ _ n hn]

end
end PaperC.V282.D4ClosurePointLaws
