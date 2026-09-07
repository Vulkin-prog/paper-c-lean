import PaperCV282.AffineCrossoverRecordMass

/-! # Sparse independent products with the actual conditioned border mass

The sparse-event mass needs only the probability of the border indicator.
Identifying its labelled conditional law additionally uses the genuine
capped clock law under the border condition.
-/
namespace PaperC.V282.AffineCrossoverSparseTarget

open MeasureTheory ProbabilityTheory InfiniteRademacher MicroscopicBorderEvents
open BulkMarkedTypes BulkMarkedTarget CrossoverBulkAtoms CrossoverBulkTestMass CrossoverBulkOnePoint
open CrossoverMarkedModel CrossoverMarkedTarget CrossoverMarkedCandidate CrossoverClockRecordMass
open CrossoverSparseTarget CrossoverSparseWeights AffineCrossoverRecordMass
open CrossoverPrimeClockStable SharpConditioning ConditionedCountableLaw GeometricClusterTarget
open scoped NNReal

noncomputable section

variable (mu : Measure InfiniteSample) [IsProbabilityMeasure mu]

/-- The unlabelled sparse mass is exact without any future neutrality or clock-law assumption. -/
theorem sparse_mass (sites : Finset ℕ) (L K : ℕ) (alpha : ℝ≥0)
    (halpha : mu.real (borderEvent L) = (alpha : ℝ)) :
    (AffineCrossoverModel.productJoint mu sites L K).real (sparseEvent sites) =
      Real.exp (-(totalRate sites L : ℝ))*
        ((alpha : ℝ)+(1-(alpha : ℝ))*(totalRate sites L : ℝ)) := by
  have he : sparseEvent sites =
      ({v : Bool×ℕ | v.1=true} ×ˢ {c | totalSize sites c=0}) ∪
      ({v : Bool×ℕ | v.1=false} ×ˢ {c | totalSize sites c=1}) := rfl
  have hd : Disjoint
      ({v : Bool×ℕ | v.1=true} ×ˢ {c : SpatialMarkedConfig sites | totalSize sites c=0})
      ({v : Bool×ℕ | v.1=false} ×ˢ {c : SpatialMarkedConfig sites | totalSize sites c=1}) := by
    apply Set.disjoint_left.mpr
    intro z hz ht
    have h := hz.1.symm.trans ht.1
    contradiction
  rw [he,measureReal_union hd (Set.to_countable _).measurableSet]
  change ((AffineCrossoverModel.recordMeasure mu L K).prod (spatialTargetMeasure sites L)).real _ +
    ((AffineCrossoverModel.recordMeasure mu L K).prod (spatialTargetMeasure sites L)).real _ = _
  rw [measureReal_prod_prod,measureReal_prod_prod,
    AffineCrossoverRecordMass.record_true_mass,AffineCrossoverRecordMass.record_false_mass,halpha,
    total_size_probability,total_size_probability]
  simp only [pow_zero,pow_one,Nat.factorial_zero,Nat.factorial_one,Nat.cast_one,div_one,mul_one]
  ring

theorem sparse_mass_pos (sites : Finset ℕ) (L K : ℕ) (alpha : ℝ≥0)
    (halpha : mu.real (borderEvent L) = (alpha : ℝ)) (hpos : 0 < alpha) :
    0 < (AffineCrossoverModel.productJoint mu sites L K).real (sparseEvent sites) := by
  rw [sparse_mass mu sites L K alpha halpha]
  have ha : (0 : ℝ) < alpha := by exact_mod_cast hpos
  have haOne : (alpha : ℝ) ≤ 1 := by rw [← halpha]; exact measureReal_le_one
  positivity

theorem sparse_test_mass (sites : Finset ℕ) (hs : sites.Nonempty) (L K : ℕ) (alpha : ℝ≥0)
    (halpha : mu.real (borderEvent L) = (alpha : ℝ)) (hpos : 0 < alpha)
    (hclock : (cond mu (borderEvent L)).map (actualClockRecord L K) =
      (geometricMeasure halfSuccess).map (fun j => (true,min j K))) (S : Set Record) :
    (AffineCrossoverModel.productJoint mu sites L K).real (sparseEvent sites ∩ (candidate sites ⁻¹' S)) =
      Real.exp (-(totalRate sites L : ℝ))*
        ((alpha : ℝ)*(cappedBorderLaw K).real S+
          (1-(alpha : ℝ))*(totalRate sites L : ℝ)*(bulkLaw sites hs).real S) := by
  rw [sparse_test_decomposition]
  have hd : Disjoint
      ({v : Bool×ℕ | v.1=true ∧ borderLabel v.2∈S} ×ˢ {c : SpatialMarkedConfig sites | totalSize sites c=0})
      ({v : Bool×ℕ | v.1=false} ×ˢ {c : SpatialMarkedConfig sites | totalSize sites c=1 ∧ bulkCandidate sites c∈S}) := by
    apply Set.disjoint_left.mpr
    intro z hz ht
    have h := hz.1.1.symm.trans ht.1
    contradiction
  rw [measureReal_union hd (Set.to_countable _).measurableSet]
  change ((AffineCrossoverModel.recordMeasure mu L K).prod (spatialTargetMeasure sites L)).real _ +
    ((AffineCrossoverModel.recordMeasure mu L K).prod (spatialTargetMeasure sites L)).real _ = _
  rw [measureReal_prod_prod,measureReal_prod_prod,
    AffineCrossoverRecordMass.true_test_mass mu L K alpha halpha hpos hclock,
    AffineCrossoverRecordMass.record_false_mass,halpha,total_size_probability,one_point_test_mass sites hs]
  simp only [pow_zero,Nat.factorial_zero,Nat.cast_one,div_one,mul_one]
  ring

theorem conditional_candidate_test (sites : Finset ℕ) (hs : sites.Nonempty) (L K : ℕ) (alpha : ℝ≥0)
    (halpha : mu.real (borderEvent L) = (alpha : ℝ)) (hpos : 0 < alpha)
    (hclock : (cond mu (borderEvent L)).map (actualClockRecord L K) =
      (geometricMeasure halfSuccess).map (fun j => (true,min j K))) (S : Set Record) :
    ((cond (AffineCrossoverModel.productJoint mu sites L K) (sparseEvent sites)).map (candidate sites)).real S =
      ((alpha : ℝ)*(cappedBorderLaw K).real S+
        (1-(alpha : ℝ))*(totalRate sites L : ℝ)*(bulkLaw sites hs).real S)/
        ((alpha : ℝ)+(1-(alpha : ℝ))*(totalRate sites L : ℝ)) := by
  rw [map_measureReal_apply (measurable_of_countable _) (Set.to_countable _).measurableSet,
    cond_real_apply _ _ (Set.to_countable _).measurableSet,
    sparse_test_mass mu sites hs L K alpha halpha hpos hclock,sparse_mass mu sites L K alpha halpha]
  exact mul_div_mul_left _ _ (Real.exp_ne_zero _)

/-- Replacing the sparse weights is uniform even when one of the two sources has vanishing weight. -/
theorem conditional_candidate_tv_le (sites : Finset ℕ) (hs : sites.Nonempty) (L K : ℕ) (alpha : ℝ≥0)
    (halpha : mu.real (borderEvent L) = (alpha : ℝ)) (hpos : 0 < alpha)
    (hclock : (cond mu (borderEvent L)).map (actualClockRecord L K) =
      (geometricMeasure halfSuccess).map (fun j => (true,min j K))) :
    measureTotalVariation
      ((cond (AffineCrossoverModel.productJoint mu sites L K) (sparseEvent sites)).map (candidate sites))
      ((AffineCrossoverTarget.mixedLaw sites hs L alpha).map (capBorder K)) ≤ (totalRate sites L : ℝ) := by
  letI instProbabilityConditionalSparse : IsProbabilityMeasure
      (cond (AffineCrossoverModel.productJoint mu sites L K) (sparseEvent sites)) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ (sparse_mass_pos mu sites L K alpha halpha hpos))
  letI instProbabilityCandidate : IsProbabilityMeasure
      ((cond (AffineCrossoverModel.productJoint mu sites L K) (sparseEvent sites)).map (candidate sites)) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  letI instProbabilityCappedMixed : IsProbabilityMeasure
      ((AffineCrossoverTarget.mixedLaw sites hs L alpha).map (capBorder K)) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  apply (measureTotalVariation_le_iff _ _ _).mpr
  intro S _
  rw [conditional_candidate_test mu sites hs L K alpha halpha hpos hclock,
    AffineCrossoverTarget.capped_mixedLaw_real]
  have haOne : (alpha : ℝ) ≤ 1 := by rw [← halpha]; exact measureReal_le_one
  have h := two_weight_error_le (by exact_mod_cast hpos) haOne
    (show 0 ≤ (totalRate sites L : ℝ) by positivity)
    (show 0 ≤ (cappedBorderLaw K).real S from measureReal_nonneg)
    (show (cappedBorderLaw K).real S ≤ 1 from measureReal_le_one)
    (show 0 ≤ (bulkLaw sites hs).real S from measureReal_nonneg)
    (show (bulkLaw sites hs).real S ≤ 1 from measureReal_le_one)
  convert h using 1
  simp only [AffineCrossoverTarget.borderWeight,AffineCrossoverTarget.bulkWeight,
    NNReal.coe_div,NNReal.coe_add]
  congr 1
  ring

end
end PaperC.V282.AffineCrossoverSparseTarget
