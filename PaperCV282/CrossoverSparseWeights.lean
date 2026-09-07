import PaperCV282.CrossoverSparseTarget

/-! # Uniform replacement of sparse-product weights by the moving crossover weights -/
namespace PaperC.V282.CrossoverSparseWeights

open MeasureTheory ProbabilityTheory CrossoverSparseTarget CrossoverMarkedCandidate
open CrossoverMarkedModel CrossoverMarkedTarget CrossoverClockRecordMass CrossoverBulkAtoms
open CrossoverBulkOnePoint SharpConditioning ConditionedCountableLaw

noncomputable section

theorem two_weight_error_le {a b u v : ℝ} (ha : 0<a) (haOne : a≤1) (hb : 0≤b)
    (hu : 0≤u) (huOne : u≤1) (hv : 0≤v) (hvOne : v≤1) :
    |(a*u+(1-a)*b*v)/(a+(1-a)*b)-(a*u+b*v)/(a+b)|≤b := by
  have hd : 0<a+(1-a)*b := by positivity
  have hs : 0<a+b := by positivity
  have hfactor : 0≤a^2*b/((a+(1-a)*b)*(a+b)) := by positivity
  have hfactorle : a^2*b/((a+(1-a)*b)*(a+b))≤b := by
    apply (div_le_iff₀ (mul_pos hd hs)).mpr
    have hda : a≤a+(1-a)*b := by nlinarith
    have hsa : a≤a+b := by linarith
    have hm := mul_le_mul hda hsa ha.le hd.le
    nlinarith [mul_le_mul_of_nonneg_right hm hb]
  have he : (a*u+(1-a)*b*v)/(a+(1-a)*b)-(a*u+b*v)/(a+b)=
      (a^2*b/((a+(1-a)*b)*(a+b)))*(u-v) := by
    field_simp
    ring
  rw [he,abs_mul,abs_of_nonneg hfactor]
  have hab : |u-v|≤1 := abs_sub_le_iff.mpr ⟨by linarith,by linarith⟩
  exact (mul_le_mul_of_nonneg_left hab hfactor).trans (by simpa using hfactorle)

theorem bulkLaw_capBorder (sites : Finset ℕ) (hs : sites.Nonempty) (K : ℕ) :
    (bulkLaw sites hs).map (capBorder K)=bulkLaw sites hs := by
  rw [bulkLaw,Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  rfl

theorem capped_mixed_test (sites : Finset ℕ) (hs : sites.Nonempty) (L K : ℕ) (S : Set Record) :
    ((mixedLaw sites hs L).map (capBorder K)).real S=
      ((borderRate L : ℝ)*(cappedBorderLaw K).real S+
        (totalRate sites L : ℝ)*(bulkLaw sites hs).real S)/
      ((borderRate L : ℝ)+(totalRate sites L : ℝ)) := by
  rw [map_measureReal_apply (measurable_of_countable _) (Set.to_countable _).measurableSet,mixedLaw_real]
  have hb : borderLaw.real (capBorder K ⁻¹' S)=(cappedBorderLaw K).real S :=
    (map_measureReal_apply (measurable_of_countable _) (Set.to_countable _).measurableSet).symm
  have hc : (bulkLaw sites hs).real (capBorder K ⁻¹' S)=(bulkLaw sites hs).real S := by
    rw [← map_measureReal_apply (measurable_of_countable _) (Set.to_countable _).measurableSet,
      bulkLaw_capBorder]
  rw [hb,hc]
  simp only [borderWeight,bulkWeight,NNReal.coe_div,NNReal.coe_add]
  ring

/-- The replacement is uniform in the relative size of the two rare sources. -/
theorem conditional_candidate_tv_le (sites : Finset ℕ) (hs : sites.Nonempty) (L K : ℕ) :
    measureTotalVariation
      ((cond (productJoint sites L K) (sparseEvent sites)).map (candidate sites))
      ((mixedLaw sites hs L).map (capBorder K)) ≤ (totalRate sites L : ℝ) := by
  letI instProbabilityConditional : IsProbabilityMeasure (cond (productJoint sites L K) (sparseEvent sites)) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ (sparse_mass_pos sites hs L K))
  letI instProbabilityCandidate : IsProbabilityMeasure
      ((cond (productJoint sites L K) (sparseEvent sites)).map (candidate sites)) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  letI instProbabilityCappedMixed : IsProbabilityMeasure ((mixedLaw sites hs L).map (capBorder K)) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  apply (measureTotalVariation_le_iff _ _ _).mpr
  intro S _
  rw [conditional_candidate_test sites hs,capped_mixed_test]
  exact two_weight_error_le (by exact_mod_cast borderRate_pos L) (borderRate_le_one L) (by positivity)
    measureReal_nonneg measureReal_le_one measureReal_nonneg measureReal_le_one

theorem sparse_mass_relative_error {a b : ℝ} (ha : 0<a) (haOne : a≤1) (hb : 0≤b) :
    |Real.exp (-b)*(a+(1-a)*b)/(a+b)-1|≤2*b := by
  have hs : 0<a+b := by positivity
  have hd : 0≤a+(1-a)*b := by positivity
  have hdp : a+(1-a)*b≤a+b := by nlinarith
  have he : Real.exp (-b)≤1 := Real.exp_le_one_iff.mpr (by linarith)
  have helo : 1-b≤Real.exp (-b) := by linarith [Real.add_one_le_exp (-b)]
  have hupper : Real.exp (-b)*(a+(1-a)*b)≤a+b :=
    (mul_le_of_le_one_left hd he).trans hdp
  have hlower := mul_le_mul_of_nonneg_right helo hd
  have hab : a*b≤b*(a+b) := by nlinarith
  have hbd := mul_le_mul_of_nonneg_left hdp hb
  rw [abs_of_nonpos (by apply sub_nonpos.mpr; exact (div_le_one hs).mpr hupper)]
  rw [neg_sub,one_sub_div hs.ne']
  apply (div_le_iff₀ hs).mpr
  nlinarith

end
end PaperC.V282.CrossoverSparseWeights
