import PaperCV282.AffineCrossoverModel

/-! # Actual border-record masses under an arbitrary source probability

Only the true conditional capped clock is used to identify labelled border
tests. The unlabelled border mass and its complement require no neutrality.
-/
namespace PaperC.V282.AffineCrossoverRecordMass

open MeasureTheory ProbabilityTheory InfiniteRademacher MicroscopicBorderEvents
open CrossoverPrimeClockStable CrossoverPrimeClockLaw CrossoverMarkedModel CrossoverMarkedTarget
open CrossoverMarkedCandidate CrossoverClockRecordMass SharpConditioning GeometricClusterTarget
open ConditionedCountableLaw
open scoped NNReal

noncomputable section

variable (mu : Measure InfiniteSample)

theorem record_true_mass (L K : ℕ) :
    (AffineCrossoverModel.recordMeasure mu L K).real {v | v.1=true} = mu.real (borderEvent L) := by
  rw [AffineCrossoverModel.recordMeasure,
    map_measureReal_apply (measurable_actualClockRecord L K) (Set.to_countable _).measurableSet]
  congr 1
  ext omega
  simp [actualClockRecord]

theorem record_false_mass [IsProbabilityMeasure mu] (L K : ℕ) :
    (AffineCrossoverModel.recordMeasure mu L K).real {v | v.1=false} = 1-mu.real (borderEvent L) := by
  have he : {v : Bool×ℕ | v.1=false} = {v | v.1=true}ᶜ := by
    ext v
    cases v.1 <;> simp
  rw [he, measureReal_compl (Set.to_countable _).measurableSet, probReal_univ, record_true_mass]

/-- With cap zero the clock law is automatic, without any future-prime hypothesis. -/
theorem conditional_actualClockRecord_zero [IsProbabilityMeasure mu] (L : ℕ)
    (hpos : 0 < mu.real (borderEvent L)) :
    (cond mu (borderEvent L)).map (actualClockRecord L 0) =
      (geometricMeasure halfSuccess).map (fun j => (true,min j 0)) := by
  letI instProbabilityConditionalBorder : IsProbabilityMeasure (cond mu (borderEvent L)) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hpos)
  have he : actualClockRecord L 0 =ᵐ[cond mu (borderEvent L)] (fun _ => (true,0)) := by
    filter_upwards [ae_cond_mem (μ := mu) (measurableSet_borderEvent L)] with omega hb
    simp [actualClockRecord,hb]
  rw [Measure.map_congr he]
  simp

/-- The true border contribution to any capped marked test, under the current source measure. -/
theorem true_test_mass (L K : ℕ) (alpha : ℝ≥0) (halpha : mu.real (borderEvent L) = (alpha : ℝ))
    (hpos : 0 < alpha)
    (hclock : (cond mu (borderEvent L)).map (actualClockRecord L K) =
      (geometricMeasure halfSuccess).map (fun j => (true,min j K))) (S : Set Record) :
    (AffineCrossoverModel.recordMeasure mu L K).real {v | v.1=true ∧ borderLabel v.2∈S} =
      (alpha : ℝ)*(cappedBorderLaw K).real S := by
  let T : Set (Bool×ℕ) := {v | v.1=true ∧ borderLabel v.2∈S}
  have he : borderEvent L ∩ (actualClockRecord L K ⁻¹' T) = actualClockRecord L K ⁻¹' T := by
    apply Set.inter_eq_right.mpr
    intro omega h
    by_contra hb
    simp [T,actualClockRecord,hb] at h
  have hc := congrArg (fun nu : Measure (Bool×ℕ) => nu.real T) hclock
  rw [map_measureReal_apply (measurable_actualClockRecord L K) (Set.to_countable _).measurableSet,
    cond_real_apply _ _ (measurableSet_borderEvent L),he] at hc
  have ht : ((geometricMeasure halfSuccess).map (fun j => (true,min j K))).real T =
      (cappedBorderLaw K).real S := by
    rw [cappedBorderLaw,borderLaw,Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    rw [map_measureReal_apply (measurable_of_countable _) (Set.to_countable _).measurableSet,
      map_measureReal_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
    congr 1
    ext j
    simp [T,capBorder,borderLabel]
  rw [ht,halpha] at hc
  rw [AffineCrossoverModel.recordMeasure,
    map_measureReal_apply (measurable_actualClockRecord L K) (Set.to_countable _).measurableSet]
  exact ((div_eq_iff (show (alpha : ℝ) ≠ 0 from ne_of_gt (by exact_mod_cast hpos))).mp hc).trans
    (mul_comm _ _)

end
end PaperC.V282.AffineCrossoverRecordMass
