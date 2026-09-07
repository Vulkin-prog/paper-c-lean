import PaperCV282.CrossoverMarkedCandidate

/-! # Exact border-cylinder masses before the rare event is normalized -/
namespace PaperC.V282.CrossoverClockRecordMass

open MeasureTheory ProbabilityTheory InfiniteRademacher MicroscopicBorderEvents
open CrossoverPrimeClockStable CrossoverPrimeClockLaw CrossoverMarkedModel CrossoverMarkedTarget
open CrossoverMarkedCandidate SharpConditioning GeometricClusterTarget

noncomputable section
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P
local instance instProbabilityInfinite : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

def recordMeasure (L K : ℕ) : Measure (Bool × ℕ) := infiniteRademacherMeasure.map (actualClockRecord L K)

instance instProbabilityRecordMeasure (L K : ℕ) : IsProbabilityMeasure (recordMeasure L K) :=
  Measure.isProbabilityMeasure_map (measurable_actualClockRecord L K).aemeasurable

theorem border_probability (L : ℕ) : infiniteRademacherMeasure.real (borderEvent L)=(borderRate L : ℝ) := by
  rw [equation_seven_one]
  simp [borderRate,one_div,inv_pow]

def cappedBorderLaw (K : ℕ) : Measure Record := borderLaw.map (capBorder K)

instance instProbabilityCappedBorderLaw (K : ℕ) : IsProbabilityMeasure (cappedBorderLaw K) :=
  Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

theorem true_test_mass (L K : ℕ) (S : Set Record) :
    (recordMeasure L K).real {v | v.1=true ∧ borderLabel v.2∈S}=
      (borderRate L : ℝ)*(cappedBorderLaw K).real S := by
  let T : Set (Bool × ℕ) := {v | v.1=true ∧ borderLabel v.2∈S}
  have he : borderEvent L ∩ (actualClockRecord L K ⁻¹' T)=actualClockRecord L K ⁻¹' T := by
    apply Set.inter_eq_right.mpr
    intro omega h
    by_contra hb
    simp [T,actualClockRecord,hb] at h
  have hc := congrArg (fun mu : Measure (Bool × ℕ) => mu.real T) (conditional_actualClockRecord L K)
  rw [map_measureReal_apply (measurable_actualClockRecord L K) (Set.to_countable _).measurableSet,
    cond_real_apply _ _ (measurableSet_borderEvent L),he] at hc
  have ht : ((geometricMeasure halfSuccess).map (fun G => (true,min G K))).real T=
      (cappedBorderLaw K).real S := by
    rw [cappedBorderLaw,borderLaw,Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    rw [map_measureReal_apply (measurable_of_countable _) (Set.to_countable _).measurableSet,
      map_measureReal_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
    congr 1
    ext G
    simp [T,capBorder,borderLabel]
  rw [ht] at hc
  rw [recordMeasure,map_measureReal_apply (measurable_actualClockRecord L K) (Set.to_countable _).measurableSet]
  change infiniteRademacherMeasure.real (actualClockRecord L K ⁻¹' T)=_
  rw [← border_probability]
  exact ((div_eq_iff (borderEvent_probability_pos L).ne').mp hc).trans (mul_comm _ _)

theorem record_true_mass (L K : ℕ) :
    (recordMeasure L K).real {v | v.1=true}=(borderRate L : ℝ) := by
  simpa only [Set.mem_univ,and_true,probReal_univ,mul_one] using true_test_mass L K Set.univ

theorem record_false_mass (L K : ℕ) :
    (recordMeasure L K).real {v | v.1=false}=1-(borderRate L : ℝ) := by
  have he : {v : Bool × ℕ | v.1=false}={v | v.1=true}ᶜ := by ext v; cases v.1 <;> simp
  rw [he,measureReal_compl (Set.to_countable _).measurableSet,probReal_univ,record_true_mass]

theorem borderRate_le_one (L : ℕ) : (borderRate L : ℝ) ≤ 1 := by
  rw [← border_probability]
  exact measureReal_le_one

end
end PaperC.V282.CrossoverClockRecordMass
