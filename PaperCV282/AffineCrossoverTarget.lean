import PaperCV282.CrossoverMovingTarget

/-! # The moving marked mixture with an arbitrary boundary mass

The boundary probability is supplied by the actual affine cylinder. The bulk
population and its exact Poisson intensity are unchanged.
-/
namespace PaperC.V282.AffineCrossoverTarget

open MeasureTheory ProbabilityTheory CrossoverMarkedModel CrossoverMarkedTarget
open CrossoverMarkedCandidate CrossoverBulkAtoms CrossoverClockRecordMass BulkMarkedGeometry
open scoped NNReal ENNReal

noncomputable section

def borderWeight (sites : Finset ℕ) (L : ℕ) (alpha : ℝ≥0) : ℝ≥0 :=
  alpha/(alpha+totalRate sites L)

def bulkWeight (sites : Finset ℕ) (L : ℕ) (alpha : ℝ≥0) : ℝ≥0 :=
  totalRate sites L/(alpha+totalRate sites L)

theorem weights_sum (sites : Finset ℕ) (hs : sites.Nonempty) (L : ℕ) (alpha : ℝ≥0) :
    borderWeight sites L alpha+bulkWeight sites L alpha=1 := by
  have hb : 0<totalRate sites L := by
    unfold totalRate
    have h := Finset.card_pos.mpr hs
    positivity
  unfold borderWeight bulkWeight
  rw [← add_div,div_self (ne_of_gt (add_pos_of_nonneg_of_pos (by positivity) hb))]

def mixedLaw (sites : Finset ℕ) (hs : sites.Nonempty) (L : ℕ) (alpha : ℝ≥0) : Measure Record :=
  (borderWeight sites L alpha : ℝ≥0∞) • borderLaw+
    (bulkWeight sites L alpha : ℝ≥0∞) • bulkLaw sites hs

instance instProbabilityMixedLaw (sites : Finset ℕ) (hs : sites.Nonempty) (L : ℕ) (alpha : ℝ≥0) :
    IsProbabilityMeasure (mixedLaw sites hs L alpha) := by
  constructor
  simp only [mixedLaw,Measure.add_apply,Measure.smul_apply,smul_eq_mul,measure_univ,mul_one]
  exact_mod_cast weights_sum sites hs L alpha

theorem mixedLaw_real (sites : Finset ℕ) (hs : sites.Nonempty) (L : ℕ) (alpha : ℝ≥0) (S : Set Record) :
    (mixedLaw sites hs L alpha).real S=
      (borderWeight sites L alpha : ℝ)*borderLaw.real S+
        (bulkWeight sites L alpha : ℝ)*(bulkLaw sites hs).real S := by
  unfold mixedLaw
  rw [measureReal_add_apply
    (by simpa only [Measure.smul_apply,smul_eq_mul] using
      ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top borderLaw S))
    (by simpa only [Measure.smul_apply,smul_eq_mul] using
      ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top (bulkLaw sites hs) S))]
  simp only [measureReal_ennreal_smul_apply,ENNReal.coe_toReal]

theorem capBorder_bulkLabel (K : ℕ) (sites : Finset ℕ) (j : BulkMarkedTypes.SpatialMarkedIndex sites) :
    capBorder K (bulkLabel sites j)=bulkLabel sites j := rfl

theorem capped_bulkLaw (K : ℕ) (sites : Finset ℕ) (hs : sites.Nonempty) :
    (bulkLaw sites hs).map (capBorder K)=bulkLaw sites hs := by
  rw [bulkLaw,Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  rfl

theorem capped_mixedLaw_real (sites : Finset ℕ) (hs : sites.Nonempty) (L K : ℕ)
    (alpha : ℝ≥0) (S : Set Record) :
    ((mixedLaw sites hs L alpha).map (capBorder K)).real S=
      (borderWeight sites L alpha : ℝ)*(cappedBorderLaw K).real S+
        (bulkWeight sites L alpha : ℝ)*(bulkLaw sites hs).real S := by
  rw [map_measureReal_apply (measurable_of_countable _) (Set.to_countable _).measurableSet,mixedLaw_real]
  have hb : borderLaw.real (capBorder K ⁻¹' S)=(cappedBorderLaw K).real S := by
    rw [cappedBorderLaw,map_measureReal_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
  have hc : (bulkLaw sites hs).real (capBorder K ⁻¹' S)=(bulkLaw sites hs).real S := by
    rw [← map_measureReal_apply (measurable_of_countable _) (Set.to_countable _).measurableSet,capped_bulkLaw]
  rw [hb,hc]

def targetLaw (M L : ℕ) (delta : ℝ) (alpha : ℝ≥0) : Measure Record :=
  if hs : (bulkStarts M L delta).Nonempty then mixedLaw (bulkStarts M L delta) hs L alpha else borderLaw

instance instProbabilityTargetLaw (M L : ℕ) (delta : ℝ) (alpha : ℝ≥0) :
    IsProbabilityMeasure (targetLaw M L delta alpha) := by
  unfold targetLaw
  split_ifs <;> infer_instance

theorem targetLaw_eq {M L : ℕ} {delta : ℝ} (alpha : ℝ≥0)
    (hs : (bulkStarts M L delta).Nonempty) :
    targetLaw M L delta alpha=mixedLaw (bulkStarts M L delta) hs L alpha := by
  simp only [targetLaw,dif_pos hs]

theorem mixedLaw_positive (sites : Finset ℕ) (hs : sites.Nonempty) (L : ℕ) (alpha : ℝ≥0) :
    (mixedLaw sites hs L alpha).real {r | positiveSign r=true}=
      ((alpha : ℝ)+(totalRate sites L : ℝ)/2)/((alpha : ℝ)+(totalRate sites L : ℝ)) := by
  rw [mixedLaw_real,borderLaw_positive,bulkLaw_positive]
  simp only [borderWeight,bulkWeight,NNReal.coe_div,NNReal.coe_add]
  ring

end
end PaperC.V282.AffineCrossoverTarget
