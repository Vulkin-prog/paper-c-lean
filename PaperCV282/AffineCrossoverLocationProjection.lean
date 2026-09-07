import PaperCV282.AffineCrossoverTarget
import PaperCV282.AffineCrossoverLocationSource
import PaperCV282.AffineCrossoverLocationTarget

/-! # Exact projections of the affine moving marked target

Every location projection ignores the boundary prime clock.  Consequently
the capped comparison with cap zero is sufficient for this whole module.
-/
namespace PaperC.V282.AffineCrossoverLocationProjection

open MeasureTheory ProbabilityTheory CrossoverMarkedModel CrossoverMarkedTarget
open CrossoverMarkedCandidate CrossoverLocationProjection CrossoverResolvedLocationSource
open CrossoverResolvedLocationTarget CrossoverLocationGrid CrossoverLocationMixture
open AffineCrossoverLocationTarget BulkMarkedGeometry CountableWeakTransfer
open scoped NNReal ENNReal

noncomputable section
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

theorem capBorder_recordStart (K : ℕ) (r : Record) : recordStart (capBorder K r)=recordStart r := by
  cases r with
  | none => rfl
  | some r => cases r <;> rfl

theorem capBorder_recordInteger (K : ℕ) (r : Record) : recordInteger (capBorder K r)=recordInteger r := by
  cases r with
  | none => rfl
  | some r => cases r <;> rfl

theorem capBorder_eq_none (K : ℕ) (r : Record) : capBorder K r=none ↔ r=none := by
  cases r with
  | none => simp [capBorder]
  | some r => cases r <;> simp [capBorder,borderLabel]

theorem targetLaw_cemetery_zero (M L : ℕ) (delta : ℝ) (alpha : ℝ≥0) :
    (AffineCrossoverTarget.targetLaw M L delta alpha).real {none}=0 := by
  unfold AffineCrossoverTarget.targetLaw
  split_ifs with hs
  · rw [AffineCrossoverTarget.mixedLaw_real]
    have hb : borderLaw.real {none}=0 := by
      rw [borderLaw,Measure.real,Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
      have he : borderLabel ⁻¹' {none}=∅ := by ext k; simp [borderLabel]
      simp [he]
    have hc : (bulkLaw (bulkStarts M L delta) hs).real {none}=0 := by
      rw [bulkLaw,Measure.real,Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
      have he : bulkLabel (bulkStarts M L delta) ⁻¹' {none}=∅ := by ext k; simp [bulkLabel]
      simp [he]
    simp [hb,hc]
  · rw [borderLaw,Measure.real,Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
    have he : borderLabel ⁻¹' {none}=∅ := by ext k; simp [borderLabel]
    simp [he]

theorem borderWeight_eq (M L : ℕ) (delta : ℝ) (d : ℕ) :
    AffineCrossoverTarget.borderWeight (bulkStarts M L delta) L (((2 : ℝ≥0)⁻¹)^d)=
      AffineCrossoverLocationTarget.borderWeight M L delta d := rfl

theorem bulkWeight_eq (M L : ℕ) (delta : ℝ) (d : ℕ) :
    AffineCrossoverTarget.bulkWeight (bulkStarts M L delta) L (((2 : ℝ≥0)⁻¹)^d)=
      AffineCrossoverLocationTarget.bulkWeight M L delta d := rfl

theorem targetLaw_recordPosition (M L : ℕ) (delta : ℝ) (d : ℕ) :
    (AffineCrossoverTarget.targetLaw M L delta (((2 : ℝ≥0)⁻¹)^d)).map
      (fun r => (recordStart r : ℝ)/M)=
        (physicalTargetLaw M L delta d : Measure ℝ) := by
  by_cases hs : (bulkStarts M L delta).Nonempty
  · rw [AffineCrossoverTarget.targetLaw_eq _ hs,AffineCrossoverTarget.mixedLaw,
      Measure.map_add _ _ (measurable_of_countable _),Measure.map_smul,Measure.map_smul,
      borderLaw_recordPosition,bulkLaw_recordPosition]
    change _=(AffineCrossoverLocationTarget.borderWeight M L delta d : ℝ≥0∞) • Measure.dirac (1/(M : ℝ))+
      (AffineCrossoverLocationTarget.bulkWeight M L delta d : ℝ≥0∞) • (bulkLocationLaw M L delta : Measure ℝ)
    rw [bulkLocationLaw_eq_uniform_site M L delta hs,borderWeight_eq,bulkWeight_eq]
  · have he : bulkStarts M L delta=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    have hz : BulkPopulation.bulkRate M L delta=0 := by
      apply NNReal.coe_injective
      rw [BulkPopulation.bulkRate_coe,he]
      norm_num
    have hb : AffineCrossoverLocationTarget.borderWeight M L delta d=1 := by
      rw [AffineCrossoverLocationTarget.borderWeight,hz,add_zero,div_self (by positivity)]
    have hc : AffineCrossoverLocationTarget.bulkWeight M L delta d=0 := by
      simp [AffineCrossoverLocationTarget.bulkWeight,hz]
    rw [AffineCrossoverTarget.targetLaw,dif_neg hs,borderLaw_recordPosition]
    simp [physicalTargetLaw,mixtureLaw,hb,hc,borderLocationLaw]

theorem targetLaw_twoClockPosition (M L : ℕ) (delta : ℝ) (d : ℕ) :
    (AffineCrossoverTarget.targetLaw M L delta (((2 : ℝ≥0)⁻¹)^d)).map (twoClockPosition M L)=
      (AffineCrossoverLocationTarget.resolvedTargetLaw M L delta d : Measure (Bool×ℝ)) := by
  by_cases hs : (bulkStarts M L delta).Nonempty
  · rw [AffineCrossoverTarget.targetLaw_eq _ hs,AffineCrossoverTarget.mixedLaw,
      Measure.map_add _ _ (measurable_of_countable _),Measure.map_smul,Measure.map_smul,
      borderLaw_twoClockPosition,bulkLaw_twoClockPosition M L delta hs,borderWeight_eq,bulkWeight_eq]
    rfl
  · have he : bulkStarts M L delta=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    have hz : BulkPopulation.bulkRate M L delta=0 := by
      apply NNReal.coe_injective
      rw [BulkPopulation.bulkRate_coe,he]
      norm_num
    have hb : AffineCrossoverLocationTarget.borderWeight M L delta d=1 := by
      rw [AffineCrossoverLocationTarget.borderWeight,hz,add_zero,div_self (by positivity)]
    have hc : AffineCrossoverLocationTarget.bulkWeight M L delta d=0 := by
      simp [AffineCrossoverLocationTarget.bulkWeight,hz]
    rw [AffineCrossoverTarget.targetLaw,dif_neg hs,borderLaw_twoClockPosition]
    simp [AffineCrossoverLocationTarget.resolvedTargetLaw,resolvedMixture,hb,hc]

def targetStartLaw (M L : ℕ) (delta : ℝ) (d : ℕ) : ProbabilityMeasure ℕ :=
  imageProbabilityLaw (AffineCrossoverTarget.targetLaw M L delta (((2 : ℝ≥0)⁻¹)^d))
    recordStart (measurable_of_countable _)

def targetResolvedIntegerLaw (M L : ℕ) (delta : ℝ) (d : ℕ) : ProbabilityMeasure (Bool×ℕ) :=
  imageProbabilityLaw (AffineCrossoverTarget.targetLaw M L delta (((2 : ℝ≥0)⁻¹)^d))
    recordInteger (measurable_of_countable _)

theorem targetStartLaw_position (M L : ℕ) (delta : ℝ) (d : ℕ) :
    (targetStartLaw M L delta d : Measure ℕ).map (fun x : ℕ => (x : ℝ)/M)=
      (physicalTargetLaw M L delta d : Measure ℝ) := by
  change ((AffineCrossoverTarget.targetLaw M L delta (((2 : ℝ≥0)⁻¹)^d)).map recordStart).map _=_
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  exact targetLaw_recordPosition M L delta d

theorem targetResolvedIntegerLaw_position (M L : ℕ) (delta : ℝ) (d : ℕ) :
    (targetResolvedIntegerLaw M L delta d : Measure (Bool×ℕ)).map (resolvedPosition M L)=
      (AffineCrossoverLocationTarget.resolvedTargetLaw M L delta d : Measure (Bool×ℝ)) := by
  change ((AffineCrossoverTarget.targetLaw M L delta (((2 : ℝ≥0)⁻¹)^d)).map recordInteger).map _=_
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  simpa only [Function.comp_def,resolvedPosition_recordInteger] using targetLaw_twoClockPosition M L delta d

end
end PaperC.V282.AffineCrossoverLocationProjection
