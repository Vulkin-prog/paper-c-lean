import PaperCV282.D4ClosureSpatialIdentification

/-! # Upper-half point configurations are restrictions of the same whole target -/
namespace PaperC.V282.D4ClosureWholeRestriction

open MeasureTheory ProbabilityTheory
open D4ClosurePointMeasure D4ClosureSpatialHalfLines D4ClosureSpatialIdentification
open D4GridIdentificationConfiguration PointMeasureSpace
open scoped BigOperators ENNReal

noncomputable section

def upperPosition (m : ℤ) (x : ℝ × (ℕ × F₂)) : ℝ × ℤ := (x.1,m+x.2.1)

theorem measurable_upperPosition (m : ℤ) : Measurable (upperPosition m) :=
  measurable_fst.prodMk (measurable_const.add
    ((measurable_of_countable (fun e : ℕ => (e : ℤ))).comp (measurable_fst.comp measurable_snd)))

theorem integerPointMeasure_upper_finite_sum (sample : IntegerSpatialSample) (m : ℤ)
    (c : ℕ→₀ℕ) (hc : ∀ e : ℕ, c e=(sample (m+e)).1) :
    (integerPointMeasure sample).restrict (Set.univ ×ˢ Set.Ici m)=
      ∑ e ∈ c.support, integerPointRow sample (m+e) := by
  classical
  let s : Finset ℤ := c.support.image (fun e : ℕ => m+e)
  apply Measure.ext
  intro A hA
  rw [Measure.restrict_apply hA,integerPointMeasure,
    Measure.sum_apply _ (hA.inter (MeasurableSet.univ.prod measurableSet_Ici))]
  have hz (r : ℤ) (hr : r∉s) : integerPointRow sample r (A ∩ (Set.univ ×ˢ Set.Ici m))=0 := by
    by_cases hmr : r<m
    · simp [integerPointRow,Measure.coe_finsetSum,Finset.sum_apply,
        Measure.dirac_apply' _ (hA.inter (MeasurableSet.univ.prod measurableSet_Ici)),
        Set.indicator,not_le.mpr hmr]
    · let e : ℕ := (r-m).toNat
      have he : m+e=r := by dsimp [e]; omega
      have hec : e∉c.support := by
        intro h
        exact hr (Finset.mem_image.mpr ⟨e,h,he⟩)
      have hc0 : (sample r).1=0 := by
        rw [← he,← hc e]
        exact Finsupp.notMem_support_iff.mp hec
      simp [integerPointRow,hc0]
  rw [tsum_eq_sum hz]
  change (∑ r ∈ c.support.image (fun e : ℕ => m+e), integerPointRow sample r
    (A ∩ (Set.univ ×ˢ Set.Ici m)))=_
  rw [Finset.sum_image (fun e he f hf h => by omega),Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro e he
  simp [integerPointRow,Measure.coe_finsetSum,Finset.sum_apply,
    Measure.dirac_apply' _ (hA.inter (MeasurableSet.univ.prod measurableSet_Ici)),
    Measure.dirac_apply' _ hA,Set.indicator]

theorem map_pointsFromCounts (sample : IntegerSpatialSample) (m : ℤ)
    (c : ℕ→₀ℕ) (hc : ∀ e : ℕ, c e=(sample (m+e)).1) :
    ((pointsFromCounts m c sample).val.map (upperPosition m))=
      ∑ e ∈ c.support, integerPointRow sample (m+e) := by
  classical
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply (measurable_upperPosition m) hA]
  change ((∑ e ∈ c.support, fixedPointMeasure (c e)
    (fun i => (1+((sample (m+e)).2 i : ℝ),(e,(0 : F₂))))) : PointMeasure (ℝ × (ℕ × F₂))).val
      (upperPosition m ⁻¹' A) = _
  change ((↑(∑ e ∈ c.support, (show FiniteMeasure (ℝ × (ℕ × F₂)) from
    fixedPointMeasure (c e) (fun i => (1+((sample (m+e)).2 i : ℝ),(e,(0 : F₂)))))) : Measure _)
      (upperPosition m ⁻¹' A)) = _
  rw [FiniteMeasure.toMeasure_sum,Measure.finsetSum_apply,Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro e he
  rw [hc e]
  change ((↑(∑ i ∈ Finset.range ((sample (m+e)).1),
    (show FiniteMeasure (ℝ × (ℕ × F₂)) from pointDirac (1+((sample (m+e)).2 i : ℝ),(e,(0 : F₂)))))) :
      Measure _) (upperPosition m ⁻¹' A) = _
  rw [FiniteMeasure.toMeasure_sum,Measure.finsetSum_apply]
  change _ = (∑ i ∈ Finset.range ((sample (m+e)).1),
    Measure.dirac (1+((sample (m+e)).2 i : ℝ),m+e)) A
  rw [Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  change (Measure.dirac (1+((sample (m+e)).2 i : ℝ),(e,(0 : F₂)))) (upperPosition m ⁻¹' A) = _
  rw [Measure.dirac_apply' _ ((measurable_upperPosition m) hA),Measure.dirac_apply' _ hA]
  rfl

/-- This identifies the constructed finite half-line with the literal restriction
of the complete locally finite measure, on the original probability space. -/
theorem ae_halfLinePointConfiguration_is_restriction (theta : ℝ) (m : ℤ) :
    ∀ᵐ sample ∂integerSpatialSampleMeasure theta,
      ((halfLinePointConfiguration m sample).val.map (upperPosition m))=(integerPointMeasure sample).restrict (Set.univ ×ˢ Set.Ici m) := by
  filter_upwards [ae_spatialHalfCounts_coordinates theta m] with sample hc
  change ((pointsFromCounts m (D4GridIdentificationConfiguration.spatialHalfCounts m sample) sample).val.map (upperPosition m))=_
  rw [map_pointsFromCounts sample m _ hc,integerPointMeasure_upper_finite_sum sample m _ hc]

end
end PaperC.V282.D4ClosureWholeRestriction
