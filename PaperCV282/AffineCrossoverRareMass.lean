import PaperCV282.AffineCrossoverSourceCoupling

/-! # Finite rare-hit mass under an arbitrary absolutely continuous source

The product comparison uses the true conditioned border marginal. The
exceptional probabilities are measured under that same source.
-/
namespace PaperC.V282.AffineCrossoverRareMass

open MeasureTheory ProbabilityTheory Set Filter InfiniteRademacher SharpConditioning
open CrossoverSourceGeometry CrossoverMarkedCandidate CrossoverPrimeClockStable
open CrossoverBulkAtoms CrossoverBulkOnePoint BulkMarkedSource BulkMarkedGeometry
open RarePrefixGeometry RarePrefixEvents MicroscopicNonvacancy MicroscopicBorderEvents
open AffineCrossoverModel
open scoped NNReal ENNReal

noncomputable section

theorem record_false_mass (mu : Measure InfiniteSample) [IsProbabilityMeasure mu] (L K : ℕ) :
    (recordMeasure mu L K).real {v | v.1=false}=1-mu.real (borderEvent L) := by
  have hp : actualClockRecord L K ⁻¹' {v : Bool×ℕ | v.1=false}=(borderEvent L)ᶜ := by
    ext omega
    simp [actualClockRecord]
  rw [recordMeasure,map_measureReal_apply (measurable_actualClockRecord L K)
    (Set.to_countable _).measurableSet,hp,measureReal_compl (measurableSet_borderEvent L),probReal_univ]

theorem product_rare_mass (mu : Measure InfiniteSample) [IsProbabilityMeasure mu]
    (sites : Finset ℕ) (L K : ℕ) :
    (productJoint mu sites L K).real (rareEvent sites)=
      1-(1-mu.real (borderEvent L))*Real.exp (-(totalRate sites L : ℝ)) := by
  have he : rareEvent sites=({v : Bool×ℕ | v.1=false} ×ˢ {c | totalSize sites c=0})ᶜ := by
    ext z
    cases h : z.1.1 <;> simp [rareEvent,h]
  rw [he,measureReal_compl ((Set.to_countable _).measurableSet.prod
    (Set.to_countable _).measurableSet),probReal_univ,AffineCrossoverModel.productJoint,measureReal_prod_prod,record_false_mass,
    total_size_probability]
  simp

theorem hit_source_rare_error_le (mu : Measure InfiniteSample) [IsProbabilityMeasure mu]
    (habs : mu ≪ infiniteRademacherMeasure) {M L K : ℕ} {delta : ℝ}
    (hM : 2≤M) (hL : 1≤L) (hLM : L≤M) (hdelta : 0<delta) :
    |mu.real (hitEvent M L)-(sourceJoint mu M L K delta).real (rareEvent (bulkStarts M L delta))| ≤
      mu.real (interiorEvent L)+mu.real (middleEvent M L delta) := by
  let f := fun omega => (actualClockRecord L K omega,
    spatialMarkedSource (bulkStarts M L delta) L omega)
  have hf : Measurable f := (measurable_actualClockRecord L K).prodMk
    (measurable_spatialMarkedSource _ _)
  rw [AffineCrossoverModel.sourceJoint,map_measureReal_apply hf (Set.to_countable _).measurableSet]
  apply (abs_measureReal_sub_le_measureReal_symmDiff (measurableSet_hitEvent M L).nullMeasurableSet
    (hf (Set.to_countable _).measurableSet).nullMeasurableSet).trans
  apply le_trans ?_ (measureReal_union_le (μ := mu) _ _)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [habs.ae_le (ae_hit_iff_rareEvent (K := K) hM hL hLM hdelta)] with omega ho
  intro hs
  by_contra hn
  have hi : omega∉interiorEvent L := fun h => hn (Or.inl h)
  have hm : omega∉middleEvent M L delta := fun h => hn (Or.inr h)
  have he := ho hi hm
  change (omega∈hitEvent M L ∧ omega∉f ⁻¹' rareEvent _) ∨
    (omega∈f ⁻¹' rareEvent _ ∧ omega∉hitEvent M L) at hs
  rcases hs with hs | hs
  · exact hs.2 (he.mp hs.1)
  · exact hs.2 (he.mpr hs.1)

/-- Quantitative before any limiting passage or division by the rare probability. -/
theorem hit_probability_error_le (mu : Measure InfiniteSample) [IsProbabilityMeasure mu]
    (habs : mu ≪ infiniteRademacherMeasure) {M L K : ℕ} {delta : ℝ}
    (hM : 2≤M) (hL : 1≤L) (hLM : L≤M) (hdelta : 0<delta) :
    |hitProbability mu M L-(mu.real (borderEvent L)+(totalRate (bulkStarts M L delta) L : ℝ))| ≤
      mu.real (interiorEvent L)+mu.real (middleEvent M L delta)+jointDistance mu M L K delta+
      (totalRate (bulkStarts M L delta) L : ℝ)^2+
      mu.real (borderEvent L)*(totalRate (bulkStarts M L delta) L : ℝ) := by
  have h1 := hit_source_rare_error_le mu habs (K := K) hM hL hLM hdelta
  have h2 := discrepancy_le (sourceJoint mu M L K delta) (productJoint mu (bulkStarts M L delta) L K)
    (rareEvent _) (Set.to_countable _).measurableSet
  rw [product_rare_mass] at h2
  have ha : mu.real (borderEvent L)≤1 := measureReal_le_one
  have h3 := RarePrefixPoisson.independent_union_error_le
    (measureReal_nonneg (μ := mu) (s := borderEvent L)) ha
    (show (0 : ℝ)≤(totalRate (bulkStarts M L delta) L : ℝ) by positivity)
  have h4 := abs_sub_le (mu.real (hitEvent M L))
    ((sourceJoint mu M L K delta).real (rareEvent (bulkStarts M L delta)))
    (1-(1-mu.real (borderEvent L))*Real.exp (-(totalRate (bulkStarts M L delta) L : ℝ)))
  have h5 := abs_sub_le (mu.real (hitEvent M L))
    (1-(1-mu.real (borderEvent L))*Real.exp (-(totalRate (bulkStarts M L delta) L : ℝ)))
    (mu.real (borderEvent L)+(totalRate (bulkStarts M L delta) L : ℝ))
  change |(sourceJoint mu M L K delta).real (rareEvent (bulkStarts M L delta))-_|
    ≤jointDistance mu M L K delta at h2
  dsimp [hitProbability] at *
  linarith

end
end PaperC.V282.AffineCrossoverRareMass
