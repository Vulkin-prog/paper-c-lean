import PaperCPrel8.MicroscopicSourceRelabelling
import PaperCPrel8.MicroscopicDiscardTheorem

/-! # Genuine event-conditioned spatial laws, without an excess cutoff

The finite comparison is transported through an exact bijection. Truncation
costs the actual conditional source tail and the independent Poisson tail.
-/
namespace PaperC.Prel8.MicroscopicConditionalSpatial
open MeasureTheory ProbabilityTheory PaperC.InfiniteRademacher PaperC.InfiniteCylinderTransfer
open PaperC.Prel8.MicroscopicSourceRelabelling PaperC.Prel8.MicroscopicInfiniteField
open PaperC.Prel8.MicroscopicValueProfile PaperC.Prel8.MicroscopicDiscardBounds
open PaperC.Prel8.ActualSignedPalm
open PaperC.InfiniteExactLengthProbabilityTransfer PaperC.V282.FiniteStartMaskAverages
open PaperC.ConditionalStartProbability PaperC.ArratiaGoldsteinGordonInput
open PaperC.V282.BulkMarkedTypes PaperC.V282.BulkMarkedSource
open PaperC.V282.BulkMarkedTarget PaperC.V282.BulkMarkedComparison
open PaperC.V282.BulkMarkedInfinite PaperC.V282.BulkMarkedTransfer
open PaperC.V282.BulkMarkedTargetProjection PaperC.V282.FiniteFieldPoissonCoupling
open PaperC.V282.ConditionedCountableLaw PaperC.V282.CountableLawTransfer
open PaperC.V282.InfiniteMassCoupling PaperC.V282.FiniteFieldTotalVariation
open PaperC.V282.MassPushforward PaperC.V282.MovingMarkedLevels
noncomputable section
local instance : MeasurableSpace PaperC.F₂ := ⊤
local instance : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

/-- The represented small-prime event on the original infinite probability space. -/
def traceEvent (C Y : ℕ) (A : SmallSample C Y → Prop) : Set InfiniteSample :=
  {ω | A (restrictSmall C Y (restrictToFinite C ω))}

theorem measurableSet_traceEvent (C Y : ℕ) (A : SmallSample C Y → Prop) :
    MeasurableSet (traceEvent C Y A) :=
  (measurable_restrictToFinite C) (Set.toFinite {σ : SampleSpace C | A (restrictSmall C Y σ)} |>.measurableSet)

theorem traceEvent_probability (C Y : ℕ) (A : SmallSample C Y → Prop) :
    infiniteRademacherMeasure.real (traceEvent C Y A) =
      eventProbability (FinitePMF.uniform (SampleSpace C)) (fun σ => A (restrictSmall C Y σ)) :=
  cylinder_probability C (fun σ => A (restrictSmall C Y σ))

/-- Relabelling identifies actual conditional masses, including their normalization. -/
theorem conditional_vector_law (C Y L E : ℕ) (G : Finset ℕ) (A : SmallSample C Y → Prop) :
    conditionalObservableLaw infiniteRademacherMeasure (traceEvent C Y A)
      (infiniteSignedField (retainedStarts G) L E (retainedStarts G)) =
      pushforwardMass (vectorEquiv G E) (conditionalLaw C Y L E G A) := by
  funext z
  rw [conditionalObservableLaw_eq_ratio _ _ (measurableSet_traceEvent C Y A),pushforwardMass_equiv]
  unfold conditionalLaw
  congr 2
  ext ω
  simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,traceEvent,infinite_vector_eq]
  rw [← Equiv.eq_symm_apply]
  exact and_comm

/-- The finite spatial comparison and the boundary-indexed comparison have identical TV. -/
theorem conditional_vector_distance (C Y L E : ℕ) (G : Finset ℕ) (A : SmallSample C Y → Prop) :
    massTotalVariation
      (conditionalObservableLaw infiniteRademacherMeasure (traceEvent C Y A)
        (infiniteSignedField (retainedStarts G) L E (retainedStarts G)))
      (poissonFieldMass (allSignedRates (retainedStarts G) L E (retainedStarts G))) =
      massTotalVariation (conditionalLaw C Y L E G A) (poissonFieldMass (rate L)) := by
  rw [conditional_vector_law]
  have ht : poissonFieldMass (allSignedRates (retainedStarts G) L E (retainedStarts G)) =
      pushforwardMass (vectorEquiv G E) (poissonFieldMass (rate L)) := by
    funext z
    obtain ⟨w,rfl⟩ := (vectorEquiv G E).surjective z
    rw [poisson_vector_eq,pushforwardMass_equiv,Equiv.symm_apply_apply]
  rw [ht,massTotalVariation_equiv]

/-- The spatial tail is contained in the unsigned exact-excess event used in the arithmetic bound. -/
theorem spatial_tail_subset_excess (sites : Finset ℕ) (L E : ℕ) :
    spatialSourceTail sites L E ⊆ excessTail L E sites := by
  rintro ω ⟨j,he,hj⟩
  have hm := (spatialMarkedValue_ne_zero_iff sites L ω j).mp hj
  exact ⟨j.1.val,j.1.property,j.2.1,he,hm.1⟩

/-- Remove the excess cutoff for any measurable positive conditioning event. -/
theorem spatial_distance_le_finite_and_tails (sites : Finset ℕ) (L E : ℕ)
    (A : Set InfiniteSample) (hA : MeasurableSet A) (hpos : 0 < infiniteRademacherMeasure.real A) :
    massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure A (spatialMarkedSource sites L))
      (spatialTargetLaw sites L) ≤
      infiniteRademacherMeasure.real (A ∩ excessTail L E sites)/infiniteRademacherMeasure.real A +
      massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure A
        (infiniteSignedField sites L E sites)) (poissonFieldMass (allSignedRates sites L E sites)) +
      (maskRate L sites:ℝ)/(2:ℝ)^(E+1) := by
  let : IsProbabilityMeasure (cond infiniteRademacherMeasure A) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hpos)
  have hs : (cond infiniteRademacherMeasure A).real {ω | spatialMarkedSource sites L ω ≠
      embedConfiguration sites E (infiniteSignedField sites L E sites ω)} ≤
      infiniteRademacherMeasure.real (A ∩ excessTail L E sites)/infiniteRademacherMeasure.real A := by
    have hd : {ω | spatialMarkedSource sites L ω ≠
        embedConfiguration sites E (infiniteSignedField sites L E sites ω)} ⊆ excessTail L E sites := by
      intro ω hω
      by_contra hn
      apply hω
      rw [← project_spatialMarkedSource,embed_project_configuration]
      exact spatialMarkedSource_eq_truncate_off_tail sites L E ω
        (fun h => hn (spatial_tail_subset_excess sites L E h))
    apply (measureReal_mono hd (measure_ne_top _ _)).trans_eq
    unfold Measure.real
    rw [cond_apply hA,ENNReal.toReal_mul,ENNReal.toReal_inv]
    ring
  have ht : observableLaw (spatialTargetMeasure sites L) (projectConfiguration sites E) =
      poissonFieldMass (allSignedRates sites L E sites) := funext (spatial_project_mass_eq sites L E)
  have h := truncation_tv_le_of_bounds (cond infiniteRademacherMeasure A) (spatialTargetMeasure sites L)
    (measurable_spatialMarkedSource sites L) measurable_id (measurable_infiniteSignedField_full sites L E)
    (measurable_of_countable (projectConfiguration sites E)) (embedConfiguration sites E)
    hs (le_refl _) (target_embedding_disagreement_le sites L E)
  rw [ht] at h
  exact h

end
end PaperC.Prel8.MicroscopicConditionalSpatial
