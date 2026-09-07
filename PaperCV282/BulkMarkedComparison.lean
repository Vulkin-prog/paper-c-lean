import PaperCV282.BulkMarkedSource
import PaperCV282.BulkMarkedTargetProjection
import PaperCV282.BulkMarkedTargetTail
import PaperCV282.BulkMarkedFieldBounds
import PaperCV282.FinitePrimeEnvironment

/-! # Averaged full-prime conditioning for the complete signed bulk configuration -/
namespace PaperC.V282.BulkMarkedComparison

open MeasureTheory ProbabilityTheory InfiniteRademacher InfiniteConditionalWords InfiniteCylinderTransfer
open ConditionalStartProbability BulkMarkedTypes BulkMarkedSource BulkMarkedTarget
open BulkMarkedTargetProjection BulkMarkedTargetTail BulkMarkedInfinite BulkMarkedTransfer
open BulkMarkedFieldBounds ConditionedCountableLaw CountablePrimeEventTransfer
open InfiniteMassCoupling FiniteFieldTotalVariation CountableLawTransfer FiniteFieldPoissonCoupling
open FinitePrimeEnvironment FiniteStartMaskAverages SectionThirteenFiniteBound
open ConditionalAGGAverage ConditionalAGGInstantiation ProcessAGGInput
open scoped BigOperators

noncomputable section
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instProbabilityInfiniteRademacher : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance

def spatialTargetLaw (sites : Finset ℕ) (L : ℕ) : SpatialMarkedConfig sites → ℝ :=
  observableLaw (spatialTargetMeasure sites L) id

theorem hasSum_spatialTargetLaw (sites : Finset ℕ) (L : ℕ) : HasSum (spatialTargetLaw sites L) 1 :=
  hasSum_observableLaw _ measurable_id

theorem spatialTargetLaw_nonneg (sites : Finset ℕ) (L : ℕ) (config : SpatialMarkedConfig sites) :
    0 ≤ spatialTargetLaw sites L config := observableLaw_nonneg _ _ _

/-- The expectation of actual conditional total variation; every excess and sign is retained. -/
def spatialConditionalDistance (C Y : ℕ) (sites : Finset ℕ) (L : ℕ) : ℝ :=
  meanAtomDistance C Y (spatialMarkedSource sites L) (spatialTargetLaw sites L)

def spatialSignedDistance (sites : Finset ℕ) (L : ℕ) : ℝ :=
  massTotalVariation (spatialSourceLaw sites L) (spatialTargetLaw sites L)

theorem spatialConditionalDistance_nonneg (C Y : ℕ) (sites : Finset ℕ) (L : ℕ) :
    0 ≤ spatialConditionalDistance C Y sites L := meanAtomDistance_nonneg _ _ _ _

theorem measurable_infiniteSignedField_full (sites : Finset ℕ) (L E : ℕ) :
    Measurable (infiniteSignedField sites L E sites) := by
  have h : (projectConfiguration sites E) ∘ (spatialMarkedSource sites L) =
      infiniteSignedField sites L E sites := funext (project_spatialMarkedSource sites L E)
  rw [← h]
  exact (measurable_of_countable _).comp (measurable_spatialMarkedSource sites L)

/-- The actual finite field's conditional masses agree with the full source atom ratios. -/
theorem finite_meanAtomDistance_eq (C Y : ℕ) (sites : Finset ℕ) (L E : ℕ) :
    meanAtomDistance C Y (infiniteSignedField sites L E sites)
      (poissonFieldMass (allSignedRates sites L E sites)) =
      exactSignedConditionalDistance C sites L E Y sites := by
  have h (sigma : SmallSample C Y) :
      conditionalObservableLaw infiniteRademacherMeasure (infiniteSmallPrimeAtom C Y sigma)
        (infiniteSignedField sites L E sites) = sourceConditionalSignedLaw C sites L E Y sites sigma := by
    funext k
    exact conditionalObservableLaw_eq_ratio _ _ (measurableSet_infiniteSmallPrimeAtom C Y sigma) _ k
  unfold meanAtomDistance exactSignedConditionalDistance
  simp_rw [h]
  rfl

theorem target_embedding_disagreement_le (sites : Finset ℕ) (L E : ℕ) :
    (spatialTargetMeasure sites L).real {config | config ≠
      embedConfiguration sites E (projectConfiguration sites E config)} ≤
      (maskRate L sites : ℝ)/(2 : ℝ)^(E+1) := by
  apply (measureReal_mono (μ := spatialTargetMeasure sites L) (s₂ := spatialTargetTail sites E) ?_).trans
    (spatial_target_tail_probability_le sites L E)
  intro config hconfig
  by_contra hn
  apply hconfig
  rw [embed_project_configuration]
  exact (spatial_truncation_eq_outside_tail sites E config hn).symm

/-- Both discarded tails are coupled on the actual probability spaces before averaging. -/
theorem conditional_signed_tv_le_finite_and_tails (C Y : ℕ) (sites : Finset ℕ) (L E : ℕ) :
    spatialConditionalDistance C Y sites L ≤
      infiniteRademacherMeasure.real (spatialSourceTail sites L E) +
      exactSignedConditionalDistance C sites L E Y sites +
      (maskRate L sites : ℝ)/(2 : ℝ)^(E+1) := by
  have htarget : observableLaw (spatialTargetMeasure sites L) (projectConfiguration sites E) =
      poissonFieldMass (allSignedRates sites L E sites) := funext (spatial_project_mass_eq sites L E)
  have hpoint (sigma : SmallSample C Y) :
      massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure
        (infiniteSmallPrimeAtom C Y sigma) (spatialMarkedSource sites L)) (spatialTargetLaw sites L) ≤
      (cond infiniteRademacherMeasure (infiniteSmallPrimeAtom C Y sigma)).real (spatialSourceTail sites L E) +
      massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure
        (infiniteSmallPrimeAtom C Y sigma) (infiniteSignedField sites L E sites))
        (poissonFieldMass (allSignedRates sites L E sites)) +
      (maskRate L sites : ℝ)/(2 : ℝ)^(E+1) := by
    letI instProbabilityConditionalAtom : IsProbabilityMeasure (cond infiniteRademacherMeasure (infiniteSmallPrimeAtom C Y sigma)) :=
      cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _
        (ExactMarkedInfinite.signed_conditioning_atom_real_pos C Y sigma))
    have hs : (cond infiniteRademacherMeasure (infiniteSmallPrimeAtom C Y sigma)).real
        {omega | spatialMarkedSource sites L omega ≠
          embedConfiguration sites E (infiniteSignedField sites L E sites omega)} ≤
        (cond infiniteRademacherMeasure (infiniteSmallPrimeAtom C Y sigma)).real (spatialSourceTail sites L E) := by
      apply measureReal_mono ?_ (measure_ne_top _ _)
      intro omega homega
      by_contra hn
      apply homega
      rw [← project_spatialMarkedSource,embed_project_configuration]
      exact spatialMarkedSource_eq_truncate_off_tail sites L E omega hn
    have h := truncation_tv_le_of_bounds
      (cond infiniteRademacherMeasure (infiniteSmallPrimeAtom C Y sigma)) (spatialTargetMeasure sites L)
      (measurable_spatialMarkedSource sites L) measurable_id (measurable_infiniteSignedField_full sites L E)
      (measurable_of_countable (projectConfiguration sites E)) (embedConfiguration sites E)
      hs (le_refl _) (target_embedding_disagreement_le sites L E)
    rw [htarget] at h
    exact h
  have hav := finiteUniformAverage_mono hpoint
  have hadd {ι : Type} [Fintype ι] [Nonempty ι] (f g : ι → ℝ) (c : ℝ) :
      finiteUniformAverage (fun i => f i+g i+c) = finiteUniformAverage f+finiteUniformAverage g+c := by
    unfold finiteUniformAverage
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp
  rw [hadd] at hav
  have ht := average_conditional_event C Y (spatialSourceTail sites L E)
    (measurableSet_spatialSourceTail sites L E)
  change finiteUniformAverage _ = _ at ht
  rw [ht] at hav
  change spatialConditionalDistance C Y sites L ≤ _ at hav
  change spatialConditionalDistance C Y sites L ≤ infiniteRademacherMeasure.real (spatialSourceTail sites L E) +
    meanAtomDistance C Y (infiniteSignedField sites L E sites)
      (poissonFieldMass (allSignedRates sites L E sites)) + _ at hav
  rwa [finite_meanAtomDistance_eq] at hav

/-- The represented prime-algebra integral uses the actual source conditional laws.
It is the full F_Y integral when Y ≤ C. -/
theorem spatialConditionalDistance_eq_integral (C Y : ℕ) (sites : Finset ℕ) (L : ℕ) :
    spatialConditionalDistance C Y sites L = ∫ omega,
      environmentDistance C Y (spatialMarkedSource sites L) (spatialTargetLaw sites L) omega
      ∂infiniteRademacherMeasure := (integral_environmentDistance _ _ _ _).symm

/-- A finite ledger and genuine two tails bound the complete signed configuration. -/
theorem complete_signed_field_le_ledger (hAGG : ProcessAGGStatement)
    {C L E Y : ℕ} (sites : Finset ℕ) (hsite : ∀x∈sites,2≤x) (hL : 1≤L)
    (hC : ∀x∈sites,x+L+E+1≤C) (hY : 2*(L+E+2)≤Y) :
    spatialConditionalDistance C Y sites L ≤ exactMarkedLedger C sites L E Y sites +
      ((MaskedArithmeticGeometry.fullDefectMass (L+E+1) sites : ℝ)+2*sites.card)/(2 : ℝ)^(L+E+1) := by
  have h := conditional_signed_tv_le_finite_and_tails C Y sites L E
  have hf := (signed_source_field_le_ledger hAGG hsite hL hC hY sites (Finset.Subset.refl _)).1
  have hs := spatial_source_tail_le_full_defects L E hsite
  have ht : (maskRate L sites : ℝ)/(2 : ℝ)^(E+1) = sites.card/(2 : ℝ)^(L+E+1) := by
    change ((sites.card : ℝ)/(2 : ℝ)^L)/(2 : ℝ)^(E+1) = _
    rw [show L+E+1=L+(E+1) by omega,pow_add]
    ring
  rw [ht] at h
  exact (h.trans (add_le_add (add_le_add hs hf) (le_refl _))).trans_eq (by ring)

end
end PaperC.V282.BulkMarkedComparison
