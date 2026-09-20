import PaperCPrel8.MicroscopicSpatialRates
import PaperCV282.MacroTransportRestoration

/-! # Restoring every interior site with the actual conditional deletion event -/
namespace PaperC.Prel8.MicroscopicSiteRestoration
open MeasureTheory ProbabilityTheory PaperC.InfiniteRademacher
open PaperC.Prel8.IndependentScalarTail PaperC.Prel8.MicroscopicValueProfile
open PaperC.Prel8.MicroscopicRetainedTheorem PaperC.Prel8.MicroscopicActualGeometry
open PaperC.Prel8.MicroscopicProfileBudget PaperC.Prel8.MicroscopicGoodField
open PaperC.Prel8.MicroscopicDeletedSites PaperC.Prel8.MicroscopicBadPivotCount
open PaperC.V282.BulkMarkedSource PaperC.V282.BulkMarkedTarget PaperC.V282.BulkMarkedComparison
open PaperC.V282.MacroTransportRestriction PaperC.V282.MacroTransportRestoration
open PaperC.V282.ConditionedCountableLaw PaperC.V282.CountableLawTransfer
open PaperC.V282.InfiniteMassCoupling PaperC.V282.FiniteFieldTotalVariation
open PaperC.V282.FiniteStartMaskAverages
noncomputable section
local instance : MeasurableSpace PaperC.F₂ := ⊤
local instance : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- All paper interior starts, including those excluded from the prime coupling. -/
def interiorStarts (M L : ℕ) : Finset ℕ := retainedStarts (Finset.Icc 1 (M-L))

theorem retained_subset_interior (M L : ℕ) (I : ℝ) :
    retainedStarts (actualSites M L I) ⊆ interiorStarts M L :=
  Finset.image_subset_image (goodSites_subset _ _ _ _ _)

theorem interior_difference (M L : ℕ) (I : ℝ) :
    interiorStarts M L \ retainedStarts (actualSites M L I) =
      deletedStarts M (M-L) L (paperExcess M L I) (primeCutoff M) := by
  unfold interiorStarts retainedStarts deletedStarts deletedSites actualSites
  exact (Finset.image_sdiff _ _ (fun _ _ h => Nat.add_right_cancel h)).symm

/-- Site restoration costs the actual joint event, not a fictitious independent source. -/
theorem conditional_restoration_by_hit {s t : Finset ℕ} (hst : s ⊆ t) (L : ℕ)
    (A : Set InfiniteSample) (hA : MeasurableSet A) (hpos : 0 < infiniteRademacherMeasure.real A) :
    massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure A (spatialMarkedSource t L))
      (spatialTargetLaw t L) ≤
      infiniteRademacherMeasure.real (A ∩ hitEvent L (t\s))/infiniteRademacherMeasure.real A +
      massTotalVariation (conditionalObservableLaw infiniteRademacherMeasure A (spatialMarkedSource s L))
        (spatialTargetLaw s L) + (maskRate L (t\s):ℝ) := by
  let : IsProbabilityMeasure (cond infiniteRademacherMeasure A) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ hpos)
  have hs : (cond infiniteRademacherMeasure A).real {ω | spatialMarkedSource t L ω ≠
      embedSites hst (spatialMarkedSource s L ω)} ≤
      infiniteRademacherMeasure.real (A ∩ hitEvent L (t\s))/infiniteRademacherMeasure.real A := by
    have hd : {ω | spatialMarkedSource t L ω ≠ embedSites hst (spatialMarkedSource s L ω)} ⊆
        hitEvent L (t\s) := by
      intro ω hω
      by_contra hn
      apply hω
      symm
      apply source_eq_embedded_off_removed_starts hst L ω
      intro x hx he
      exact hn ((hitEvent_iff L (t\s) ω).mpr ⟨x,hx,he⟩)
    apply (measureReal_mono hd (measure_ne_top _ _)).trans_eq
    unfold Measure.real
    rw [cond_apply hA,ENNReal.toReal_mul,ENNReal.toReal_inv]
    ring
  have he : observableLaw (spatialTargetMeasure t L) (restrictSites hst) =
      observableLaw (spatialTargetMeasure s L) id :=
    observableLaw_of_hasLaw _ _ (hasLaw_restrictSites hst L)
  have h := truncation_tv_le_of_bounds (cond infiniteRademacherMeasure A) (spatialTargetMeasure t L)
    (measurable_spatialMarkedSource t L) measurable_id (measurable_spatialMarkedSource s L)
    (measurable_of_countable (restrictSites hst)) (embedSites hst) hs (le_refl _)
    (target_restoration_probability_le hst L)
  rw [he] at h
  exact h

end
end PaperC.Prel8.MicroscopicSiteRestoration
