import PaperCPrel8.GoodStartDeletion
import PaperCPrel8.StrongerDeletionTheorem
import PaperCPrel8.MicroscopicDeletedTarget
import PaperCPrel8.MicroscopicDiscardTheorem

/-! # Literal ordinary outside-deletion costs for the stronger retained set -/
namespace PaperC.Prel8.OutsideDeletion
open Finset MeasureTheory ProbabilityTheory InfiniteRademacher
open StrongerDeletionTheorem RoughKernelDeletion MicroscopicSiteRestoration MicroscopicValueProfile
open MicroscopicActualGeometry MicroscopicProfileBudget MicroscopicPaperBudget MicroscopicGoodField
open MicroscopicDeletedSites MicroscopicBadPivotCount MicroscopicConditionalSpatial IndependentScalarTail
open GoodStartDeletion ConditionalStartProbability V282.FiniteStartMaskAverages
noncomputable section
local instance : MeasurableSpace F₂ := ⊤
local instance : IsProbabilityMeasure infiniteRademacherMeasure := by
  unfold infiniteRademacherMeasure
  infer_instance
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def outside (M L : ℕ) (I theta : ℝ) : Finset ℕ :=
  interiorStarts M L \ retainedStarts (strongerGood M L I theta)

def sourceCost (M L : ℕ) (I theta : ℝ)
    (A : SmallSample (sourceCylinder M L I) (primeCutoff M) → Prop) : ℝ :=
  (cond infiniteRademacherMeasure (traceEvent (sourceCylinder M L I) (primeCutoff M) A)).real
    (hitEvent L (outside M L I theta))

def targetCost (M L : ℕ) (I theta : ℝ) : ℝ := maskRate L (outside M L I theta)

theorem outside_union (M L : ℕ) (I theta : ℝ) :
    outside M L I theta = deletedStarts M (M-L) L (paperExcess M L I) (primeCutoff M) ∪
      (added M L I theta).image (fun j ↦ j+1) := by
  have hs : strongerGood M L I theta⊆originalGood M L I := strongGood_subset _ _ _ _
  have hg := retained_subset_interior M L I
  rw [← interior_difference]
  have he : (added M L I theta).image (fun j ↦ j+1)=
      retainedStarts (originalGood M L I) \ retainedStarts (strongerGood M L I theta) :=
    image_sdiff _ _ (fun _ _ h ↦ Nat.add_right_cancel h)
  rw [he]
  change _ = (interiorStarts M L \ retainedStarts (originalGood M L I)) ∪ _
  have hs' := image_subset_image (f:=fun j ↦ j+1) hs
  ext x
  simp only [outside,mem_sdiff,mem_union]
  change (x∈interiorStarts M L ∧ x∉retainedStarts (strongerGood M L I theta)) ↔ _
  constructor
  · intro h
    by_cases hx : x∈retainedStarts (originalGood M L I)
    · exact Or.inr ⟨hx,h.2⟩
    · exact Or.inl ⟨h.1,hx⟩
  · rintro (h|h)
    · exact ⟨h.1,fun hx ↦ h.2 (hs' hx)⟩
    · exact ⟨hg h.1,h.2⟩

theorem sourceCost_eq (M L : ℕ) (I theta : ℝ)
    (A : SmallSample (sourceCylinder M L I) (primeCutoff M) → Prop) :
    sourceCost M L I theta A =
      infiniteRademacherMeasure.real (traceEvent (sourceCylinder M L I) (primeCutoff M) A ∩
        hitEvent L (outside M L I theta)) /
      infiniteRademacherMeasure.real (traceEvent (sourceCylinder M L I) (primeCutoff M) A) := by
  unfold sourceCost Measure.real
  rw [cond_apply (measurableSet_traceEvent _ _ _),ENNReal.toReal_mul,ENNReal.toReal_inv]
  ring

theorem sourceCost_le (M L : ℕ) (I theta : ℝ)
    {betaMin betaMax : ℝ} (hgeo : GeometryFacts M L I betaMin betaMax)
    (A : SmallSample (sourceCylinder M L I) (primeCutoff M) → Prop)
    (hA : 0 < infiniteRademacherMeasure.real (traceEvent (sourceCylinder M L I) (primeCutoff M) A)) :
    sourceCost M L I theta A ≤
      infiniteRademacherMeasure.real (traceEvent (sourceCylinder M L I) (primeCutoff M) A ∩
        hitEvent L (deletedStarts M (M-L) L (paperExcess M L I) (primeCutoff M))) /
      infiniteRademacherMeasure.real (traceEvent (sourceCylinder M L I) (primeCutoff M) A) +
      2*((1/(2:ℝ)^L)*((added M L I theta).card:ℝ)) := by
  have hgood := actual_goodGeometry hgeo
  have ha := infinite_mask_mass_le hgood (show added M L I theta⊆originalGood M L I from sdiff_subset) A
  have hu : hitEvent L (outside M L I theta) =
      hitEvent L (deletedStarts M (M-L) L (paperExcess M L I) (primeCutoff M)) ∪
      hitEvent L ((added M L I theta).image (fun j ↦ j+1)) := by
    ext w
    simp only [outside_union,hitEvent_iff,mem_union,Set.mem_union]
    aesop
  rw [sourceCost_eq,hu,Set.inter_union_distrib_left]
  apply (div_le_div_of_nonneg_right (measureReal_union_le _ _) hA.le).trans
  rw [add_div]
  apply add_le_add_right
  apply (div_le_div_of_nonneg_right ha hA.le).trans_eq
  field_simp

theorem targetCost_le (M L : ℕ) (I theta : ℝ) :
    targetCost M L I theta ≤
      (maskRate L (deletedStarts M (M-L) L (paperExcess M L I) (primeCutoff M)):ℝ)+
      (1/(2:ℝ)^L)*((added M L I theta).card:ℝ) := by
  have hh := card_union_le
    (deletedStarts M (M-L) L (paperExcess M L I) (primeCutoff M))
    ((added M L I theta).image (fun j ↦ j+1))
  have hi := card_image_le (s:=added M L I theta) (f:=fun j ↦ j+1)
  change ((outside M L I theta).card:ℝ)/(2:ℝ)^L ≤ _
  rw [outside_union]
  have hc : (((deletedStarts M (M-L) L (paperExcess M L I) (primeCutoff M) ∪
      (added M L I theta).image (fun j ↦ j+1)).card):ℝ) ≤
      (deletedStarts M (M-L) L (paperExcess M L I) (primeCutoff M)).card+(added M L I theta).card := by
    exact_mod_cast (hh.trans (Nat.add_le_add_left hi _))
  apply (div_le_div_of_nonneg_right hc (by positivity)).trans_eq
  change _ = _/(2:ℝ)^L+_
  ring
end
end PaperC.Prel8.OutsideDeletion
