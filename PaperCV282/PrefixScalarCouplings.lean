import PaperCV282.FiniteStartMaskSource
import PaperCV282.PrefixLongestGeometry
import PaperCV282.MesoscopicPrefixMass

/-! # Exact source couplings for restoring a complete prefix -/
namespace PaperC.V282.PrefixScalarCouplings

open MeasureTheory Set InfiniteRademacher InfiniteCylinderTransfer InfiniteStartProbabilityTransfer
open InfiniteExactLengthProbabilityTransfer ConditionalAGGAverage
open Affine ArratiaGoldsteinGordonInput SectionThirteenFiniteBound SectionThirteenCouplings
open FiniteStartMaskModel FiniteStartMaskAverages FiniteStartMaskDeletion FiniteStartMaskSource
open InfiniteMaskedScalarTransfer TheoremSixteenTwo CorollaryPrefixLaw MicroscopicBorderEvents
open scoped BigOperators ENNReal

noncomputable section
local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

theorem infiniteStartProbability_eq_uniform {C x L : ℕ} (hcut : x+L≤C) :
    infiniteStartProbability x L =
      ((uniformEventProbability (fun omega : SampleSpace C => startAt omega x L) : ℚ) : ℝ) := by
  rw [infiniteStartProbability,infiniteStartEvent_eq_preimage hcut,
    ← Measure.map_apply (measurable_restrictToFinite C) (measurableSet_finiteStartEvent C x L),
    map_infiniteRademacherMeasure_restrictToFinite]
  rw [finiteStartEvent,finiteRademacherMeasure_event_eq_uniformEventProbability,ENNReal.toReal_ofReal]
  apply Rat.cast_nonneg.mpr
  unfold uniformEventProbability
  positivity

theorem source_subset_tv_le {L : ℕ} {small mask : Finset ℕ} (hsub : small⊆mask) :
    natTotalVariation (infiniteMaskedLaw L mask) (infiniteMaskedLaw L small) ≤
      ∑ x∈mask\small,infiniteStartProbability x L := by
  let C := mask.sup id+L
  have hcut (x : ℕ) (hx : x∈mask) : x+L≤C := Nat.add_le_add_right (Finset.le_sup (f := id) hx) L
  rw [infiniteMaskedLaw_eq_finiteLaw mask hcut,
    infiniteMaskedLaw_eq_finiteLaw small (fun x hx => hcut x (hsub hx))]
  have h := finiteLaw_subset_tv_le (C := C) (L := L) hsub
  convert h using 1
  apply Finset.sum_congr rfl
  intro x hx
  exact infiniteStartProbability_eq_uniform (hcut x (Finset.mem_sdiff.mp hx).1)

theorem source_global_law_eq (M L : ℕ) :
    infiniteMaskedLaw L (Finset.Ico 2 M)=globalStartLaw M L := by
  rw [infiniteMaskedLaw_eq_finiteLaw (Finset.Ico 2 M) (C := globalCylinderCutoff M L) (by
    intro x hx
    have hb := Finset.mem_Ico.mp hx
    unfold globalCylinderCutoff dyadicCutoff
    omega)]
  rfl

theorem prefix_boundary_probability_eq (M L : ℕ) :
    prefixBoundaryProbability M L = ((2 : ℝ)⁻¹)^Nat.primeCounting L := by
  rw [prefixBoundaryProbability_eq_measure]
  change (infiniteRademacherMeasure (PrefixBoundaryProbability.infinitePrefixBoundaryEvent L)).toReal = _
  rw [← borderEvent_eq_prefix]
  exact MicroscopicBorderEvents.equation_seven_one L

theorem prefix_overflow_mass_eq_source (M L : ℕ) :
    prefixOverflowStartMass M L = ∑ x∈prefixOverflowStartIndices M L,infiniteStartProbability x L := by
  unfold prefixOverflowStartMass
  apply Finset.sum_congr rfl
  intro x hx
  have hcut : x+L≤globalCylinderCutoff M L := by
    have h := Finset.mem_Ico.mp hx
    unfold globalCylinderCutoff dyadicCutoff
    omega
  rw [infiniteStartProbability_eq_uniform hcut]
  unfold commonCylinderStartProbability globalUniformPMF
  rw [eventProbability_fullUniformPMF_eq,finiteUniformProbability_eq_uniformEventProbability]

/-- Border and true overflow starts are the entire prefix/global coupling cost. -/
theorem source_prefix_global_tv_le {M L : ℕ} (hL : 2≤L) (hLM : L≤M) :
    natTotalVariation (infinitePrefixStartLaw M L) (infiniteMaskedLaw L (Finset.Ico 2 M)) ≤
      ((2 : ℝ)⁻¹)^Nat.primeCounting L +
        ∑ x∈prefixOverflowStartIndices M L,infiniteStartProbability x L := by
  rw [infinitePrefixStartCount_law_eq_prefixStartLaw,source_global_law_eq]
  simpa only [prefix_boundary_probability_eq,prefix_overflow_mass_eq_source] using
    natTotalVariation_prefix_global_le hL hLM

end
end PaperC.V282.PrefixScalarCouplings
