import PaperC.Probability.InfiniteStartProbabilityTransfer
import PaperC.Probability.SectionTwelveMoments

/-!
# Base-start laws in every adequate prime cylinder

An enlarged cylinder is related to the canonical cylinder through the same
actual infinite product source. Averaging conditioned base events therefore
returns the existing start probabilities at the base length, not the mark length.
-/
set_option maxHeartbeats 800000

namespace PaperC.V282.FullCylinderStartLaw

open MeasureTheory InfiniteRademacher InfiniteCylinderTransfer InfiniteExactLengthProbabilityTransfer
open InfiniteStartProbabilityTransfer SectionTwelveMoments ConditionalStartProbability
open ConditionalAGGInstantiation ConditionalAGGAverage ArratiaGoldsteinGordonInput SectionThirteenCouplings
open SectionThirteenFiniteBound

local instance instMeasurableSpaceF2Discrete : MeasurableSpace F₂ := ⊤

noncomputable section

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- Two finite observations of the same infinite event have identical probabilities. -/
theorem cylinder_event_probability_invariant (C D : ℕ)
    (P : SampleSpace C → Prop) (Q : SampleSpace D → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ omega : InfiniteSample, P (restrictToFinite C omega) ↔ Q (restrictToFinite D omega)) :
    ((uniformEventProbability P : ℚ) : ℝ) = ((uniformEventProbability Q : ℚ) : ℝ) := by
  have hm : finiteRademacherMeasure C {omega | P omega} = finiteRademacherMeasure D {omega | Q omega} := by
    rw [← map_infiniteRademacherMeasure_restrictToFinite C,
      ← map_infiniteRademacherMeasure_restrictToFinite D,
      Measure.map_apply (measurable_restrictToFinite C) (Set.toFinite _ |>.measurableSet),
      Measure.map_apply (measurable_restrictToFinite D) (Set.toFinite _ |>.measurableSet)]
    congr 1
    ext omega
    exact h omega
  rw [finiteRademacherMeasure_event_eq_uniformEventProbability,
    finiteRademacherMeasure_event_eq_uniformEventProbability] at hm
  have hp : (0 : ℝ) ≤ (uniformEventProbability P : ℚ) := by
    exact_mod_cast (show (0 : ℚ) ≤ uniformEventProbability P by unfold uniformEventProbability;positivity)
  have hq : (0 : ℝ) ≤ (uniformEventProbability Q : ℚ) := by
    exact_mod_cast (show (0 : ℚ) ≤ uniformEventProbability Q by unfold uniformEventProbability;positivity)
  have hh := congrArg ENNReal.toReal hm
  simpa only [ENNReal.toReal_ofReal hp,ENNReal.toReal_ofReal hq] using hh

/-- Exact base marginal in an arbitrary adequate cylinder. -/
theorem fullCylinder_start_probability_eq {C N L x : ℕ}
    (hx : x ∈ dyadicBlock N) (hcut : x+L ≤ C) :
    ((uniformEventProbability (M := C) (fun omega => startAt omega x L) : ℚ) : ℝ) =
      (startProbability N L x : ℝ) := by
  have hcanonical : x+L ≤ dyadicCutoff N L := by
    have hh := Finset.mem_Ico.mp hx
    unfold dyadicCutoff
    omega
  unfold startProbability
  apply cylinder_event_probability_invariant
  intro omega
  rw [startAt_restrictToFinite_iff omega hcut,startAt_restrictToFinite_iff omega hcanonical]

/-- Exact joint base law, with no ratio or mark-length restriction. -/
theorem fullCylinder_joint_probability_eq {C N L x y : ℕ}
    (hx : x ∈ dyadicBlock N) (hy : y ∈ dyadicBlock N) (hcutx : x+L ≤ C) (hcuty : y+L ≤ C) :
    ((uniformEventProbability (M := C) (fun omega => startAt omega x L ∧ startAt omega y L) : ℚ) : ℝ) =
      (jointStartProbability N L x y : ℝ) := by
  have hcanonicalx : x+L ≤ dyadicCutoff N L := by
    have hh := Finset.mem_Ico.mp hx
    unfold dyadicCutoff
    omega
  have hcanonicaly : y+L ≤ dyadicCutoff N L := by
    have hh := Finset.mem_Ico.mp hy
    unfold dyadicCutoff
    omega
  exact cylinder_event_probability_invariant C (dyadicCutoff N L)
    (fun omega : SampleSpace C => startAt omega x L ∧ startAt omega y L)
    (fun omega : SampleSpace (dyadicCutoff N L) => startAt omega x L ∧ startAt omega y L)
    (fun omega => (and_congr (startAt_restrictToFinite_iff omega hcutx)
      (startAt_restrictToFinite_iff omega hcuty)).trans
        ((and_congr (startAt_restrictToFinite_iff omega hcanonicalx)
          (startAt_restrictToFinite_iff omega hcanonicaly)).symm))

/-- PMF form of the single-start cylinder invariance. -/
theorem eventProbability_fullCylinder_start {C N L x : ℕ}
    (hx : x ∈ dyadicBlock N) (hcut : x+L ≤ C) :
    eventProbability (fullUniformPMF C) (fun omega => startAt omega x L) = (startProbability N L x : ℝ) := by
  rw [eventProbability_fullUniformPMF_eq,finiteUniformProbability_eq_uniformEventProbability]
  exact fullCylinder_start_probability_eq hx hcut

/-- PMF form of the joint-start cylinder invariance. -/
theorem eventProbability_fullCylinder_joint {C N L x y : ℕ}
    (hx : x ∈ dyadicBlock N) (hy : y ∈ dyadicBlock N) (hcutx : x+L ≤ C) (hcuty : y+L ≤ C) :
    eventProbability (fullUniformPMF C) (fun omega => startAt omega x L ∧ startAt omega y L) =
      (jointStartProbability N L x y : ℝ) := by
  rw [eventProbability_fullUniformPMF_eq,finiteUniformProbability_eq_uniformEventProbability]
  exact fullCylinder_joint_probability_eq hx hy hcutx hcuty

/-- Average after conditioning on any cutoff returns the base start probability. -/
theorem average_conditioned_base_start_probability {C N L x : ℕ} (Y : ℕ)
    (hx : x ∈ dyadicBlock N) (hcut : x+L ≤ C) :
    finiteUniformAverage (fun sigma : SmallSample C Y =>
      eventProbability (largeUniformPMF C Y) (fun eta => startAt (assemble C Y sigma eta) x L)) =
      (startProbability N L x : ℝ) := by
  exact (finiteUniformAverage_largeEventProbability_eq_full C Y
    (fun omega : SampleSpace C => startAt omega x L)).trans
      (fullCylinder_start_probability_eq hx hcut)

/-- Average the true joint before applying the base-length relation profile. -/
theorem average_conditioned_base_joint_probability {C N L x y : ℕ} (Y : ℕ)
    (hx : x ∈ dyadicBlock N) (hy : y ∈ dyadicBlock N) (hcutx : x+L ≤ C) (hcuty : y+L ≤ C) :
    finiteUniformAverage (fun sigma : SmallSample C Y =>
      eventProbability (largeUniformPMF C Y) (fun eta =>
        startAt (assemble C Y sigma eta) x L ∧ startAt (assemble C Y sigma eta) y L)) =
      (jointStartProbability N L x y : ℝ) := by
  exact (finiteUniformAverage_largeEventProbability_eq_full C Y
    (fun omega : SampleSpace C => startAt omega x L ∧ startAt omega y L)).trans
      (fullCylinder_joint_probability_eq hx hy hcutx hcuty)

end
end PaperC.V282.FullCylinderStartLaw
