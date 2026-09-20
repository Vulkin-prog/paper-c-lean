import PaperCV282.MaskedScalarRetained
import PaperCV282.AllStartConditionalDependency

/-!
# True conditional scalar laws and whole-support deletion

The complete count is the literal sum of start events on the given mask,
with the small-prime assignment fixed. The retained count uses the exact
whole-support good mask. Their coupling cost keeps every removed vertex,
including a defect at the root x-1, and averages to the actual bad mass.
-/

namespace PaperC.V282.MaskedScalarCoupling

open ArratiaGoldsteinGordonInput ConditionalStartProbability ConditionalAGGInstantiation
open ConditionalAGGAverage SectionThirteenFiniteBound SectionThirteenCouplings
open SectionTwelveMoments LargePrimeDependencyGraph MaskedPoissonCritical
open MaskedArithmeticGeometry MaskedArithmeticAverages MaskedBadMass
open MaskedScalarRetained ScalarSteinInput AllStartConditionalDependency
open scoped BigOperators NNReal

noncomputable section

local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- The actual complete masked count on a fixed small-prime fibre. -/
def conditionalMaskedCount (N L Y : ℕ) (mask : Finset ℕ)
    (sigma : SmallSample (dyadicCutoff N L) Y)
    (eta : LargeSample (dyadicCutoff N L) Y) : ℕ :=
  fullMaskedDyadicCount N L mask (assemble (dyadicCutoff N L) Y sigma eta)

/-- Pushforward law of the actual complete count, without deleting any sites. -/
def conditionalMaskedLaw (N L Y : ℕ) (mask : Finset ℕ)
    (sigma : SmallSample (dyadicCutoff N L) Y) : ℕ → ℝ :=
  finiteNatLaw (largeUniformPMF (dyadicCutoff N L) Y)
    (conditionalMaskedCount N L Y mask sigma)

/-- The retained historical count is exactly the literal whole-support good-site sum. -/
theorem retained_conditional_count_eq_sum {N L Y : ℕ} (mask : Finset ℕ)
    (hmask : mask ⊆ dyadicBlock N)
    (sigma : SmallSample (dyadicCutoff N L) Y)
    (eta : LargeSample (dyadicCutoff N L) Y) :
    indicatorSum (maskedConditionedGoodIndicator N L Y (fullGoodMask N L Y mask) sigma) eta =
      ∑ x ∈ fullGoodMask N L Y mask,
        if startAt (assemble (dyadicCutoff N L) Y sigma eta) x L then 1 else 0 := by
  classical
  rw [conditionedMaskedIndicatorSum_eq_fullMaskedGoodStartCount,
    fullMaskedGoodStartCount_eq_sum,historical_maskedGood_eq_full hmask]

/-- Disagreement with the retained count requires an actual start at a removed site. -/
theorem exists_fullBad_start_of_conditional_counts_ne {N L Y : ℕ} (mask : Finset ℕ)
    (hmask : mask ⊆ dyadicBlock N)
    (sigma : SmallSample (dyadicCutoff N L) Y)
    (eta : LargeSample (dyadicCutoff N L) Y)
    (hne : conditionalMaskedCount N L Y mask sigma eta ≠
      indicatorSum (maskedConditionedGoodIndicator N L Y (fullGoodMask N L Y mask) sigma) eta) :
    ∃ x ∈ fullBadMask N L Y mask,
      startAt (assemble (dyadicCutoff N L) Y sigma eta) x L := by
  classical
  by_contra h
  push Not at h
  apply hne
  rw [retained_conditional_count_eq_sum mask hmask sigma eta]
  unfold conditionalMaskedCount fullMaskedDyadicCount
  symm
  apply Finset.sum_subset (fullGoodMask_subset_mask N L Y mask)
  intro x hxmask hxnotgood
  have hxbad : x ∈ fullBadMask N L Y mask := by
    apply mem_fullBadMask.mpr
    refine ⟨hxmask,?_⟩
    by_contra hxnotbad
    exact hxnotgood (mem_fullGoodMask.mpr ⟨hxmask,hxnotbad⟩)
  exact if_neg (h x hxbad)

/-- The actual conditional coupling costs only the sum of the removed-site probabilities. -/
theorem conditional_full_retained_tv_le {N L Y : ℕ} (mask : Finset ℕ)
    (hmask : mask ⊆ dyadicBlock N)
    (sigma : SmallSample (dyadicCutoff N L) Y) :
    natTotalVariation (conditionalMaskedLaw N L Y mask sigma)
      (maskedConditionalGoodLaw N L Y (fullGoodMask N L Y mask) sigma) ≤
        ∑ x ∈ fullBadMask N L Y mask,
          eventProbability (largeUniformPMF (dyadicCutoff N L) Y)
            (fun eta => startAt (assemble (dyadicCutoff N L) Y sigma eta) x L) := by
  classical
  rw [maskedConditionalGoodLaw_eq_finiteNatLaw]
  apply (natTotalVariation_finiteNatLaw_le_disagreement
    (largeUniformPMF (dyadicCutoff N L) Y)
    (conditionalMaskedCount N L Y mask sigma)
    (indicatorSum (maskedConditionedGoodIndicator N L Y (fullGoodMask N L Y mask) sigma))).trans
  unfold disagreementProbability eventProbability
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro eta heta
  by_cases hne : conditionalMaskedCount N L Y mask sigma eta ≠
      indicatorSum (maskedConditionedGoodIndicator N L Y (fullGoodMask N L Y mask) sigma) eta
  · rw [if_pos hne]
    obtain ⟨x,hxbad,hxstart⟩ := exists_fullBad_start_of_conditional_counts_ne mask hmask sigma eta hne
    calc
      _ = if startAt (assemble (dyadicCutoff N L) Y sigma eta) x L then
          (largeUniformPMF (dyadicCutoff N L) Y).prob eta else 0 := (if_pos hxstart).symm
      _ ≤ _ := by
        apply Finset.single_le_sum (s := fullBadMask N L Y mask)
          (f := fun y => if startAt (assemble (dyadicCutoff N L) Y sigma eta) y L then
            (largeUniformPMF (dyadicCutoff N L) Y).prob eta else 0)
        · intro y hy
          split_ifs
          · exact (largeUniformPMF (dyadicCutoff N L) Y).nonneg eta
          · exact le_rfl
        · exact hxbad
  · rw [if_neg hne]
    exact Finset.sum_nonneg fun x hx => by
      split_ifs
      · exact (largeUniformPMF (dyadicCutoff N L) Y).nonneg eta
      · exact le_rfl

/-- Averaging the removed probabilities is the exact finite law of total probability. -/
theorem average_conditional_bad_probability_sum_eq (N L Y : ℕ) (mask : Finset ℕ) :
    finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
      ∑ x ∈ fullBadMask N L Y mask,
        eventProbability (largeUniformPMF (dyadicCutoff N L) Y)
          (fun eta => startAt (assemble (dyadicCutoff N L) Y sigma eta) x L)) =
      (maskedBadStartMass N L Y mask : ℝ) := by
  classical
  rw [finiteUniformAverage_finsetSum]
  unfold maskedBadStartMass
  push_cast
  apply Finset.sum_congr rfl
  intro x hx
  have h := finiteUniformAverage_largeEventProbability_eq_full (dyadicCutoff N L) Y
    (fun omega => startAt omega x L)
  simpa only [startProbability] using h

/-- The mean conditional deletion cost is bounded by the true masked bad mass. -/
theorem average_conditional_full_retained_tv_le {N L Y : ℕ} (mask : Finset ℕ)
    (hmask : mask ⊆ dyadicBlock N) :
    finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
      natTotalVariation (conditionalMaskedLaw N L Y mask sigma)
        (maskedConditionalGoodLaw N L Y (fullGoodMask N L Y mask) sigma)) ≤
      (maskedBadStartMass N L Y mask : ℝ) := by
  have h := finiteUniformAverage_mono (fun sigma : SmallSample (dyadicCutoff N L) Y => conditional_full_retained_tv_le mask hmask sigma)
  rwa [average_conditional_bad_probability_sum_eq] at h

/-- The new measure-derived Poisson mass agrees exactly with the historical formula. -/
theorem poissonMass_eq_poissonPMFReal (rate : ℝ≥0) :
    poissonMass rate = ProbabilityTheory.poissonPMFReal rate := by
  funext k
  rw [poissonMass_formula]
  rfl

/-- Deleting sites changes the target intensity by exactly their own masked cardinality. -/
theorem abs_retainedRate_sub_target_eq (N L Y : ℕ) (mask : Finset ℕ) :
    |(retainedRate N L Y mask : ℝ) - (maskedTargetPoissonRate L mask : ℝ)| =
      (fullBadMask N L Y mask).card / (2 : ℝ) ^ L := by
  have hcard : ((fullGoodMask N L Y mask).card : ℝ) + (fullBadMask N L Y mask).card = mask.card := by
    exact_mod_cast card_fullGood_add_card_fullBad N L Y mask
  change |((fullGoodMask N L Y mask).card : ℝ) / 2 ^ L - mask.card / 2 ^ L| = _
  have heq : ((fullGoodMask N L Y mask).card : ℝ) / 2 ^ L - mask.card / 2 ^ L =
      -((fullBadMask N L Y mask).card / (2 : ℝ) ^ L) := by
    rw [← hcard]
    ring
  rw [heq,abs_neg,abs_of_nonneg (by positivity)]

/-- Actual Poisson measures admit the precise masked intensity-shift coupling. -/
theorem retained_target_poisson_tv_le (N L Y : ℕ) (mask : Finset ℕ) :
    natTotalVariation (poissonMass (retainedRate N L Y mask))
      (poissonMass (maskedTargetPoissonRate L mask)) ≤
        (fullBadMask N L Y mask).card / (2 : ℝ) ^ L := by
  rw [poissonMass_eq_poissonPMFReal,poissonMass_eq_poissonPMFReal]
  exact (natTotalVariation_poisson_le_abs_rate_sub _ _).trans_eq
    (abs_retainedRate_sub_target_eq N L Y mask)


/-- Mixing the actual conditional laws recovers the complete unconditional masked law. -/
theorem average_conditionalMaskedLaw_eq_full (N L Y : ℕ) (mask : Finset ℕ) :
    (fun k => finiteUniformAverage (fun sigma : SmallSample (dyadicCutoff N L) Y =>
      conditionalMaskedLaw N L Y mask sigma k)) = fullMaskedDyadicStartLaw N L mask := by
  classical
  funext k
  let P : SampleSpace (dyadicCutoff N L) → Prop := fun omega => fullMaskedDyadicCount N L mask omega = k
  have htotal := finiteUniformAverage_largeEventProbability_eq_full (dyadicCutoff N L) Y P
  have hfull : eventProbability (fullUniformPMF (dyadicCutoff N L)) P =
      ((uniformEventProbability P : ℚ) : ℝ) := by
    rw [eventProbability_fullUniformPMF_eq,finiteUniformProbability_eq_uniformEventProbability]
  rw [← hfull] at htotal
  have hlarge (sigma : SmallSample (dyadicCutoff N L) Y) :
      conditionalMaskedLaw N L Y mask sigma k =
        eventProbability (largeUniformPMF (dyadicCutoff N L) Y)
          (fun eta => P (assemble (dyadicCutoff N L) Y sigma eta)) := by
    unfold conditionalMaskedLaw finiteNatLaw eventProbability
    apply Finset.sum_congr rfl
    intro eta heta
    by_cases hk : conditionalMaskedCount N L Y mask sigma eta = k
    · have hP : P (assemble (dyadicCutoff N L) Y sigma eta) := hk
      rw [if_pos hk, if_pos hP]
    · have hP : ¬ P (assemble (dyadicCutoff N L) Y sigma eta) := hk
      rw [if_neg hk, if_neg hP]
  have hfullLaw : fullMaskedDyadicStartLaw N L mask k =
      eventProbability (fullUniformPMF (dyadicCutoff N L)) P := by
    unfold fullMaskedDyadicStartLaw finiteNatLaw eventProbability
    apply Finset.sum_congr rfl
    intro omega homega
    by_cases hk : fullMaskedDyadicCount N L mask omega = k <;> simp [P,hk]
  simp_rw [hlarge,hfullLaw]
  exact htotal

end
end PaperC.V282.MaskedScalarCoupling
